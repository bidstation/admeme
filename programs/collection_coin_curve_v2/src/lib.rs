use anchor_lang::prelude::*;
use anchor_lang::solana_program::program_option::COption;
use anchor_lang::system_program;
use anchor_spl::associated_token::AssociatedToken;
use anchor_spl::token::{self, Mint, MintTo, SetAuthority, Token, TokenAccount, Transfer};
use anchor_spl::token::spl_token::instruction::AuthorityType;

// Replace with your deployed program id before building/deploying.
declare_id!("FUAYEMXuFbmEyCu215fqH4G5Q2jSjQUBJvPPJJSQDMZj");

const BPS_DENOMINATOR: u64 = 10_000;
const PLATFORM_FEE_BPS: u16 = 100; // 1%
const GLOBAL_VERSION: u8 = 1;
const MARKET_VERSION: u8 = 1;
const MARKET_STATUS_ACTIVE: u8 = 0;
const MARKET_STATUS_FROZEN_FOR_MIGRATION: u8 = 1;
const MARKET_STATUS_MIGRATED: u8 = 2;

#[program]
pub mod collection_coin_curve_v2 {
    use super::*;

    pub fn initialize_global(
        ctx: Context<InitializeGlobal>,
        platform_treasury: Pubkey,
        graduation_enabled: bool,
        graduation_sol_threshold: u64,
    ) -> Result<()> {
        require!(platform_treasury != Pubkey::default(), CurveError::InvalidTreasury);

        let global = &mut ctx.accounts.global;
        global.version = GLOBAL_VERSION;
        global.bump = ctx.bumps.global;
        global.authority = ctx.accounts.authority.key();
        global.platform_treasury = platform_treasury;
        global.fee_bps = PLATFORM_FEE_BPS;
        global.graduation_enabled = graduation_enabled;
        global.graduation_sol_threshold = graduation_sol_threshold;
        global.reserved = [0u8; 64];

        emit!(GlobalConfigured {
            authority: global.authority,
            platform_treasury,
            fee_bps: global.fee_bps,
            graduation_enabled,
            graduation_sol_threshold,
        });
        Ok(())
    }

    pub fn update_global(
        ctx: Context<UpdateGlobal>,
        new_platform_treasury: Option<Pubkey>,
        graduation_enabled: Option<bool>,
        graduation_sol_threshold: Option<u64>,
    ) -> Result<()> {
        let global = &mut ctx.accounts.global;

        if let Some(treasury) = new_platform_treasury {
            require!(treasury != Pubkey::default(), CurveError::InvalidTreasury);
            global.platform_treasury = treasury;
        }
        if let Some(enabled) = graduation_enabled {
            global.graduation_enabled = enabled;
        }
        if let Some(threshold) = graduation_sol_threshold {
            global.graduation_sol_threshold = threshold;
        }

        emit!(GlobalConfigured {
            authority: global.authority,
            platform_treasury: global.platform_treasury,
            fee_bps: global.fee_bps,
            graduation_enabled: global.graduation_enabled,
            graduation_sol_threshold: global.graduation_sol_threshold,
        });
        Ok(())
    }

    pub fn create_collection_coin(
        ctx: Context<CreateCollectionCoin>,
        args: CreateCollectionCoinArgs,
    ) -> Result<()> {
        require!(args.total_supply > 0, CurveError::InvalidParam);
        require!(args.decimals <= 9, CurveError::InvalidParam);
        require!(args.initial_virtual_token_reserves > args.total_supply, CurveError::InvalidParam);
        require!(args.initial_virtual_sol_reserves > 0, CurveError::InvalidParam);
        require!(args.collection_id != [0u8; 32], CurveError::InvalidParam);

        let creator_key = ctx.accounts.creator.key();
        require!(ctx.accounts.mint.supply == 0, CurveError::InvalidMintState);
        require!(ctx.accounts.mint.decimals == args.decimals, CurveError::InvalidMintState);
        require!(
            ctx.accounts.mint.mint_authority == COption::Some(creator_key),
            CurveError::InvalidMintAuthority
        );
        require!(
            ctx.accounts.mint.freeze_authority == COption::Some(creator_key),
            CurveError::InvalidMintAuthority
        );

        let market = &mut ctx.accounts.market;
        market.version = MARKET_VERSION;
        market.bump = ctx.bumps.market;
        market.status = MARKET_STATUS_ACTIVE;
        market.collection_id = args.collection_id;
        market.creator = creator_key;
        market.mint = ctx.accounts.mint.key();
        market.token_vault = ctx.accounts.token_vault.key();
        market.decimals = args.decimals;
        market.total_supply = args.total_supply;
        market.virtual_token_reserves = args.initial_virtual_token_reserves as u128;
        market.virtual_sol_reserves = args.initial_virtual_sol_reserves as u128;
        market.real_token_reserves = args.total_supply;
        market.real_sol_reserves = 0;
        market.total_platform_fees_collected = 0;
        market.migration_target = Pubkey::default();
        market.migration_started_at = 0;
        market.migration_completed_at = 0;
        market.created_at = Clock::get()?.unix_timestamp;
        market.reserved = [0u8; 64];

        token::mint_to(
            CpiContext::new(
                ctx.accounts.token_program.to_account_info(),
                MintTo {
                    mint: ctx.accounts.mint.to_account_info(),
                    to: ctx.accounts.token_vault.to_account_info(),
                    authority: ctx.accounts.creator.to_account_info(),
                },
            ),
            args.total_supply,
        )?;

        token::set_authority(
            CpiContext::new(
                ctx.accounts.token_program.to_account_info(),
                SetAuthority {
                    account_or_mint: ctx.accounts.mint.to_account_info(),
                    current_authority: ctx.accounts.creator.to_account_info(),
                },
            ),
            AuthorityType::MintTokens,
            None,
        )?;

        token::set_authority(
            CpiContext::new(
                ctx.accounts.token_program.to_account_info(),
                SetAuthority {
                    account_or_mint: ctx.accounts.mint.to_account_info(),
                    current_authority: ctx.accounts.creator.to_account_info(),
                },
            ),
            AuthorityType::FreezeAccount,
            None,
        )?;

        emit!(MarketCreated {
            market: market.key(),
            creator: market.creator,
            collection_id: market.collection_id,
            mint: market.mint,
            total_supply: market.total_supply,
            initial_virtual_token_reserves: args.initial_virtual_token_reserves,
            initial_virtual_sol_reserves: args.initial_virtual_sol_reserves,
        });

        Ok(())
    }

    pub fn buy_exact_out(
        ctx: Context<BuyExactOut>,
        token_amount_out: u64,
        max_sol_cost: u64,
    ) -> Result<()> {
        require!(token_amount_out > 0, CurveError::InvalidAmount);

        require_valid_treasury(&ctx.accounts.platform_treasury, &ctx.accounts.global)?;
        require!(
            ctx.accounts.token_vault.amount >= token_amount_out,
            CurveError::InsufficientTokenLiquidity
        );
        let market_key = ctx.accounts.market.key();
        let market_info = ctx.accounts.market.to_account_info();
        let market_collection_id = ctx.accounts.market.collection_id;
        let market_bump = ctx.accounts.market.bump;

        let (reserve_cost, fee) = {
            let market = &ctx.accounts.market;
            require_market_active(market)?;
            require!(
                market.real_token_reserves >= token_amount_out,
                CurveError::InsufficientTokenLiquidity
            );

            let reserve_cost = buy_cost_exact_out(
                market.virtual_sol_reserves,
                market.virtual_token_reserves,
                token_amount_out,
            )?;
            let fee = fee_amount(reserve_cost, ctx.accounts.global.fee_bps)?;
            let total_cost = reserve_cost
                .checked_add(fee)
                .ok_or(error!(CurveError::MathOverflow))?;
            require!(total_cost <= max_sol_cost, CurveError::SlippageExceeded);

            (reserve_cost, fee)
        };

        system_program::transfer(
            CpiContext::new(
                ctx.accounts.system_program.to_account_info(),
                system_program::Transfer {
                    from: ctx.accounts.buyer.to_account_info(),
                    to: market_info.clone(),
                },
            ),
            reserve_cost,
        )?;

        if fee > 0 {
            system_program::transfer(
                CpiContext::new(
                    ctx.accounts.system_program.to_account_info(),
                    system_program::Transfer {
                        from: ctx.accounts.buyer.to_account_info(),
                        to: ctx.accounts.platform_treasury.to_account_info(),
                    },
                ),
                fee,
            )?;
        }

        let signer_seeds: &[&[u8]] = &[b"market", &market_collection_id, &[market_bump]];
        token::transfer(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                Transfer {
                    from: ctx.accounts.token_vault.to_account_info(),
                    to: ctx.accounts.buyer_token_ata.to_account_info(),
                    authority: market_info,
                },
                &[signer_seeds],
            ),
            token_amount_out,
        )?;

        let market = &mut ctx.accounts.market;
        market.virtual_sol_reserves = market
            .virtual_sol_reserves
            .checked_add(reserve_cost as u128)
            .ok_or(error!(CurveError::MathOverflow))?;
        market.virtual_token_reserves = market
            .virtual_token_reserves
            .checked_sub(token_amount_out as u128)
            .ok_or(error!(CurveError::MathOverflow))?;
        market.real_sol_reserves = market
            .real_sol_reserves
            .checked_add(reserve_cost)
            .ok_or(error!(CurveError::MathOverflow))?;
        market.real_token_reserves = market
            .real_token_reserves
            .checked_sub(token_amount_out)
            .ok_or(error!(CurveError::MathOverflow))?;
        market.total_platform_fees_collected = market
            .total_platform_fees_collected
            .checked_add(fee)
            .ok_or(error!(CurveError::MathOverflow))?;

        emit!(TradeExecuted {
            market: market_key,
            trader: ctx.accounts.buyer.key(),
            side: TradeSide::Buy,
            token_amount: token_amount_out,
            gross_sol_amount: reserve_cost,
            fee_paid: fee,
            net_sol_to_or_from_reserve: reserve_cost,
            virtual_sol_reserves: market.virtual_sol_reserves,
            virtual_token_reserves: market.virtual_token_reserves,
            real_sol_reserves: market.real_sol_reserves,
            real_token_reserves: market.real_token_reserves,
            status: market.status,
        });

        Ok(())
    }

    pub fn sell_exact_in(
        ctx: Context<SellExactIn>,
        token_amount_in: u64,
        min_sol_output: u64,
    ) -> Result<()> {
        require!(token_amount_in > 0, CurveError::InvalidAmount);

        require_valid_treasury(&ctx.accounts.platform_treasury, &ctx.accounts.global)?;
        let market_key = ctx.accounts.market.key();
        let market_info = ctx.accounts.market.to_account_info();

        let (gross_sol_out, fee, net_sol_out, tracked_real_sol_reserves) = {
            let market = &ctx.accounts.market;
            require_market_active(market)?;

            let gross_sol_out = sell_output_exact_in(
                market.virtual_sol_reserves,
                market.virtual_token_reserves,
                token_amount_in,
            )?;
            require!(gross_sol_out > 0, CurveError::InvalidAmount);
            require!(
                gross_sol_out <= market.real_sol_reserves,
                CurveError::InsufficientSolLiquidity
            );

            let fee = fee_amount(gross_sol_out, ctx.accounts.global.fee_bps)?;
            let net_sol_out = gross_sol_out
                .checked_sub(fee)
                .ok_or(error!(CurveError::MathOverflow))?;
            require!(net_sol_out >= min_sol_output, CurveError::SlippageExceeded);

            (gross_sol_out, fee, net_sol_out, market.real_sol_reserves)
        };

        token::transfer(
            CpiContext::new(
                ctx.accounts.token_program.to_account_info(),
                Transfer {
                    from: ctx.accounts.seller_token_ata.to_account_info(),
                    to: ctx.accounts.token_vault.to_account_info(),
                    authority: ctx.accounts.seller.to_account_info(),
                },
            ),
            token_amount_in,
        )?;

        debit_market_lamports(
            &market_info,
            gross_sol_out,
            tracked_real_sol_reserves,
        )?;
        credit_lamports(&ctx.accounts.seller.to_account_info(), net_sol_out)?;
        if fee > 0 {
            credit_lamports(&ctx.accounts.platform_treasury.to_account_info(), fee)?;
        }

        let market = &mut ctx.accounts.market;
        market.virtual_sol_reserves = market
            .virtual_sol_reserves
            .checked_sub(gross_sol_out as u128)
            .ok_or(error!(CurveError::MathOverflow))?;
        market.virtual_token_reserves = market
            .virtual_token_reserves
            .checked_add(token_amount_in as u128)
            .ok_or(error!(CurveError::MathOverflow))?;
        market.real_sol_reserves = market
            .real_sol_reserves
            .checked_sub(gross_sol_out)
            .ok_or(error!(CurveError::MathOverflow))?;
        market.real_token_reserves = market
            .real_token_reserves
            .checked_add(token_amount_in)
            .ok_or(error!(CurveError::MathOverflow))?;
        market.total_platform_fees_collected = market
            .total_platform_fees_collected
            .checked_add(fee)
            .ok_or(error!(CurveError::MathOverflow))?;

        emit!(TradeExecuted {
            market: market_key,
            trader: ctx.accounts.seller.key(),
            side: TradeSide::Sell,
            token_amount: token_amount_in,
            gross_sol_amount: gross_sol_out,
            fee_paid: fee,
            net_sol_to_or_from_reserve: net_sol_out,
            virtual_sol_reserves: market.virtual_sol_reserves,
            virtual_token_reserves: market.virtual_token_reserves,
            real_sol_reserves: market.real_sol_reserves,
            real_token_reserves: market.real_token_reserves,
            status: market.status,
        });

        Ok(())
    }

    pub fn freeze_market_for_migration(
        ctx: Context<FreezeMarketForMigration>,
        migration_target: Pubkey,
    ) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(market.status == MARKET_STATUS_ACTIVE, CurveError::MarketFrozen);

        market.status = MARKET_STATUS_FROZEN_FOR_MIGRATION;
        market.migration_target = migration_target;
        market.migration_started_at = Clock::get()?.unix_timestamp;

        emit!(MarketMigrationStateChanged {
            market: market.key(),
            status: market.status,
            migration_target,
            migration_started_at: market.migration_started_at,
            migration_completed_at: market.migration_completed_at,
        });
        Ok(())
    }

    pub fn mark_market_migrated(ctx: Context<MarkMarketMigrated>) -> Result<()> {
        let market = &mut ctx.accounts.market;
        require!(
            market.status == MARKET_STATUS_FROZEN_FOR_MIGRATION,
            CurveError::MigrationNotPrepared
        );

        market.status = MARKET_STATUS_MIGRATED;
        market.migration_completed_at = Clock::get()?.unix_timestamp;

        emit!(MarketMigrationStateChanged {
            market: market.key(),
            status: market.status,
            migration_target: market.migration_target,
            migration_started_at: market.migration_started_at,
            migration_completed_at: market.migration_completed_at,
        });
        Ok(())
    }
}

#[derive(Accounts)]
pub struct InitializeGlobal<'info> {
    #[account(mut)]
    pub payer: Signer<'info>,
    pub authority: Signer<'info>,
    #[account(
        init,
        payer = payer,
        space = 8 + GlobalConfig::INIT_SPACE,
        seeds = [b"global"],
        bump,
    )]
    pub global: Account<'info, GlobalConfig>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct UpdateGlobal<'info> {
    pub authority: Signer<'info>,
    #[account(
        mut,
        seeds = [b"global"],
        bump = global.bump,
        has_one = authority,
    )]
    pub global: Account<'info, GlobalConfig>,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone)]
pub struct CreateCollectionCoinArgs {
    pub collection_id: [u8; 32],
    pub decimals: u8,
    pub total_supply: u64,
    pub initial_virtual_token_reserves: u64,
    pub initial_virtual_sol_reserves: u64,
}

#[derive(Accounts)]
#[instruction(args: CreateCollectionCoinArgs)]
pub struct CreateCollectionCoin<'info> {
    #[account(mut)]
    pub creator: Signer<'info>,

    pub authority: Signer<'info>,

    #[account(
        seeds = [b"global"],
        bump = global.bump,
        has_one = authority,
    )]
    pub global: Account<'info, GlobalConfig>,

    #[account(
        init,
        payer = creator,
        space = 8 + Market::INIT_SPACE,
        seeds = [b"market", args.collection_id.as_ref()],
        bump,
    )]
    pub market: Account<'info, Market>,

    #[account(mut)]
    pub mint: Account<'info, Mint>,

    #[account(
        init,
        payer = creator,
        associated_token::mint = mint,
        associated_token::authority = market,
    )]
    pub token_vault: Account<'info, TokenAccount>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct BuyExactOut<'info> {
    #[account(mut)]
    pub buyer: Signer<'info>,

    #[account(
        seeds = [b"global"],
        bump = global.bump,
    )]
    pub global: Account<'info, GlobalConfig>,

    #[account(
        mut,
        seeds = [b"market", market.collection_id.as_ref()],
        bump = market.bump,
    )]
    pub market: Account<'info, Market>,

    #[account(mut, address = market.mint)]
    pub mint: Account<'info, Mint>,

    #[account(mut, address = market.token_vault)]
    pub token_vault: Account<'info, TokenAccount>,

    #[account(
        init_if_needed,
        payer = buyer,
        associated_token::mint = mint,
        associated_token::authority = buyer,
    )]
    pub buyer_token_ata: Account<'info, TokenAccount>,

    /// CHECK: validated in handler against `global.platform_treasury` and system ownership.
    #[account(mut)]
    pub platform_treasury: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, System>,
}

#[derive(Accounts)]
pub struct SellExactIn<'info> {
    #[account(mut)]
    pub seller: Signer<'info>,

    #[account(
        seeds = [b"global"],
        bump = global.bump,
    )]
    pub global: Account<'info, GlobalConfig>,

    #[account(
        mut,
        seeds = [b"market", market.collection_id.as_ref()],
        bump = market.bump,
    )]
    pub market: Account<'info, Market>,

    #[account(mut, address = market.mint)]
    pub mint: Account<'info, Mint>,

    #[account(mut, address = market.token_vault)]
    pub token_vault: Account<'info, TokenAccount>,

    #[account(
        mut,
        associated_token::mint = mint,
        associated_token::authority = seller,
    )]
    pub seller_token_ata: Account<'info, TokenAccount>,

    /// CHECK: validated in handler against `global.platform_treasury` and system ownership.
    #[account(mut)]
    pub platform_treasury: UncheckedAccount<'info>,

    pub token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct FreezeMarketForMigration<'info> {
    pub authority: Signer<'info>,
    #[account(
        seeds = [b"global"],
        bump = global.bump,
        has_one = authority,
    )]
    pub global: Account<'info, GlobalConfig>,
    #[account(
        mut,
        seeds = [b"market", market.collection_id.as_ref()],
        bump = market.bump,
    )]
    pub market: Account<'info, Market>,
}

#[derive(Accounts)]
pub struct MarkMarketMigrated<'info> {
    pub authority: Signer<'info>,
    #[account(
        seeds = [b"global"],
        bump = global.bump,
        has_one = authority,
    )]
    pub global: Account<'info, GlobalConfig>,
    #[account(
        mut,
        seeds = [b"market", market.collection_id.as_ref()],
        bump = market.bump,
    )]
    pub market: Account<'info, Market>,
}

#[account]
#[derive(InitSpace)]
pub struct GlobalConfig {
    pub version: u8,
    pub bump: u8,
    pub authority: Pubkey,
    pub platform_treasury: Pubkey,
    pub fee_bps: u16,
    pub graduation_enabled: bool,
    pub graduation_sol_threshold: u64,
    pub reserved: [u8; 64],
}

#[account]
#[derive(InitSpace)]
pub struct Market {
    pub version: u8,
    pub bump: u8,
    pub status: u8,
    pub collection_id: [u8; 32],
    pub creator: Pubkey,
    pub mint: Pubkey,
    pub token_vault: Pubkey,
    pub decimals: u8,
    pub total_supply: u64,
    pub virtual_token_reserves: u128,
    pub virtual_sol_reserves: u128,
    pub real_token_reserves: u64,
    pub real_sol_reserves: u64,
    pub total_platform_fees_collected: u64,
    pub migration_target: Pubkey,
    pub migration_started_at: i64,
    pub migration_completed_at: i64,
    pub created_at: i64,
    pub reserved: [u8; 64],
}

#[event]
pub struct GlobalConfigured {
    pub authority: Pubkey,
    pub platform_treasury: Pubkey,
    pub fee_bps: u16,
    pub graduation_enabled: bool,
    pub graduation_sol_threshold: u64,
}

#[event]
pub struct MarketCreated {
    pub market: Pubkey,
    pub creator: Pubkey,
    pub collection_id: [u8; 32],
    pub mint: Pubkey,
    pub total_supply: u64,
    pub initial_virtual_token_reserves: u64,
    pub initial_virtual_sol_reserves: u64,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone, PartialEq, Eq)]
pub enum TradeSide {
    Buy,
    Sell,
}

#[event]
pub struct TradeExecuted {
    pub market: Pubkey,
    pub trader: Pubkey,
    pub side: TradeSide,
    pub token_amount: u64,
    pub gross_sol_amount: u64,
    pub fee_paid: u64,
    pub net_sol_to_or_from_reserve: u64,
    pub virtual_sol_reserves: u128,
    pub virtual_token_reserves: u128,
    pub real_sol_reserves: u64,
    pub real_token_reserves: u64,
    pub status: u8,
}

#[event]
pub struct MarketMigrationStateChanged {
    pub market: Pubkey,
    pub status: u8,
    pub migration_target: Pubkey,
    pub migration_started_at: i64,
    pub migration_completed_at: i64,
}

#[error_code]
pub enum CurveError {
    #[msg("Invalid parameter")]
    InvalidParam,
    #[msg("Invalid amount")]
    InvalidAmount,
    #[msg("Math overflow")]
    MathOverflow,
    #[msg("Slippage exceeded")]
    SlippageExceeded,
    #[msg("Insufficient SOL liquidity")]
    InsufficientSolLiquidity,
    #[msg("Insufficient token liquidity")]
    InsufficientTokenLiquidity,
    #[msg("Market is frozen for migration")]
    MarketFrozen,
    #[msg("Market is already migrated")]
    MarketMigrated,
    #[msg("Invalid treasury account")]
    InvalidTreasury,
    #[msg("Mint account state is invalid")]
    InvalidMintState,
    #[msg("Mint authority must belong to the creator before creation")]
    InvalidMintAuthority,
    #[msg("Market migration has not been prepared")]
    MigrationNotPrepared,
}

fn require_market_active(market: &Account<'_, Market>) -> Result<()> {
    if market.status == MARKET_STATUS_MIGRATED {
        return err!(CurveError::MarketMigrated);
    }
    require!(market.status == MARKET_STATUS_ACTIVE, CurveError::MarketFrozen);
    Ok(())
}

fn require_valid_treasury(
    treasury: &UncheckedAccount<'_>,
    global: &Account<'_, GlobalConfig>,
) -> Result<()> {
    require!(treasury.key() == global.platform_treasury, CurveError::InvalidTreasury);
    require!(treasury.owner == &system_program::ID, CurveError::InvalidTreasury);
    Ok(())
}

fn fee_amount(amount: u64, fee_bps: u16) -> Result<u64> {
    let fee = (amount as u128)
        .checked_mul(fee_bps as u128)
        .ok_or(error!(CurveError::MathOverflow))?
        .checked_div(BPS_DENOMINATOR as u128)
        .ok_or(error!(CurveError::MathOverflow))?;
    u64::try_from(fee).map_err(|_| error!(CurveError::MathOverflow))
}

fn ceil_div(n: u128, d: u128) -> Result<u128> {
    require!(d > 0, CurveError::MathOverflow);
    let adj = d.checked_sub(1).ok_or(error!(CurveError::MathOverflow))?;
    n.checked_add(adj)
        .ok_or(error!(CurveError::MathOverflow))?
        .checked_div(d)
        .ok_or(error!(CurveError::MathOverflow))
}

/// Constant-product exact-out buy cost using virtual reserves.
/// cost = ceil(vs * dx / (vt - dx))
fn buy_cost_exact_out(virtual_sol: u128, virtual_token: u128, token_out: u64) -> Result<u64> {
    let dx = token_out as u128;
    require!(dx > 0, CurveError::InvalidAmount);
    require!(dx < virtual_token, CurveError::InsufficientTokenLiquidity);

    let numerator = virtual_sol
        .checked_mul(dx)
        .ok_or(error!(CurveError::MathOverflow))?;
    let denominator = virtual_token
        .checked_sub(dx)
        .ok_or(error!(CurveError::MathOverflow))?;
    let cost = ceil_div(numerator, denominator)?;
    u64::try_from(cost).map_err(|_| error!(CurveError::MathOverflow))
}

/// Constant-product exact-in sell output using virtual reserves.
/// out = floor(vs * dx / (vt + dx))
fn sell_output_exact_in(virtual_sol: u128, virtual_token: u128, token_in: u64) -> Result<u64> {
    let dx = token_in as u128;
    require!(dx > 0, CurveError::InvalidAmount);

    let numerator = virtual_sol
        .checked_mul(dx)
        .ok_or(error!(CurveError::MathOverflow))?;
    let denominator = virtual_token
        .checked_add(dx)
        .ok_or(error!(CurveError::MathOverflow))?;
    let out = numerator
        .checked_div(denominator)
        .ok_or(error!(CurveError::MathOverflow))?;
    u64::try_from(out).map_err(|_| error!(CurveError::MathOverflow))
}

fn debit_market_lamports(market_ai: &AccountInfo, amount: u64, tracked_reserve: u64) -> Result<()> {
    require!(amount <= tracked_reserve, CurveError::InsufficientSolLiquidity);
    let mut market_lamports = market_ai.try_borrow_mut_lamports()?;
    require!(**market_lamports >= amount, CurveError::InsufficientSolLiquidity);
    **market_lamports = (**market_lamports)
        .checked_sub(amount)
        .ok_or(error!(CurveError::MathOverflow))?;
    Ok(())
}

fn credit_lamports(target_ai: &AccountInfo, amount: u64) -> Result<()> {
    let mut target_lamports = target_ai.try_borrow_mut_lamports()?;
    **target_lamports = (**target_lamports)
        .checked_add(amount)
        .ok_or(error!(CurveError::MathOverflow))?;
    Ok(())
}
