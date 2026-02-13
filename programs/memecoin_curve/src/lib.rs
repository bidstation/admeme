use anchor_lang::prelude::*;
use anchor_lang::solana_program::program_option::COption;
use anchor_lang::solana_program::pubkey;
use anchor_spl::associated_token::AssociatedToken;
use anchor_spl::token::{
    self, Burn, Mint, MintTo, SetAuthority, Token, TokenAccount, Transfer,
};
use anchor_spl::token::spl_token::instruction::AuthorityType;

// Deployed program id (mainnet-beta)
declare_id!("BKWVgcPdNvYXUVBzfy17RDtSy7nvyxudUEF2yK34EYvu");

// Trading fee: 1% total, split 50/50 between platform and uploader (creator).
const TRADE_FEE_BPS_TOTAL: u16 = 100; // 1%

// a2m_campaign_vault program id (must match `apps/ad2-meme/contracts/lib.rs`)
const A2M_CAMPAIGN_VAULT_PROGRAM_ID: Pubkey = pubkey!("2s7V6oGMGMY2ys9y9FHBKt9HPvxqCUK2DpXEWegWzA8G");

#[program]
pub mod memecoin_curve {
    use super::*;

    /// Create the **campaign coin** for a specific `a2m_campaign_vault` campaign.
    ///
    /// This replaces the old "per-meme memecoin" creation flow:
    /// - only **one coin per campaign** (seed = campaign PDA pubkey bytes)
    /// - only the campaign advertiser may create it (must sign + provide the correct campaign PDA)
    pub fn create_campaign_coin(
        ctx: Context<CreateCampaignCoin>,
        campaign_id: u64,
        a: u64,
        b: u64,
        fee_bps: u16,
        decimals: u8,
    ) -> Result<()> {
        // Fee is fixed (prevents per-memecoin fee mismatch across UI/backends).
        require!(fee_bps == TRADE_FEE_BPS_TOTAL, CurveError::InvalidParam);

        // ---- Campaign authorization ----
        // Require the provided campaign account to be the canonical PDA for:
        //   seeds = ["campaign", advertiser_pubkey, campaign_id_le]
        // under the a2m_campaign_vault program id.
        let campaign_info = ctx.accounts.campaign.to_account_info();
        require!(!campaign_info.data_is_empty(), CurveError::InvalidCampaign);
        require!(campaign_info.owner == &A2M_CAMPAIGN_VAULT_PROGRAM_ID, CurveError::InvalidCampaign);

        let (expected_campaign, _) = Pubkey::find_program_address(
            &[
                b"campaign",
                ctx.accounts.creator.key().as_ref(),
                &campaign_id.to_le_bytes(),
            ],
            &A2M_CAMPAIGN_VAULT_PROGRAM_ID,
        );
        require_keys_eq!(
            ctx.accounts.campaign.key(),
            expected_campaign,
            CurveError::InvalidCampaign
        );

        // One-coin-per-campaign: seed is campaign pubkey bytes.
        let seed: [u8; 32] = ctx.accounts.campaign.key().to_bytes();

        let state = &mut ctx.accounts.memecoin;
        state.bump = ctx.bumps.memecoin;
        state.seed = seed;
        state.creator = ctx.accounts.creator.key();
        state.base_mint = ctx.accounts.base_mint.key();
        state.memecoin_mint = ctx.accounts.memecoin_mint.key();
        state.reserve_vault = ctx.accounts.reserve_vault.key();
        state.creator_fee_vault = ctx.accounts.creator_fee_vault.key();
        state.a = a as u128;
        state.b = b as u128;
        // Keep field for compatibility, but treat it as informational (fixed constant on-chain).
        state.fee_bps = TRADE_FEE_BPS_TOTAL;
        state.decimals = decimals;
        state.supply = 0u128;
        state.created_at = Clock::get()?.unix_timestamp;
        state.finalized = false;
        Ok(())
    }

    /// Transfer the memecoin mint authority from the creator to the memecoin PDA.
    /// Intended flow:
    /// 1) `create_campaign_coin` initializes the mint with `creator` as temporary mint authority
    /// 2) client creates Metaplex metadata directly (mint authority = creator)
    /// 3) client calls `handoff_mint_authority` so `buy_memecoin` can mint (mint authority = memecoin PDA)
    pub fn handoff_mint_authority(ctx: Context<HandoffMintAuthority>) -> Result<()> {
        // Only the original creator can do the handoff
        require_keys_eq!(
            ctx.accounts.creator.key(),
            ctx.accounts.memecoin.creator,
            CurveError::Unauthorized
        );
        // Prevent off-curve mints before the handoff
        require!(ctx.accounts.memecoin_mint.supply == 0, CurveError::InvalidState);
        // Ensure the creator is still the current mint authority
        require!(
            ctx.accounts.memecoin_mint.mint_authority == COption::Some(ctx.accounts.creator.key()),
            CurveError::InvalidState
        );

        let cpi_accounts = SetAuthority {
            account_or_mint: ctx.accounts.memecoin_mint.to_account_info(),
            current_authority: ctx.accounts.creator.to_account_info(),
        };
        token::set_authority(
            CpiContext::new(ctx.accounts.token_program.to_account_info(), cpi_accounts),
            AuthorityType::MintTokens,
            Some(ctx.accounts.memecoin.key()),
        )?;

        Ok(())
    }

    /// Buy `amount_out` memecoins; cost is the integral over [s, s+amount_out].
    /// Transfers base tokens from buyer to reserve and mints memecoins to buyer.
    ///
    /// Slippage protection: the caller must pass `max_total` (maximum total base
    /// tokens they are willing to pay including fee). The on-chain computed
    /// `total` must be less than or equal to `max_total`.
    pub fn buy_memecoin(ctx: Context<BuyMemecoin>, amount_out: u64, max_total: u64) -> Result<()> {
        require!(!ctx.accounts.memecoin.finalized, CurveError::Unauthorized);
        require!(amount_out > 0, CurveError::InvalidAmount);
        let s = ctx.accounts.memecoin.supply; // current supply (u128 base units)
        let d = amount_out as u128;

        // Scale the integral by memecoin decimals: supply is tracked in base units.
        // Desired model uses whole-token units, so divide by 10^decimals appropriately.
        let cost = linear_integral_cost_scaled(
            ctx.accounts.memecoin.a,
            ctx.accounts.memecoin.b,
            s,
            d,
            ctx.accounts.memecoin.decimals,
        )?;
        let fee = cost
            .checked_mul(TRADE_FEE_BPS_TOTAL as u128)
            .ok_or_else(|| error!(CurveError::MathOverflow))?
            .checked_div(10_000)
            .ok_or_else(|| error!(CurveError::MathOverflow))?;
        let total_u128 = cost
            .checked_add(fee)
            .ok_or_else(|| error!(CurveError::MathOverflow))?;

        // Ensure buyer has enough base token; also enforce slippage bound (compare in u128)
        require!((ctx.accounts.buyer_base_ata.amount as u128) >= total_u128, CurveError::InsufficientFunds);
        require!(total_u128 <= (max_total as u128), CurveError::InvalidAmount);
        // Ensure amounts fit into u64 for token program transfers
        require!(total_u128 <= (u64::MAX as u128), CurveError::InvalidAmount);

        // Move base to reserve and creator escrow (split)
        let cost_u64 = u128_to_u64_checked(cost)?;
        let fee_total_u64 = u128_to_u64_checked(fee)?;
        // Split 50/50. If odd, the extra base unit goes to creator.
        let platform_fee_u64 = fee_total_u64 / 2;
        let creator_fee_u64 = fee_total_u64
            .checked_sub(platform_fee_u64)
            .ok_or_else(|| error!(CurveError::MathOverflow))?;
        token::transfer(ctx.accounts.transfer_base_to_reserve(), cost_u64)?;
        if platform_fee_u64 > 0 {
            token::transfer(ctx.accounts.transfer_base_to_platform_escrow(), platform_fee_u64)?;
        }
        if creator_fee_u64 > 0 {
            token::transfer(ctx.accounts.transfer_base_to_creator_escrow(), creator_fee_u64)?;
        }

        // Mint memecoins to buyer
        // Mint memecoins to buyer (PDA signer)
        let mint_cpi = MintTo {
            mint: ctx.accounts.memecoin_mint.to_account_info(),
            to: ctx.accounts.buyer_memecoin_ata.to_account_info(),
            authority: ctx.accounts.memecoin.to_account_info(),
        };
        let seeds = [
            b"memecoin".as_ref(),
            ctx.accounts.memecoin.seed.as_ref(),
            &[ctx.accounts.memecoin.bump],
        ];
        token::mint_to(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                mint_cpi,
                &[&seeds],
            ),
            amount_out,
        )?;

        // Update supply
        ctx.accounts.memecoin.supply = s
            .checked_add(d)
            .ok_or_else(|| error!(CurveError::MathOverflow))?;
        Ok(())
    }

    /// Sell `amount_in` memecoins; refund is the integral over [s-amount_in, s].
    /// Burns seller memecoins and transfers base tokens from reserve to seller.
    ///
    /// Slippage protection: the caller must pass `min_refund` (minimum base
    /// tokens they expect to receive net of fees). The on-chain computed net
    /// refund must be greater than or equal to `min_refund`.
    pub fn sell_memecoin(ctx: Context<SellMemecoin>, amount_in: u64, min_refund: u64) -> Result<()> {
        require!(!ctx.accounts.memecoin.finalized, CurveError::Unauthorized);
        require!(amount_in > 0, CurveError::InvalidAmount);
        let s = ctx.accounts.memecoin.supply;
        let d = amount_in as u128;
        require!(s >= d, CurveError::InvalidAmount);

        let s0 = s
            .checked_sub(d)
            .ok_or_else(|| error!(CurveError::MathOverflow))?;
        // refund equals the cost of moving from s0 to s on the curve
        let refund_u128 = linear_integral_cost_scaled(
            ctx.accounts.memecoin.a,
            ctx.accounts.memecoin.b,
            s0,
            d,
            ctx.accounts.memecoin.decimals,
        )?;

        // Calculate creator fee on sell and net refund
        let fee_u128 = refund_u128
            .checked_mul(TRADE_FEE_BPS_TOTAL as u128)
            .ok_or_else(|| error!(CurveError::MathOverflow))?
            .checked_div(10_000)
            .ok_or_else(|| error!(CurveError::MathOverflow))?;
        let refund_net_u128 = refund_u128
            .checked_sub(fee_u128)
            .ok_or_else(|| error!(CurveError::MathOverflow))?;

        // Burn memecoins
        token::burn(ctx.accounts.burn_from_seller(), amount_in)?;

        // Pay base from reserve to seller (memecoin PDA signs)
        require!((ctx.accounts.reserve_vault.amount as u128) >= refund_u128, CurveError::InsufficientReserve);
        // Enforce slippage bound on net refund and transfer base from reserve to seller (PDA signer)
        require!(refund_net_u128 >= (min_refund as u128), CurveError::InvalidAmount);
        // Downcast checked to u64 for transfers
        let refund_net_u64 = u128_to_u64_checked(refund_net_u128)?;
        let fee_total_u64 = u128_to_u64_checked(fee_u128)?;
        // Split 50/50. If odd, the extra base unit goes to creator.
        let platform_fee_u64 = fee_total_u64 / 2;
        let creator_fee_u64 = fee_total_u64
            .checked_sub(platform_fee_u64)
            .ok_or_else(|| error!(CurveError::MathOverflow))?;
        let xfer_cpi = Transfer {
            from: ctx.accounts.reserve_vault.to_account_info(),
            to: ctx.accounts.seller_base_ata.to_account_info(),
            authority: ctx.accounts.memecoin.to_account_info(),
        };
        let seeds = [
            b"memecoin".as_ref(),
            ctx.accounts.memecoin.seed.as_ref(),
            &[ctx.accounts.memecoin.bump],
        ];
        token::transfer(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                xfer_cpi,
                &[&seeds],
            ),
            refund_net_u64,
        )?;

        // Transfer fees from reserve to platform/creator escrow (PDA signer)
        if platform_fee_u64 > 0 {
            let xfer_fee_cpi = Transfer {
                from: ctx.accounts.reserve_vault.to_account_info(),
                to: ctx.accounts.platform_fee_vault.to_account_info(),
                authority: ctx.accounts.memecoin.to_account_info(),
            };
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    xfer_fee_cpi,
                    &[&seeds],
                ),
                platform_fee_u64,
            )?;
        }
        if creator_fee_u64 > 0 {
            let xfer_fee_cpi = Transfer {
                from: ctx.accounts.reserve_vault.to_account_info(),
                to: ctx.accounts.creator_fee_vault.to_account_info(),
                authority: ctx.accounts.memecoin.to_account_info(),
            };
            token::transfer(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    xfer_fee_cpi,
                    &[&seeds],
                ),
                creator_fee_u64,
            )?;
        }

        // Update supply
        ctx.accounts.memecoin.supply = s0;
        Ok(())
    }

    /// Initialize the platform singleton with an authority who must co-sign claims.
    pub fn init_platform(ctx: Context<InitPlatform>, authority: Pubkey) -> Result<()> {
        let p = &mut ctx.accounts.platform;
        p.bump = ctx.bumps.platform;
        p.authority = authority;
        Ok(())
    }

    /// Claim creator fees from the escrow vault to any destination ATA, approved by platform.
    pub fn claim_creator_fees(ctx: Context<ClaimCreatorFees>, amount: u64) -> Result<()> {
        // Check platform authority signer matches stored authority
        require_keys_eq!(
            ctx.accounts.platform_authority.key(),
            ctx.accounts.platform.authority,
            CurveError::Unauthorized
        );

        // Sanity: destination mint must match base mint
        require_keys_eq!(
            ctx.accounts.destination.mint,
            ctx.accounts.base_mint.key(),
            CurveError::InvalidParam
        );

        // Move funds from creator fee vault to destination (memecoin PDA signs)
        let seeds = [
            b"memecoin".as_ref(),
            ctx.accounts.memecoin.seed.as_ref(),
            &[ctx.accounts.memecoin.bump],
        ];
        let xfer_cpi = Transfer {
            from: ctx.accounts.creator_fee_vault.to_account_info(),
            to: ctx.accounts.destination.to_account_info(),
            authority: ctx.accounts.memecoin.to_account_info(),
        };
        token::transfer(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                xfer_cpi,
                &[&seeds],
            ),
            amount,
        )?;

        Ok(())
    }

    /// Claim platform fees from the platform fee vault to any destination ATA.
    pub fn claim_platform_fees(ctx: Context<ClaimPlatformFees>, amount: u64) -> Result<()> {
        // Check platform authority signer matches stored authority
        require_keys_eq!(
            ctx.accounts.platform_authority.key(),
            ctx.accounts.platform.authority,
            CurveError::Unauthorized
        );
        require!(amount > 0, CurveError::InvalidAmount);

        // Sanity: destination mint must match base mint
        require_keys_eq!(
            ctx.accounts.destination.mint,
            ctx.accounts.base_mint.key(),
            CurveError::InvalidParam
        );

        require!(
            ctx.accounts.platform_fee_vault.amount >= amount,
            CurveError::InsufficientFeeVault
        );

        // Move funds from platform fee vault to destination (platform PDA signs)
        let seeds = [b"platform".as_ref(), &[ctx.accounts.platform.bump]];
        let xfer_cpi = Transfer {
            from: ctx.accounts.platform_fee_vault.to_account_info(),
            to: ctx.accounts.destination.to_account_info(),
            authority: ctx.accounts.platform.to_account_info(),
        };
        token::transfer(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                xfer_cpi,
                &[&seeds],
            ),
            amount,
        )?;
        Ok(())
    }

    // Removed per-memecoin liquidity config; use global LiquidityDefaults instead.

    /// Initialize global defaults for a base mint. Platform authority only.
    pub fn init_liquidity_defaults(
        ctx: Context<InitLiquidityDefaults>,
        threshold_base: u64,
        min_reserve_base: u64,
        destination: Pubkey,
        enabled: bool,
    ) -> Result<()> {
        // Require platform authorization
        require_keys_eq!(
            ctx.accounts.platform_authority.key(),
            ctx.accounts.platform.authority,
            CurveError::Unauthorized
        );
        require!(threshold_base > 0, CurveError::InvalidParam);
        // Destination mint must match base mint
        require_keys_eq!(ctx.accounts.destination.mint, ctx.accounts.base_mint.key(), CurveError::InvalidParam);

        let d = &mut ctx.accounts.liquidity_defaults;
        d.bump = ctx.bumps.liquidity_defaults;
        d.base_mint = ctx.accounts.base_mint.key();
        d.threshold_base = threshold_base;
        d.min_reserve_base = min_reserve_base;
        d.destination = destination;
        d.enabled = enabled;
        Ok(())
    }

    /// Update global defaults for a base mint. Platform authority only.
    pub fn update_liquidity_defaults(
        ctx: Context<UpdateLiquidityDefaults>,
        threshold_base: u64,
        min_reserve_base: u64,
        destination: Pubkey,
        enabled: bool,
    ) -> Result<()> {
        // Require platform authorization
        require_keys_eq!(
            ctx.accounts.platform_authority.key(),
            ctx.accounts.platform.authority,
            CurveError::Unauthorized
        );
        require!(threshold_base > 0, CurveError::InvalidParam);

        let d = &mut ctx.accounts.liquidity_defaults;
        // base_mint is immutable; assert match
        require_keys_eq!(ctx.accounts.base_mint.key(), d.base_mint, CurveError::InvalidParam);
        // destination mint must match base mint
        require_keys_eq!(ctx.accounts.destination.mint, ctx.accounts.base_mint.key(), CurveError::InvalidParam);

        d.threshold_base = threshold_base;
        d.min_reserve_base = min_reserve_base;
        d.destination = destination;
        d.enabled = enabled;
        Ok(())
    }

    /// Sweep excess base tokens from reserve to default destination when reserve exceeds
    /// min_reserve + threshold (from LiquidityDefaults). Anyone can trigger.
    pub fn sweep_excess(ctx: Context<SweepExcess>) -> Result<()> {
        let d = &ctx.accounts.liquidity_defaults;
        require!(d.enabled, CurveError::Unauthorized);

        // Sanity checks
        // base mint consistent across memecoin and defaults
        require_keys_eq!(ctx.accounts.base_mint.key(), ctx.accounts.memecoin.base_mint, CurveError::InvalidParam);
        require_keys_eq!(ctx.accounts.base_mint.key(), d.base_mint, CurveError::InvalidParam);
        // destination must be the configured default destination and match base mint
        require_keys_eq!(ctx.accounts.destination.key(), d.destination, CurveError::InvalidParam);
        require_keys_eq!(ctx.accounts.destination.mint, ctx.accounts.base_mint.key(), CurveError::InvalidParam);
        // reserve vault belongs to memecoin
        require_keys_eq!(ctx.accounts.reserve_vault.key(), ctx.accounts.memecoin.reserve_vault, CurveError::InvalidParam);

        let reserve_amt = ctx.accounts.reserve_vault.amount;
        let min_keep = d.min_reserve_base;
        if reserve_amt <= min_keep { return Ok(()); }
        let available = reserve_amt
            .checked_sub(min_keep)
            .ok_or_else(|| error!(CurveError::MathOverflow))?;
        if available < d.threshold_base { return Ok(()); }

        // Transfer available from reserve to destination (PDA signer)
        let xfer = Transfer {
            from: ctx.accounts.reserve_vault.to_account_info(),
            to: ctx.accounts.destination.to_account_info(),
            authority: ctx.accounts.memecoin.to_account_info(),
        };
        let seeds = [b"memecoin".as_ref(), ctx.accounts.memecoin.seed.as_ref(), &[ctx.accounts.memecoin.bump]];
        token::transfer(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                xfer,
                &[&seeds],
            ),
            available,
        )?;

        Ok(())
    }

    /// Disable curve trading permanently, gated by threshold from defaults.
    /// This does NOT interact with Raydium yet; it only freezes the curve.
    pub fn finalize_disable_curve(ctx: Context<FinalizeDisableCurve>) -> Result<()> {
        // Curve must not be finalized already
        require!(!ctx.accounts.memecoin.finalized, CurveError::InvalidParam);

        // Base mint/defaults must match
        require_keys_eq!(ctx.accounts.base_mint.key(), ctx.accounts.memecoin.base_mint, CurveError::InvalidParam);
        require_keys_eq!(ctx.accounts.liquidity_defaults.base_mint, ctx.accounts.base_mint.key(), CurveError::InvalidParam);

        // Threshold reached check
        let reserve_amt = ctx.accounts.reserve_vault.amount;
        require!(reserve_amt >= ctx.accounts.liquidity_defaults.threshold_base, CurveError::InsufficientReserve);

        // Flip flag
        ctx.accounts.memecoin.finalized = true;
        Ok(())
    }

    /// Revoke mint and freeze authorities on the memecoin mint (post-finalization).
    pub fn revoke_mint_authorities(ctx: Context<RevokeMintAuthorities>) -> Result<()> {
        require!(ctx.accounts.memecoin.finalized, CurveError::Unauthorized);

        // PDA signer seeds
        let seeds = [b"memecoin".as_ref(), ctx.accounts.memecoin.seed.as_ref(), &[ctx.accounts.memecoin.bump]];

        // Revoke MintTokens authority
        if ctx.accounts.memecoin_mint.mint_authority == COption::Some(ctx.accounts.memecoin.key()) {
            let cpi_accounts = SetAuthority {
                account_or_mint: ctx.accounts.memecoin_mint.to_account_info(),
                current_authority: ctx.accounts.memecoin.to_account_info(),
            };
            token::set_authority(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    cpi_accounts,
                    &[&seeds],
                ),
                AuthorityType::MintTokens,
                None,
            )?;
        }

        // Revoke FreezeAccount authority (if present)
        if ctx.accounts.memecoin_mint.freeze_authority == COption::Some(ctx.accounts.memecoin.key()) {
            let cpi_accounts2 = SetAuthority {
                account_or_mint: ctx.accounts.memecoin_mint.to_account_info(),
                current_authority: ctx.accounts.memecoin.to_account_info(),
            };
            token::set_authority(
                CpiContext::new_with_signer(
                    ctx.accounts.token_program.to_account_info(),
                    cpi_accounts2,
                    &[&seeds],
                ),
                AuthorityType::FreezeAccount,
                None,
            )?;
        }

        Ok(())
    }

    /// After finalization, allow the original creator to withdraw any remaining
    /// base tokens from the reserve vault. This acts as a destructor path to
    /// recover the min_reserve_base that cannot be swept by `sweep_excess`.
    pub fn withdraw_finalized_reserve(ctx: Context<WithdrawFinalizedReserve>) -> Result<()> {
        // Only after curve has been finalized
        require!(ctx.accounts.memecoin.finalized, CurveError::Unauthorized);

        // Only the original creator may perform this action
        require_keys_eq!(
            ctx.accounts.creator.key(),
            ctx.accounts.memecoin.creator,
            CurveError::Unauthorized
        );

        // Sanity checks
        require_keys_eq!(
            ctx.accounts.base_mint.key(),
            ctx.accounts.memecoin.base_mint,
            CurveError::InvalidParam
        );
        require_keys_eq!(
            ctx.accounts.reserve_vault.key(),
            ctx.accounts.memecoin.reserve_vault,
            CurveError::InvalidParam
        );
        // Destination must be creator's ATA for the base mint
        require_keys_eq!(ctx.accounts.destination.mint, ctx.accounts.base_mint.key(), CurveError::InvalidParam);
        require_keys_eq!(ctx.accounts.destination.owner, ctx.accounts.creator.key(), CurveError::InvalidParam);

        let amount = ctx.accounts.reserve_vault.amount;
        if amount == 0 {
            return Ok(());
        }

        // Transfer entire balance from reserve_vault to creator's ATA (PDA signs)
        let seeds = [b"memecoin".as_ref(), ctx.accounts.memecoin.seed.as_ref(), &[ctx.accounts.memecoin.bump]];
        let xfer = Transfer {
            from: ctx.accounts.reserve_vault.to_account_info(),
            to: ctx.accounts.destination.to_account_info(),
            authority: ctx.accounts.memecoin.to_account_info(),
        };
        token::transfer(
            CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                xfer,
                &[&seeds],
            ),
            amount,
        )?;

        Ok(())
    }
}

/* -------------------- State -------------------- */

#[account]
pub struct Memecoin {
    pub bump: u8,
    pub seed: [u8; 32],
    pub creator: Pubkey,
    pub base_mint: Pubkey,
    pub memecoin_mint: Pubkey,
    pub reserve_vault: Pubkey,
    pub creator_fee_vault: Pubkey,
    pub a: u128,       // intercept (base token units per memecoin unit)
    pub b: u128,       // slope
    pub fee_bps: u16,  // 0..10000
    pub decimals: u8,  // memecoin mint decimals
    pub supply: u128,  // current minted supply (memecoin base units)
    pub created_at: i64, // unix timestamp (seconds)
    pub finalized: bool, // curve disabled when true
}
impl Memecoin {
    // bump + seed + creator + base_mint + memecoin_mint + reserve_vault + creator_fee_vault
    // + a + b + fee_bps + decimals + supply + created_at + finalized
    pub const LEN: usize = 1 + 32 + 32 + 32 + 32 + 32 + 32 + 16 + 16 + 2 + 1 + 16 + 8 + 1;
}

#[account]
pub struct Platform {
    pub bump: u8,
    pub authority: Pubkey,
}
impl Platform {
    pub const LEN: usize = 1 + 32;
}

// Removed per-memecoin LiquidityConfig; use LiquidityDefaults instead.

#[account]
pub struct LiquidityDefaults {
    pub bump: u8,
    pub base_mint: Pubkey,
    pub threshold_base: u64,
    pub min_reserve_base: u64,
    pub destination: Pubkey, // TokenAccount for base_mint
    pub enabled: bool,
}
impl LiquidityDefaults {
    // bump + base_mint + threshold + min_reserve + destination + enabled
    pub const LEN: usize = 1 + 32 + 8 + 8 + 32 + 1;
}

/* -------------------- Accounts -------------------- */

#[derive(Accounts)]
#[instruction(campaign_id: u64, a: u64, b: u64, fee_bps: u16, decimals: u8)]
pub struct CreateCampaignCoin<'info> {
    #[account(mut)]
    pub creator: Signer<'info>,

    /// CHECK: This account belongs to the external `a2m_campaign_vault` program and is intentionally
    /// unchecked here. It is verified in-handler by checking:
    /// - owner == `A2M_CAMPAIGN_VAULT_PROGRAM_ID`
    /// - key == PDA(["campaign", creator_pubkey, campaign_id_le], A2M_CAMPAIGN_VAULT_PROGRAM_ID)
    pub campaign: UncheckedAccount<'info>,

    #[account(seeds = [b"platform"], bump = platform.bump)]
    pub platform: Account<'info, Platform>,
    #[account(
        init_if_needed,
        payer = creator,
        associated_token::mint = base_mint,
        associated_token::authority = platform,
    )]
    pub platform_fee_vault: Account<'info, TokenAccount>,

    #[account(
        init,
        payer = creator,
        space = 8 + Memecoin::LEN,
        seeds = [b"memecoin", campaign.key().as_ref()],
        bump,
    )]
    pub memecoin: Account<'info, Memecoin>,

    #[account(
        init,
        payer = creator,
        mint::decimals = decimals,
        mint::authority = creator,
    )]
    pub memecoin_mint: Account<'info, Mint>,

    /// Base currency mint used for pricing and reserves (e.g., a platform token)
    pub base_mint: Account<'info, Mint>,

    #[account(
        init,
        payer = creator,
        associated_token::mint = base_mint,
        associated_token::authority = memecoin,
    )]
    pub reserve_vault: Account<'info, TokenAccount>,

    #[account(
        init,
        payer = creator,
        seeds = [b"creator_fee_vault", campaign.key().as_ref()],
        bump,
        token::mint = base_mint,
        token::authority = memecoin,
    )]
    pub creator_fee_vault: Account<'info, TokenAccount>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, anchor_lang::system_program::System>,
}

#[derive(Accounts)]
pub struct HandoffMintAuthority<'info> {
    pub creator: Signer<'info>,

    #[account(
        seeds = [b"memecoin", memecoin.seed.as_ref()],
        bump = memecoin.bump,
    )]
    pub memecoin: Account<'info, Memecoin>,

    #[account(
        mut,
        constraint = memecoin_mint.key() == memecoin.memecoin_mint
    )]
    pub memecoin_mint: Account<'info, Mint>,

    pub token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct BuyMemecoin<'info> {
    #[account(mut)]
    pub buyer: Signer<'info>,

    #[account(seeds = [b"platform"], bump = platform.bump)]
    pub platform: Account<'info, Platform>,
    #[account(
        init_if_needed,
        payer = buyer,
        associated_token::mint = base_mint,
        associated_token::authority = platform,
    )]
    pub platform_fee_vault: Account<'info, TokenAccount>,

    #[account(
        mut,
        seeds = [b"memecoin", memecoin.seed.as_ref()],
        bump = memecoin.bump,
    )]
    pub memecoin: Account<'info, Memecoin>,

    #[account(mut, constraint = memecoin_mint.key() == memecoin.memecoin_mint)]
    pub memecoin_mint: Account<'info, Mint>,
    #[account(mut, constraint = base_mint.key() == memecoin.base_mint)]
    pub base_mint: Account<'info, Mint>,

    #[account(mut, constraint = reserve_vault.key() == memecoin.reserve_vault)]
    pub reserve_vault: Account<'info, TokenAccount>,

    #[account(mut, constraint = creator_fee_vault.key() == memecoin.creator_fee_vault)]
    pub creator_fee_vault: Account<'info, TokenAccount>,

    #[account(
        init_if_needed,
        payer = buyer,
        associated_token::mint = base_mint,
        associated_token::authority = buyer,
    )]
    pub buyer_base_ata: Account<'info, TokenAccount>,
    #[account(
        init_if_needed,
        payer = buyer,
        associated_token::mint = memecoin_mint,
        associated_token::authority = buyer,
    )]
    pub buyer_memecoin_ata: Account<'info, TokenAccount>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, anchor_lang::system_program::System>,
}
impl<'info> BuyMemecoin<'info> {
    fn transfer_base_to_reserve(&self) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let c = Transfer {
            from: self.buyer_base_ata.to_account_info(),
            to: self.reserve_vault.to_account_info(),
            authority: self.buyer.to_account_info(),
        };
        CpiContext::new(self.token_program.to_account_info(), c)
    }

    fn transfer_base_to_platform_escrow(&self) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let c = Transfer {
            from: self.buyer_base_ata.to_account_info(),
            to: self.platform_fee_vault.to_account_info(),
            authority: self.buyer.to_account_info(),
        };
        CpiContext::new(self.token_program.to_account_info(), c)
    }

    fn transfer_base_to_creator_escrow(&self) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let c = Transfer {
            from: self.buyer_base_ata.to_account_info(),
            to: self.creator_fee_vault.to_account_info(),
            authority: self.buyer.to_account_info(),
        };
        CpiContext::new(self.token_program.to_account_info(), c)
    }
}

#[derive(Accounts)]
pub struct SellMemecoin<'info> {
    #[account(mut)]
    pub seller: Signer<'info>,

    #[account(seeds = [b"platform"], bump = platform.bump)]
    pub platform: Account<'info, Platform>,
    #[account(
        init_if_needed,
        payer = seller,
        associated_token::mint = base_mint,
        associated_token::authority = platform,
    )]
    pub platform_fee_vault: Account<'info, TokenAccount>,

    #[account(
        mut,
        seeds = [b"memecoin", memecoin.seed.as_ref()],
        bump = memecoin.bump,
    )]
    pub memecoin: Account<'info, Memecoin>,

    #[account(mut, constraint = memecoin_mint.key() == memecoin.memecoin_mint)]
    pub memecoin_mint: Account<'info, Mint>,
    #[account(mut, constraint = base_mint.key() == memecoin.base_mint)]
    pub base_mint: Account<'info, Mint>,

    #[account(mut, constraint = reserve_vault.key() == memecoin.reserve_vault)]
    pub reserve_vault: Account<'info, TokenAccount>,

    #[account(mut, constraint = creator_fee_vault.key() == memecoin.creator_fee_vault)]
    pub creator_fee_vault: Account<'info, TokenAccount>,

    #[account(
        init_if_needed,
        payer = seller,
        associated_token::mint = base_mint,
        associated_token::authority = seller,
    )]
    pub seller_base_ata: Account<'info, TokenAccount>,
    #[account(
        mut,
        associated_token::mint = memecoin_mint,
        associated_token::authority = seller,
    )]
    pub seller_memecoin_ata: Account<'info, TokenAccount>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, anchor_lang::system_program::System>,
}
impl<'info> SellMemecoin<'info> {
    fn burn_from_seller(&self) -> CpiContext<'_, '_, '_, 'info, Burn<'info>> {
        let c = Burn {
            mint: self.memecoin_mint.to_account_info(),
            from: self.seller_memecoin_ata.to_account_info(),
            authority: self.seller.to_account_info(),
        };
        CpiContext::new(self.token_program.to_account_info(), c)
    }
}

#[derive(Accounts)]
pub struct InitPlatform<'info> {
    #[account(mut)]
    pub payer: Signer<'info>,

    #[account(
        init,
        payer = payer,
        space = 8 + Platform::LEN,
        seeds = [b"platform"],
        bump,
    )]
    pub platform: Account<'info, Platform>,

    pub system_program: Program<'info, anchor_lang::system_program::System>,
}

#[derive(Accounts)]
pub struct ClaimCreatorFees<'info> {
    /// Platform authority must approve claims
    pub platform_authority: Signer<'info>,

    #[account(
        seeds = [b"platform"],
        bump = platform.bump,
    )]
    pub platform: Account<'info, Platform>,

    #[account(
        mut,
        seeds = [b"memecoin", memecoin.seed.as_ref()],
        bump = memecoin.bump,
    )]
    pub memecoin: Account<'info, Memecoin>,

    #[account(mut, constraint = base_mint.key() == memecoin.base_mint)]
    pub base_mint: Account<'info, Mint>,

    #[account(mut, constraint = creator_fee_vault.key() == memecoin.creator_fee_vault)]
    pub creator_fee_vault: Account<'info, TokenAccount>,

    /// Destination ATA for base mint (can belong to real creator)
    #[account(mut)]
    pub destination: Account<'info, TokenAccount>,

    pub token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct ClaimPlatformFees<'info> {
    /// Platform authority must approve claims
    pub platform_authority: Signer<'info>,

    #[account(
        seeds = [b"platform"],
        bump = platform.bump,
    )]
    pub platform: Account<'info, Platform>,

    #[account(mut)]
    pub base_mint: Account<'info, Mint>,
    #[account(
        mut,
        associated_token::mint = base_mint,
        associated_token::authority = platform,
    )]
    pub platform_fee_vault: Account<'info, TokenAccount>,

    /// Destination ATA for base mint (can belong to platform treasury)
    #[account(mut)]
    pub destination: Account<'info, TokenAccount>,

    pub token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct FinalizeDisableCurve<'info> {
    /// Anyone can trigger once threshold reached
    pub caller: Signer<'info>,

    #[account(
        mut,
        seeds = [b"memecoin", memecoin.seed.as_ref()],
        bump = memecoin.bump,
    )]
    pub memecoin: Account<'info, Memecoin>,

    #[account(constraint = base_mint.key() == memecoin.base_mint)]
    pub base_mint: Account<'info, Mint>,

    #[account(mut, constraint = reserve_vault.key() == memecoin.reserve_vault)]
    pub reserve_vault: Account<'info, TokenAccount>,

    #[account(seeds = [b"liquidity_defaults", base_mint.key().as_ref()], bump = liquidity_defaults.bump)]
    pub liquidity_defaults: Account<'info, LiquidityDefaults>,
}

#[derive(Accounts)]
pub struct RevokeMintAuthorities<'info> {
    /// Platform authority or creator must sign for this action
    pub any_signer: Signer<'info>,

    #[account(
        seeds = [b"platform"],
        bump = platform.bump,
    )]
    pub platform: Account<'info, Platform>,

    #[account(
        mut,
        seeds = [b"memecoin", memecoin.seed.as_ref()],
        bump = memecoin.bump,
        constraint = any_signer.key() == memecoin.creator || any_signer.key() == platform.authority @ CurveError::Unauthorized,
    )]
    pub memecoin: Account<'info, Memecoin>,

    #[account(mut, constraint = memecoin_mint.key() == memecoin.memecoin_mint)]
    pub memecoin_mint: Account<'info, Mint>,

    pub token_program: Program<'info, Token>,
}

// Removed per-memecoin init/update liquidity config accounts.

#[derive(Accounts)]
pub struct InitLiquidityDefaults<'info> {
    /// Payer for the defaults account
    #[account(mut)]
    pub payer: Signer<'info>,

    /// Platform authority must approve
    pub platform_authority: Signer<'info>,

    #[account(
        seeds = [b"platform"],
        bump = platform.bump,
    )]
    pub platform: Account<'info, Platform>,

    /// Base currency mint for which defaults apply
    pub base_mint: Account<'info, Mint>,

    /// Destination account for base mint where excess will be sent by default
    /// Can be a DEX/router vault ATA or a treasury.
    pub destination: Account<'info, TokenAccount>,

    #[account(
        init,
        payer = payer,
        space = 8 + LiquidityDefaults::LEN,
        seeds = [b"liquidity_defaults", base_mint.key().as_ref()],
        bump,
    )]
    pub liquidity_defaults: Account<'info, LiquidityDefaults>,

    pub system_program: Program<'info, anchor_lang::system_program::System>,
}

#[derive(Accounts)]
pub struct UpdateLiquidityDefaults<'info> {
    /// Platform authority must approve
    pub platform_authority: Signer<'info>,

    #[account(
        seeds = [b"platform"],
        bump = platform.bump,
    )]
    pub platform: Account<'info, Platform>,

    /// Base mint for which defaults are updated; must match the stored base mint
    pub base_mint: Account<'info, Mint>,

    /// New destination for base mint
    #[account(mut)]
    pub destination: Account<'info, TokenAccount>,

    #[account(
        mut,
        seeds = [b"liquidity_defaults", base_mint.key().as_ref()],
        bump = liquidity_defaults.bump,
    )]
    pub liquidity_defaults: Account<'info, LiquidityDefaults>,
}

#[derive(Accounts)]
pub struct SweepExcess<'info> {
    /// Anyone can trigger
    pub caller: Signer<'info>,

    #[account(
        seeds = [b"memecoin", memecoin.seed.as_ref()],
        bump = memecoin.bump,
    )]
    pub memecoin: Account<'info, Memecoin>,

    #[account(constraint = base_mint.key() == memecoin.base_mint)]
    pub base_mint: Account<'info, Mint>,

    #[account(mut, constraint = reserve_vault.key() == memecoin.reserve_vault)]
    pub reserve_vault: Account<'info, TokenAccount>,

    /// Destination ATA for base mint (must match config)
    #[account(
        mut,
        constraint = destination.mint == base_mint.key(),
        constraint = destination.key() == liquidity_defaults.destination,
    )]
    pub destination: Account<'info, TokenAccount>,

    #[account(seeds = [b"liquidity_defaults", base_mint.key().as_ref()], bump = liquidity_defaults.bump)]
    pub liquidity_defaults: Account<'info, LiquidityDefaults>,

    pub token_program: Program<'info, Token>,
}

#[derive(Accounts)]
pub struct WithdrawFinalizedReserve<'info> {
    /// Only the original creator can withdraw remaining reserve post-finalize
    pub creator: Signer<'info>,

    #[account(
        seeds = [b"memecoin", memecoin.seed.as_ref()],
        bump = memecoin.bump,
    )]
    pub memecoin: Account<'info, Memecoin>,

    #[account(constraint = base_mint.key() == memecoin.base_mint)]
    pub base_mint: Account<'info, Mint>,

    #[account(mut, constraint = reserve_vault.key() == memecoin.reserve_vault)]
    pub reserve_vault: Account<'info, TokenAccount>,

    /// Creator's ATA for the base mint (receives the withdrawn funds)
    #[account(mut)]
    pub destination: Account<'info, TokenAccount>,

    pub token_program: Program<'info, Token>,
}

/* -------------------- Errors -------------------- */

#[error_code]
pub enum CurveError {
    #[msg("Invalid parameter")] 
    InvalidParam,
    #[msg("Invalid amount")] 
    InvalidAmount,
    #[msg("Invalid campaign")] 
    InvalidCampaign,
    #[msg("Math overflow")] 
    MathOverflow,
    #[msg("Insufficient buyer funds")] 
    InsufficientFunds,
    #[msg("Insufficient reserve funds")] 
    InsufficientReserve,
    #[msg("Insufficient fee vault balance")]
    InsufficientFeeVault,
    #[msg("Unauthorized")] 
    Unauthorized,
    #[msg("Invalid state")]
    InvalidState,
}

/* -------------------- Helpers -------------------- */

/// Linear curve integral over [s, s+d]:
/// cost = ∫(a + b*x) dx from s to s+d = a*d + b*(s*d + d^2/2)
fn linear_integral_cost(a: u128, b: u128, s: u128, d: u128) -> Result<u128> {
    let ad = a
        .checked_mul(d)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let sd = s
        .checked_mul(d)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let d2 = d
        .checked_mul(d)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let half = d2
        .checked_div(2)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let inner = sd
        .checked_add(half)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let bterm = b
        .checked_mul(inner)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    ad.checked_add(bterm)
        .ok_or_else(|| error!(CurveError::MathOverflow))
}

/// Linear curve integral over [s, s+d], accounting for memecoin decimals.
/// Supply `s` and delta `d` are in memecoin base units (mint smallest units).
/// The intended model is price(S) = a + b*S where S is in whole memecoins.
/// Converting to base units (q = S * 10^m), the integral becomes:
///   cost = (a*d)/10^m + b*(s*d + d^2/2)/10^(2m)
fn u128_to_u64_checked(v: u128) -> Result<u64> {
    if v > (u64::MAX as u128) {
        return Err(error!(CurveError::InvalidAmount));
    }
    Ok(v as u64)
}

fn linear_integral_cost_scaled(
    a: u128,
    b: u128,
    s: u128,
    d: u128,
    decimals: u8,
) -> Result<u128> {
    // Base arithmetic in whole memecoins (scaled):
    // cost = (a*d)/10^m + b*(s*d + d^2/2)/10^(2m)
    let ad = a
        .checked_mul(d)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let sd = s
        .checked_mul(d)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let d2 = d
        .checked_mul(d)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let half = d2
        .checked_div(2)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let inner = sd
        .checked_add(half)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let bterm = b
        .checked_mul(inner)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;

    // scale by memecoin decimals: common denominator is 10^(2m)
    let m = decimals as u32;
    let scale1 = 10u128
        .checked_pow(m)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let scale2 = scale1
        .checked_mul(scale1)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;

    // Instead of truncating twice (ad/scale1 + bterm/scale2), combine into one
    // division with denominator scale2 to reduce rounding bias, but avoid
    // overflow by using remainders rather than scaling ad directly.
    let term_a = ad
        .checked_div(scale1)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let rem_a = ad
        .checked_rem(scale1)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let term_b = bterm
        .checked_div(scale2)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let rem_b = bterm
        .checked_rem(scale2)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;

    // fractional_sum = (rem_a/scale1) + (rem_b/scale2)
    // with common denominator scale2: (rem_a*scale1 + rem_b)/scale2
    let rem_a_scaled = rem_a
        .checked_mul(scale1)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let numer = rem_a_scaled
        .checked_add(rem_b)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;
    let extra = numer
        .checked_div(scale2)
        .ok_or_else(|| error!(CurveError::MathOverflow))?;

    term_a
        .checked_add(term_b)
        .ok_or_else(|| error!(CurveError::MathOverflow))?
        .checked_add(extra)
        .ok_or_else(|| error!(CurveError::MathOverflow))
}