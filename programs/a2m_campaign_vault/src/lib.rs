use anchor_lang::prelude::*;
use anchor_spl::associated_token::AssociatedToken;
use anchor_spl::token::{self, Mint, Token, TokenAccount, Transfer};
use solana_sha256_hasher::hashv;

declare_id!("2s7V6oGMGMY2ys9y9FHBKt9HPvxqCUK2DpXEWegWzA8G");

// ---- Campaign pricing / fee config (hardcoded on-chain) ----
// 3% platform fee, taken upfront from advertiser deposits. Non-refundable.
const PLATFORM_FEE_BPS: u16 = 300;
// Allowed campaign mint (mainnet)
const A2M_MINT: Pubkey = Pubkey::new_from_array([
    159, 225, 109, 36, 121, 224, 103, 249, 55, 248, 48, 63, 243, 61, 85, 239,
    165, 118, 169, 247, 32, 26, 100, 112, 88, 16, 215, 48, 197, 158, 140, 20,
]);
// Claims registry rent grows linearly with the number of leaves because each leaf
// consumes one bit in the claimed bitmap. Keep the PDA size bounded.
const MAX_CLAIMS_LEAF_COUNT: u32 = 10_000;

#[program]
pub mod a2m_campaign_vault {
    use super::*;

    /* -------------------- Platform init -------------------- */

    pub fn init_platform(ctx: Context<InitPlatform>, authority: Pubkey) -> Result<()> {
        ctx.accounts.platform.authority = authority;
        Ok(())
    }

    /* -------------------- Campaign lifecycle -------------------- */

    pub fn init_campaign(
        ctx: Context<InitCampaign>,
        campaign_id: u64,
        advertiser_deposit_amount: u64,
    ) -> Result<()> {
        // Restrict rounds to A2M only.
        let mint = ctx.accounts.mint.key();
        require!(mint == A2M_MINT, ErrCode::InvalidMint);

        // init state
        {
            let c = &mut ctx.accounts.campaign;
            c.advertiser = ctx.accounts.advertiser.key();
            c.mint = mint;
            c.status = Status::Open;
            c.vault_bump = ctx.bumps.campaign;
            c.advertiser_deposit = 0;
            c.ap_total_payout = 0;
            c.ap_total_claimed = 0;
            c.id = campaign_id;
        }

        let fee = if advertiser_deposit_amount > 0 {
            ((advertiser_deposit_amount as u128)
                .checked_mul(PLATFORM_FEE_BPS as u128)
                .ok_or(ErrCode::MathOverflow)?
                / 10_000u128) as u64
        } else {
            0
        };
        let net = advertiser_deposit_amount
            .checked_sub(fee)
            .ok_or(ErrCode::MathOverflow)?;

        // optional initial advertiser funding
        if advertiser_deposit_amount > 0 {
            // Transfer fee to platform fee vault (ATA owned by platform PDA)
            if fee > 0 {
                token::transfer(
                    ctx.accounts.transfer_from_advertiser_to_platform_fee_vault(),
                    fee,
                )?;
            }
            // Transfer net to campaign vault (ATA owned by campaign PDA)
            if net > 0 {
                token::transfer(
                    ctx.accounts.transfer_from_advertiser_to_vault(),
                    net,
                )?;
            }
            // Record gross deposit for off-chain impressions math
            ctx.accounts.campaign.advertiser_deposit = advertiser_deposit_amount;
        }

        emit!(CampaignInitialized {
            campaign: ctx.accounts.campaign.key(),
            campaign_id,
            advertiser: ctx.accounts.advertiser.key(),
            mint,
            gross_deposit: advertiser_deposit_amount,
            fee,
            net_deposit: net,
        });

        Ok(())
    }

    /* -------------------- Platform fee withdrawal -------------------- */

    pub fn withdraw_fees(ctx: Context<WithdrawFees>, amount: u64) -> Result<()> {
        // Only platform authority may withdraw fees
        require_keys_eq!(
            ctx.accounts.platform_signer.key(),
            ctx.accounts.platform.authority,
            ErrCode::NotAuthorized
        );
        require!(amount > 0, ErrCode::InvalidAmount);
        require!(ctx.accounts.platform_fee_vault.amount >= amount, ErrCode::InsufficientVault);

        let bump = ctx.bumps.platform;
        let seeds: &[&[u8]] = &[b"platform", &[bump]];
        token::transfer(
            ctx.accounts
                .transfer_from_fee_vault_to_recipient()
                .with_signer(&[seeds]),
            amount,
        )?;

        emit!(FeesWithdrawn {
            mint: ctx.accounts.mint.key(),
            recipient: ctx.accounts.recipient.key(),
            amount,
        });

        Ok(())
    }

    /* -------------------- Finalize with a single Merkle registry -------------------- */
    pub fn finalize_campaign(
        ctx: Context<Finalize>,
        claims_root: [u8; 32],
        claims_leaf_count: u32,
        ap_total_payout: u64,   // cap for advertiser-pool payouts
    ) -> Result<()> {
        // ---- Auth: platform only ----
        require_keys_eq!(
            ctx.accounts
                .platform_signer
                .as_ref()
                .ok_or(ErrCode::NotAuthorized)?
                .key(),
            ctx.accounts.platform.authority,
            ErrCode::NotAuthorized
        );

        // ---- Campaign must be open ----
        let c = &mut ctx.accounts.campaign;
        require!(c.status == Status::Open, ErrCode::AlreadyFinalized);

        // ---- Vault must cover payout cap ----
        let needed = ap_total_payout;
        require!(ctx.accounts.vault.amount >= needed, ErrCode::InsufficientVault);
        require!(claims_leaf_count <= MAX_CLAIMS_LEAF_COUNT, ErrCode::TooManyClaims);

        // ---- Initialize the claims registry ----
        {
            let reg = &mut ctx.accounts.claims;
            reg.campaign = c.key();
            reg.root = claims_root;
            reg.leaf_count = claims_leaf_count;
            let bitmap_len = ((claims_leaf_count as usize) + 7) / 8;
            reg.claimed_bitmap = vec![0u8; bitmap_len];
        }
        // Record caps & lock campaign
        c.ap_total_payout = ap_total_payout;
        c.status = Status::Finalized;

        emit!(CampaignFinalized {
            campaign: c.key(),
            claims_root,
            claims_leaf_count,
            ap_total_payout,
        });

        Ok(())
    }

    pub fn claim_email_v2(
        ctx: Context<Claim>,
        email_hash: [u8; 32],
        wallet_pubkey: Pubkey,
        amount: u64,
        index: u32,
        proof: Vec<[u8; 32]>,
    ) -> Result<()> {
        // Platform co-sign is the strict fallback path for email-only v2 claims.
        require_keys_eq!(
            ctx.accounts.platform_signer.key(),
            ctx.accounts.platform.authority,
            ErrCode::NotAuthorized
        );
        require!(
            wallet_pubkey == Pubkey::default(),
            ErrCode::WalletBoundClaimRequiresWalletSigner
        );

        let campaign = ctx.accounts.campaign.key();
        let recipient = ctx.accounts.recipient.key();
        let mut ap_total_claimed = 0u64;

        {
            let c_ro = &ctx.accounts.campaign;
            require!(c_ro.status == Status::Finalized, ErrCode::NotFinalized);

            let reg_ro = &ctx.accounts.claims;
            require_keys_eq!(reg_ro.campaign, c_ro.key(), ErrCode::InvalidRegistry);
            require!((index as u64) < (reg_ro.leaf_count as u64), ErrCode::IndexOutOfBounds);
            require!(!bitmap_get(&reg_ro.claimed_bitmap, index), ErrCode::AlreadyClaimed);

            let leaf = hash_leaf_v2(
                b"A2M_CLAIM_V2",
                &c_ro.key(),
                &email_hash,
                &wallet_pubkey,
                amount,
                index,
            );
            require!(verify_merkle(leaf, &proof, index, &reg_ro.root), ErrCode::InvalidMerkleProof);

            let new_claimed = c_ro.ap_total_claimed.checked_add(amount).ok_or(ErrCode::MathOverflow)?;
            require!(new_claimed <= c_ro.ap_total_payout, ErrCode::PayoutExceeded);

            let adv = c_ro.advertiser;
            let id_bytes = c_ro.id.to_le_bytes();
            let bump = c_ro.vault_bump;
            let seeds: &[&[u8]] = &[b"campaign", adv.as_ref(), &id_bytes, &[bump]];
            token::transfer(
                ctx.accounts
                    .transfer_from_vault_to_recipient()
                    .with_signer(&[seeds]),
                amount,
            )?;

            {
                let reg = &mut ctx.accounts.claims;
                bitmap_set(&mut reg.claimed_bitmap, index);
            }
            {
                let c = &mut ctx.accounts.campaign;
                c.ap_total_claimed = new_claimed;
            }
            ap_total_claimed = new_claimed;
        }

        emit!(ClaimSettled {
            campaign,
            index,
            amount,
            recipient,
            claim_kind: ClaimKind::EmailV2,
            ap_total_claimed,
        });

        Ok(())
    }

    pub fn claim_wallet(
        ctx: Context<ClaimWallet>,
        email_hash: [u8; 32],
        amount: u64,
        index: u32,
        proof: Vec<[u8; 32]>,
    ) -> Result<()> {
        let campaign = ctx.accounts.campaign.key();
        let recipient = ctx.accounts.claimant.key();
        let mut ap_total_claimed = 0u64;

        {
            let c_ro = &ctx.accounts.campaign;
            require!(c_ro.status == Status::Finalized, ErrCode::NotFinalized);

            let reg_ro = &ctx.accounts.claims;
            require_keys_eq!(reg_ro.campaign, c_ro.key(), ErrCode::InvalidRegistry);
            require!((index as u64) < (reg_ro.leaf_count as u64), ErrCode::IndexOutOfBounds);
            require!(!bitmap_get(&reg_ro.claimed_bitmap, index), ErrCode::AlreadyClaimed);

            let claimant = ctx.accounts.claimant.key();
            require!(
                claimant != Pubkey::default(),
                ErrCode::WalletBoundClaimRequiresWalletSigner
            );
            let leaf = hash_leaf_v2(
                b"A2M_CLAIM_V2",
                &c_ro.key(),
                &email_hash,
                &claimant,
                amount,
                index,
            );
            require!(verify_merkle(leaf, &proof, index, &reg_ro.root), ErrCode::InvalidMerkleProof);

            let new_claimed = c_ro.ap_total_claimed.checked_add(amount).ok_or(ErrCode::MathOverflow)?;
            require!(new_claimed <= c_ro.ap_total_payout, ErrCode::PayoutExceeded);

            let adv = c_ro.advertiser;
            let id_bytes = c_ro.id.to_le_bytes();
            let bump = c_ro.vault_bump;
            let seeds: &[&[u8]] = &[b"campaign", adv.as_ref(), &id_bytes, &[bump]];
            token::transfer(
                ctx.accounts
                    .transfer_from_vault_to_claimant()
                    .with_signer(&[seeds]),
                amount,
            )?;

            {
                let reg = &mut ctx.accounts.claims;
                bitmap_set(&mut reg.claimed_bitmap, index);
            }
            {
                let c = &mut ctx.accounts.campaign;
                c.ap_total_claimed = new_claimed;
            }
            ap_total_claimed = new_claimed;
        }

        emit!(ClaimSettled {
            campaign,
            index,
            amount,
            recipient,
            claim_kind: ClaimKind::WalletV2,
            ap_total_claimed,
        });

        Ok(())
    }

}

/* ------------ State ------------ */

#[account]
pub struct PlatformConfig {
    pub authority: Pubkey,
}
impl PlatformConfig {
    pub const SIZE: usize = 8 + 32;
}

#[account]
pub struct Campaign {
    pub advertiser: Pubkey,
    pub mint: Pubkey,
    pub status: Status,     // 1 byte
    pub vault_bump: u8,     // 1 byte

    // Split accounting
    pub advertiser_deposit: u64, // how much advertiser deposited
    // Advertiser pool (AP) claims cap + tally
    pub ap_total_payout: u64,
    pub ap_total_claimed: u64,

    pub id: u64,
}
impl Campaign {
    // discriminator + pks + status+bump + (advertiser_deposit + ap_total_payout + ap_total_claimed + id)
    pub const SIZE: usize = 8 + 32 + 32 + 1 + 1 + 8 + 8 + 8 + 8;
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Open,
    Finalized,
}

#[derive(AnchorSerialize, AnchorDeserialize, Clone, Copy, PartialEq, Eq)]
pub enum ClaimKind {
    EmailV2,
    WalletV2,
}

/// Registry used for advertiser pool payouts
#[account]
pub struct ClaimsRegistry {
    pub campaign: Pubkey,
    pub root: [u8; 32],
    pub leaf_count: u32,
    pub claimed_bitmap: Vec<u8>,
}
impl ClaimsRegistry {
    pub fn space(leaf_count: u32) -> usize {
        let capped_leaf_count = core::cmp::min(leaf_count, MAX_CLAIMS_LEAF_COUNT) as usize;
        let bitmap_len = (capped_leaf_count + 7) / 8;
        8 + 32 + 32 + 4 + 4 + bitmap_len
    }
}

// (Booster claims registry removed)

/* ------------ Accounts ------------ */

#[derive(Accounts)]
pub struct InitPlatform<'info> {
    #[account(
        init,
        payer = payer,
        seeds = [b"platform"],
        bump,
        space = PlatformConfig::SIZE
    )]
    pub platform: Account<'info, PlatformConfig>,
    #[account(mut)]
    pub payer: Signer<'info>,
    pub system_program: Program<'info, anchor_lang::system_program::System>,
}

#[derive(Accounts)]
#[instruction(campaign_id: u64)]
pub struct InitCampaign<'info> {
    #[account(mut)]
    pub advertiser: Signer<'info>,
    #[account(
        mut,
        constraint = advertiser_ata.mint == mint.key(),
        constraint = advertiser_ata.owner == advertiser.key()
    )]
    pub advertiser_ata: Account<'info, TokenAccount>,
    pub mint: Account<'info, Mint>,

    #[account(seeds = [b"platform"], bump)]
    pub platform: Account<'info, PlatformConfig>,
    #[account(
        init_if_needed,
        payer = advertiser,
        associated_token::mint = mint,
        associated_token::authority = platform
    )]
    pub platform_fee_vault: Account<'info, TokenAccount>,

    #[account(
        init,
        payer = advertiser,
        seeds = [b"campaign", advertiser.key().as_ref(), &campaign_id.to_le_bytes()],
        bump,
        space = Campaign::SIZE
    )]
    pub campaign: Account<'info, Campaign>,

    #[account(
        init,
        payer = advertiser,
        associated_token::mint = mint,
        associated_token::authority = campaign
    )]
    pub vault: Account<'info, TokenAccount>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, anchor_lang::system_program::System>,
}
impl<'info> InitCampaign<'info> {
    fn transfer_from_advertiser_to_vault(
        &self,
    ) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let c = Transfer {
            from: self.advertiser_ata.to_account_info(),
            to: self.vault.to_account_info(),
            authority: self.advertiser.to_account_info(),
        };
        CpiContext::new(self.token_program.to_account_info(), c)
    }

    fn transfer_from_advertiser_to_platform_fee_vault(
        &self,
    ) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let c = Transfer {
            from: self.advertiser_ata.to_account_info(),
            to: self.platform_fee_vault.to_account_info(),
            authority: self.advertiser.to_account_info(),
        };
        CpiContext::new(self.token_program.to_account_info(), c)
    }
}

// (BoostMeme instruction/accounts removed)

/* ------ Finalize with single registry ------ */

#[derive(Accounts)]
#[instruction(
    claims_root: [u8;32],
    claims_leaf_count: u32,
    ap_total_payout: u64
)]
pub struct Finalize<'info> {
    // Kept optional for account-layout compatibility, but finalize requires the
    // platform signer at runtime.
    #[account(mut)]
    pub advertiser: Option<Signer<'info>>,
    #[account(mut)]
    pub platform_signer: Option<Signer<'info>>,
    #[account(seeds = [b"platform"], bump)]
    pub platform: Account<'info, PlatformConfig>,

    pub mint: Account<'info, Mint>,
    #[account(
        mut,
        seeds = [b"campaign", campaign.advertiser.as_ref(), &campaign.id.to_le_bytes()],
        bump = campaign.vault_bump,
        constraint = campaign.mint == mint.key(),
    )]
    pub campaign: Account<'info, Campaign>,

    #[account(
        mut,
        constraint = vault.owner == campaign.key(),
        constraint = vault.mint == mint.key(),
    )]
    pub vault: Account<'info, TokenAccount>,

    // AP registry
    #[account(
        init,
        payer = payer,
        seeds = [b"claims", campaign.key().as_ref()],
        bump,
        space = ClaimsRegistry::space(claims_leaf_count)
    )]
    pub claims: Account<'info, ClaimsRegistry>,

    /// Payer for the registry allocations
    #[account(mut)]
    pub payer: Signer<'info>,

    pub system_program: Program<'info, anchor_lang::system_program::System>,
}

/* ------ Claim from advertiser pool ------ */

#[derive(Accounts)]
pub struct Claim<'info> {
    pub platform_signer: Signer<'info>,
    #[account(seeds = [b"platform"], bump)]
    pub platform: Account<'info, PlatformConfig>,

    /// CHECK: Recipient wallet (or PDA). Safety: the ATA is constrained via
    /// `associated_token::authority = recipient` and `associated_token::mint = mint`.
    pub recipient: UncheckedAccount<'info>,
    #[account(
        init_if_needed,
        payer = fee_payer,
        associated_token::mint = mint,
        associated_token::authority = recipient
    )]
    pub recipient_ata: Account<'info, TokenAccount>,

    pub mint: Account<'info, Mint>,
    #[account(
        mut,
        seeds = [b"campaign", campaign.advertiser.as_ref(), &campaign.id.to_le_bytes()],
        bump = campaign.vault_bump,
        constraint = campaign.mint == mint.key(),
    )]
    pub campaign: Account<'info, Campaign>,

    #[account(
        mut,
        constraint = vault.owner == campaign.key(),
        constraint = vault.mint == mint.key(),
    )]
    pub vault: Account<'info, TokenAccount>,

    #[account(
        mut,
        seeds = [b"claims", campaign.key().as_ref()],
        bump,
        constraint = claims.campaign == campaign.key()
    )]
    pub claims: Account<'info, ClaimsRegistry>,

    #[account(mut)]
    pub fee_payer: Signer<'info>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, anchor_lang::system_program::System>,
}
impl<'info> Claim<'info> {
    fn transfer_from_vault_to_recipient(
        &self,
    ) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let c = Transfer {
            from: self.vault.to_account_info(),
            to: self.recipient_ata.to_account_info(),
            authority: self.campaign.to_account_info(),
        };
        CpiContext::new(self.token_program.to_account_info(), c)
    }
}

#[derive(Accounts)]
pub struct ClaimWallet<'info> {
    #[account(mut)]
    pub claimant: Signer<'info>,
    #[account(
        init_if_needed,
        payer = claimant,
        associated_token::mint = mint,
        associated_token::authority = claimant
    )]
    pub claimant_ata: Account<'info, TokenAccount>,

    pub mint: Account<'info, Mint>,
    #[account(
        mut,
        seeds = [b"campaign", campaign.advertiser.as_ref(), &campaign.id.to_le_bytes()],
        bump = campaign.vault_bump,
        constraint = campaign.mint == mint.key(),
    )]
    pub campaign: Account<'info, Campaign>,

    #[account(
        mut,
        constraint = vault.owner == campaign.key(),
        constraint = vault.mint == mint.key(),
    )]
    pub vault: Account<'info, TokenAccount>,

    #[account(
        mut,
        seeds = [b"claims", campaign.key().as_ref()],
        bump,
        constraint = claims.campaign == campaign.key()
    )]
    pub claims: Account<'info, ClaimsRegistry>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, anchor_lang::system_program::System>,
}
impl<'info> ClaimWallet<'info> {
    fn transfer_from_vault_to_claimant(
        &self,
    ) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let c = Transfer {
            from: self.vault.to_account_info(),
            to: self.claimant_ata.to_account_info(),
            authority: self.campaign.to_account_info(),
        };
        CpiContext::new(self.token_program.to_account_info(), c)
    }
}

/* ------ Withdraw platform fees ------ */

#[derive(Accounts)]
pub struct WithdrawFees<'info> {
    pub platform_signer: Signer<'info>,
    #[account(seeds = [b"platform"], bump)]
    pub platform: Account<'info, PlatformConfig>,

    /// CHECK: Recipient wallet (or PDA). Safety: the ATA is constrained via
    /// `associated_token::authority = recipient` and `associated_token::mint = mint`.
    pub recipient: UncheckedAccount<'info>,
    #[account(
        init_if_needed,
        payer = fee_payer,
        associated_token::mint = mint,
        associated_token::authority = recipient
    )]
    pub recipient_ata: Account<'info, TokenAccount>,

    pub mint: Account<'info, Mint>,
    #[account(
        mut,
        associated_token::mint = mint,
        associated_token::authority = platform
    )]
    pub platform_fee_vault: Account<'info, TokenAccount>,

    #[account(mut)]
    pub fee_payer: Signer<'info>,

    pub token_program: Program<'info, Token>,
    pub associated_token_program: Program<'info, AssociatedToken>,
    pub system_program: Program<'info, anchor_lang::system_program::System>,
}
impl<'info> WithdrawFees<'info> {
    fn transfer_from_fee_vault_to_recipient(
        &self,
    ) -> CpiContext<'_, '_, '_, 'info, Transfer<'info>> {
        let c = Transfer {
            from: self.platform_fee_vault.to_account_info(),
            to: self.recipient_ata.to_account_info(),
            authority: self.platform.to_account_info(),
        };
        CpiContext::new(self.token_program.to_account_info(), c)
    }
}

// (Booster claim instruction/accounts removed)

/* ------------ Events ------------ */

#[event]
pub struct CampaignInitialized {
    pub campaign: Pubkey,
    pub campaign_id: u64,
    pub advertiser: Pubkey,
    pub mint: Pubkey,
    pub gross_deposit: u64,
    pub fee: u64,
    pub net_deposit: u64,
}

#[event]
pub struct CampaignFinalized {
    pub campaign: Pubkey,
    pub claims_root: [u8; 32],
    pub claims_leaf_count: u32,
    pub ap_total_payout: u64,
}

#[event]
pub struct ClaimSettled {
    pub campaign: Pubkey,
    pub index: u32,
    pub amount: u64,
    pub recipient: Pubkey,
    pub claim_kind: ClaimKind,
    pub ap_total_claimed: u64,
}

#[event]
pub struct FeesWithdrawn {
    pub mint: Pubkey,
    pub recipient: Pubkey,
    pub amount: u64,
}

/* ------------ Errors ------------ */

#[error_code]
pub enum ErrCode {
    #[msg("Not authorized")]
    NotAuthorized,
    #[msg("Campaign already finalized")]
    AlreadyFinalized,
    #[msg("Campaign not finalized")]
    NotFinalized,
    #[msg("Insufficient vault balance")]
    InsufficientVault,
    #[msg("Already claimed")]
    AlreadyClaimed,
    #[msg("Payout exceeds cap")]
    PayoutExceeded,
    #[msg("Math overflow")]
    MathOverflow,
    #[msg("Invalid Merkle proof")]
    InvalidMerkleProof,
    #[msg("Index out of bounds")]
    IndexOutOfBounds,
    #[msg("Invalid claims registry")]
    InvalidRegistry,
    #[msg("Invalid amount")]
    InvalidAmount,
    #[msg("Invalid mint")]
    InvalidMint,
    #[msg("Too many claims in one registry")]
    TooManyClaims,
    #[msg("Wallet-bound claims must be claimed by the bound wallet signer")]
    WalletBoundClaimRequiresWalletSigner,
}

/* ------------ Helpers ------------ */

fn bitmap_get(bits: &[u8], idx: u32) -> bool {
    let i = (idx / 8) as usize;
    let b = (idx % 8) as u8;
    if i >= bits.len() { return false; }
    ((bits[i] >> b) & 1) == 1
}
fn bitmap_set(bits: &mut [u8], idx: u32) {
    let i = (idx / 8) as usize;
    let b = (idx % 8) as u8;
    if i < bits.len() {
        bits[i] |= 1u8 << b;
    }
}

fn hash_leaf_v2(
    domain: &[u8],
    campaign: &Pubkey,
    user_hash: &[u8; 32],
    wallet: &Pubkey,
    amount: u64,
    index: u32,
) -> [u8; 32] {
    let amt = amount.to_le_bytes();
    let idx = index.to_le_bytes();
    hashv(&[domain, campaign.as_ref(), user_hash, wallet.as_ref(), &amt, &idx]).to_bytes()
}

/// Indexed Merkle verification (right = odd, left = even).
fn verify_merkle(mut leaf: [u8;32], proof: &[[u8;32]], mut index: u32, root: &[u8;32]) -> bool {
    for sib in proof.iter() {
        let h = if (index & 1) == 0 {
            hashv(&[&leaf, sib]).to_bytes()
        } else {
            hashv(&[sib, &leaf]).to_bytes()
        };
        leaf = h;
        index >>= 1;
    }
    &leaf == root
}
