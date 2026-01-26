# AdMeme - Solana Programs

Public repository for the **AdMeme** on-chain programs (Rust + Anchor). This repo is intentionally scoped to the programs only.

## Programs

| Program | Crate name | Path in this repo | Purpose |
| --- | --- | --- | --- |
| **a2m_campaign_vault** | `a2m_campaign_vault` | `./programs/a2m_campaign_vault/src/lib.rs` | Campaign vault + Merkle-based payouts for advertisers. |
| **memecoin_curve** | `memecoin_curve` | `./programs/memecoin-curve/src/lib.rs` | Per-meme token with a linear bonding curve (buy/sell) + fee escrow and optional reserve management. |

## a2m_campaign_vault

Campaign vault that holds an advertiser-funded SPL token balance and pays recipients using a Merkle root published at campaign finalization time.

**Core instructions**
- `init_platform(authority)` - initializes the singleton platform config PDA (sets authority).
- `init_campaign(campaign_id, advertiser_deposit_amount)` - creates a campaign PDA and its vault ATA; optionally transfers an initial deposit into the vault.
- `finalize_campaign(claims_root, claims_leaf_count, ap_total_payout)` - locks the campaign, creates the claims registry, and sets the payout cap (requires vault balance >= `ap_total_payout`).
- `claim(email_hash, amount, index, proof)` - pays a claim from the vault after Merkle proof verification; requires platform authority co-sign.

**Key PDAs / accounts**
- `platform`: seeds `["platform"]`
- `campaign`: seeds `["campaign", advertiser_pubkey, campaign_id_le_bytes]`
- `vault`: associated token account for `mint`, authority = `campaign`
- `claims`: seeds `["claims", campaign_pubkey]` (stores Merkle root + claimed bitmap)

**Merkle leaf format**
- `leaf = H("A2M_CLAIM" || campaign_pubkey || email_hash || amount_le || index_le)` using Solana `hashv`

## memecoin_curve

Creates per-meme SPL token mints governed by a **linear bonding curve**:

- Price model: `p(s) = a + b*s`
- Buy: pay the integral cost over `[s, s + amount_out]` plus a creator fee
- Sell: burn tokens and receive the integral refund over `[s - amount_in, s]` net of fee
- Slippage protection: buyers pass `max_total`; sellers pass `min_refund`

**Core flow**
1. `create_memecoin(seed, a, b, fee_bps, decimals)` - creates `Memecoin` PDA state, initializes the memecoin mint (temporary mint authority = creator), and creates vaults.
2. (Optional) create Metaplex metadata while the creator is mint authority.
3. `handoff_mint_authority()` - transfers mint authority to the `Memecoin` PDA so curve buys can mint.
4. Trading: `buy_memecoin(amount_out, max_total)` / `sell_memecoin(amount_in, min_refund)`.

**Fees**
- `fee_bps` is in basis points (`0..=10_000`).
- Buy fees are transferred into `creator_fee_vault`.
- Sell fees are transferred from `reserve_vault` into `creator_fee_vault`.
- `claim_creator_fees(amount)` moves funds from `creator_fee_vault` to a destination token account, gated by the platform authority.

**Reserve management (optional)**
- Global per-`base_mint` configuration via `init_liquidity_defaults(...)` / `update_liquidity_defaults(...)`.
- `sweep_excess()` can move excess base tokens from `reserve_vault` to a configured destination when enabled.
- `finalize_disable_curve()` permanently disables curve trading once the reserve reaches the configured threshold.
- After finalization: `revoke_mint_authorities()` (creator or platform) and `withdraw_finalized_reserve()` (creator).

**Key PDAs / accounts**
- `memecoin`: seeds `["memecoin", seed]`
- `platform`: seeds `["platform"]`
- `liquidity_defaults`: seeds `["liquidity_defaults", base_mint_pubkey]`
- `reserve_vault`: associated token account for `base_mint`, authority = `memecoin`
- `creator_fee_vault`: seeds `["creator_fee_vault", seed]` (SPL token account for `base_mint`, authority = `memecoin`)

## Program IDs

Program IDs are declared in-source via `declare_id!()` and must be updated to match your deployments.

| Program | Program ID |
| --- | --- |
| `a2m_campaign_vault` | `2s7V6oGMGMY2ys9y9FHBKt9HPvxqCUK2DpXEWegWzA8G` |
| `memecoin_curve` | `BKWVgcPdNvYXUVBzfy17RDtSy7nvyxudUEF2yK34EYvu` |

## Building

These are Anchor programs (`anchor-lang` `0.32.1`).

- Build from an existing Anchor workspace (recommended): add the crates as workspace members and run `anchor build`.
- Or build each program with Solana's SBF toolchain:

```bash
# a2m_campaign_vault
cargo build-sbf --manifest-path ./Cargo.toml

# memecoin_curve
cargo build-sbf --manifest-path ./memecoin-curve/Cargo.toml
```

## Security

- These programs are provided as-is and have **not** been audited.
- Do not treat this repository as financial advice; review and test thoroughly before deploying.
