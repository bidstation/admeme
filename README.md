# AdMeme - Solana Programs

Public repository for the **AdMeme** on-chain programs (Rust + Anchor). This repo is intentionally scoped to the programs only.

## Programs

| Program | Crate name | Path in this repo | Purpose |
| --- | --- | --- | --- |
| **a2m_campaign_vault** | `a2m_campaign_vault` | `./programs/a2m_campaign_vault/src/lib.rs` | Campaign vault + Merkle-based payouts for advertisers. |
| **collection_coin_curve_v2** | `collection_coin_curve_v2` | `./programs/collection_coin_curve_v2/src/lib.rs` | Per-collection token with a bonding curve (buy/sell) + fee escrow. |

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

## collection_coin_curve_v2

Creates per-collection SPL token mints governed by a **bonding curve**:

## Program IDs

Program IDs are declared in-source via `declare_id!()` and must be updated to match your deployments.

| Program | Program ID |
| --- | --- |
| `a2m_campaign_vault` | `2s7V6oGMGMY2ys9y9FHBKt9HPvxqCUK2DpXEWegWzA8G` |
| `collection_coin_curve_v2` | `FUAYEMXuFbmEyCu215fqH4G5Q2jSjQUBJvPPJJSQDMZj` |

## Building

These are Anchor programs (`anchor-lang` `0.32.1`).

- Build from an existing Anchor workspace (recommended): add the crates as workspace members and run `anchor build`.
- Or build each program with Solana's SBF toolchain:

```bash
# a2m_campaign_vault
cargo build-sbf --manifest-path ./Cargo.toml

# collection_coin_curve_v2
cargo build-sbf --manifest-path ./collection_coin_curve_v2/Cargo.toml
```

## Security

- These programs are provided as-is and have **not** been audited.
- Do not treat this repository as financial advice; review and test thoroughly before deploying.
