# Public library maintenance audit

Audit date: 2026-10-30. Source baseline: `89f1ef67440aed605b91964d655fdbcf41e20d78`.

| Item | Scope and result |
|---|---|
| Product | Standalone real-analysis library; no accompanying paper or SPDE construction |
| Proof source | Four mathematical modules, unchanged from v0.1.0 |
| Pins | Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; exact transitive manifest |
| Claims | 41 registered; 26 reusable statements compared; 15 supporting/experimental claims are not promoted |
| Original evidence | Source `158e8431c1db`, lean-pkg 0.20.0; retained unchanged |
| Current evidence | Current lean-pkg 0.23.0 native and separate same-host fresh owned-source replay PASS at `6892571`; all 26 official Comparator slots PASS; complete 134-owned records match byte for byte |
| Documentation | Seven result cards, hypotheses and exclusions; primary reference locations and differences in `docs/reference-audit.json` |
| Hosting | Pages deployment enabled; repository instructions prohibit repository-defined GitHub Actions workflows |
| Attribution | Apache-2.0, NOTICE, CITATION.cff, lean-pkg credit and AI disclosure present |
| Release | Existing v0.1.0 and its DOI preserved; no new tag or DOI from this maintenance update |
| Significance | No novelty, paper certification or human review claimed |

The source and exact Lean types decide the claim. A checker inventory includes generated/private helpers and is not an authored-theorem total. Imported dependency artifacts and the compiler remain trusted inputs.

## Accepted maintenance scope

Scientific source and checker checkpoint: `689257126d3859efba8a38076353c9570d1fe1f1`. The four mathematical modules, original Challenge/Solution, claims and all dependency revisions remain unchanged. The manifest root package name is corrected; this is not a dependency upgrade. The exact [checkpoint evidence](.lean-receipts/689257126d38-gold/README.md) includes the full lossless owned corpus, native/replay identities, 18 parser mutations, eight API controls per phase and actual two-hop forbidden-axiom fixtures.

Two cold AI reviews found required defects in earlier snapshots. Their original FAIL/medium and FAIL/high reports are preserved. The first policy repair was checked in the focused successor; the second required one-line synthetic recursor fixture repair is exercised by both terminal full verification chains. No later model PASS or human approval is claimed. Original statement/reference checks are reused at unchanged statement bytes.

The compiler and pinned imported compiled dependencies remain trusted; separate same-host execution is not an independent compiler or a full Mathlib source rebuild. The 15 experimental/supporting registered claims are axiom-checked, not Comparator-promoted. The inspector alone does not prove fresh compilation; the enclosing receipts do. Discovery mode is diagnostic rather than a certificate and can refuse after writing a changed candidate roster; use the frozen strict mode for acceptance. API error expectations pin complete fixture bytes and error headers, not full diagnostic formatting.

This is a verified maintenance candidate for review. The public default branch and deployed Pages are updated only after the owner merges its pull request; their earlier evidence remains authoritative until then.
