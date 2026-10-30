# Public library maintenance audit

Audit date: 2026-10-30. Source baseline: `89f1ef67440aed605b91964d655fdbcf41e20d78`.

| Item | Scope and result |
|---|---|
| Product | Standalone real-analysis library; no accompanying paper or SPDE construction |
| Proof source | Four mathematical modules, unchanged from v0.1.0 |
| Pins | Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; exact transitive manifest |
| Claims | 41 registered; 26 reusable statements compared; 15 supporting/experimental claims are not promoted |
| Original evidence | Source `158e8431c1db`, lean-pkg 0.20.0; retained unchanged |
| Current evidence | Refresh in progress; terminal results will be linked here only after acceptance |
| Documentation | Seven result cards, hypotheses and exclusions; primary reference locations and differences in `docs/reference-audit.json` |
| Hosting | Pages deployment enabled; repository instructions prohibit Lean Actions workflows |
| Attribution | Apache-2.0, NOTICE, CITATION.cff, lean-pkg credit and AI disclosure present |
| Release | Existing v0.1.0 and its DOI preserved; no new tag or DOI from this maintenance update |
| Significance | No novelty, paper certification or human review claimed |

The source and exact Lean types decide the claim. A checker inventory includes generated/private helpers and is not an authored-theorem total. Imported dependency artifacts and the compiler remain trusted inputs.
