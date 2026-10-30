# Distribution and maintenance plan

The canonical public library is `chenle02/growth-rates-lean`; Pages provides the statement and verification guides. The v0.1.0 release is archived with its recorded Zenodo DOI. This maintenance branch does not create a release, move a tag, merge a pull request, submit to Palomar/Mathlib or post to Zulip.

Before another source release, check current stable Lean/Mathlib compatibility in isolation, preserve earlier receipts, run the complete local trust gate and separate owned-source replay, inspect every changed summary against the exported types, refresh the reference/coverage guides, and verify receipt binding and page freshness. Keep the no repository-defined GitHub Actions workflows policy unless the owner changes it.

Reservoir discovery depends on its current eligibility criteria and index; a public repository is not proof of indexing. Palomar readiness should be checked using lean-pkg's supported commands; submission and any Mathlib contribution require separate owner direction. Keep prose about classical related results separate from novelty claims.
