# Complete maintenance evidence

Accepted source/checker commit: `689257126d3859efba8a38076353c9570d1fe1f1`.

- The separate native and source-only owned replay completed with lean-pkg 0.23.0; distinct lower-tier receipts are adjacent to this directory. The full 26-slot Comparator receipt is also adjacent.
- `NATIVE-REPLAY-EQUALITY.json` records the complete 134-owned record equality: 2,014,823,225 decoded bytes per phase. This inventory contains 41 named claims and generated/private/helper/definition/inductive declarations; it is not 134 authored results.
- `MANIFEST.json` binds eight independently compressed parts. Every part was decompressed and rehashed. The complete type/body stream is retained without truncation; native/replay summaries retain their actual compiler objects and source/checker snapshots.
- `OWNED-ARCHIVE-BINDING.json` preserves the original component producer and the exact byte-equivalence bridge to both final accepted executions. The earlier component's later whole-gate failure remains a failure.
- Each phase supplies its eight API regression results, 18 reader mutations and actual positive/forbidden-transitive-axiom fixture source and transcript. API rejection is not a proof that every modified statement is false.
- Both original AI review reports and `REVIEW-DISPOSITION.json` preserve verdicts, confidence, scope and exact mechanical repair discharge. No model re-proof score replaces kernel evidence; no human sign-off is asserted.

To reconstruct the exact raw stream, run from this directory:

```sh
gzip -dc OWNED-STREAM.part-*.gz > owned-raw.log
sha256sum owned-raw.log
```

Compare that digest and decoded size with `MANIFEST.json` and `NATIVE-REPLAY-EQUALITY.json`. The compressed payload totals about 40 MB; decoded size is about 2 GB. Imported dependency artifacts and the compiler remain trusted inputs. This is proof evidence, not a prebuilt execution environment or a certificate of any concrete stochastic model.
