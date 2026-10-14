# GitHub Actions warning triage (13 October 2026)

From successful [ATR workflow 38454233640](https://github.com/janhubicka/lean-3-uniform-diaries/actions/runs/38454233640): about 385 warning lines (cache-sensitive), 177 explicitly from `ThreeUniformDiaries/`, 87 from `Milliken/`, and 49 from `SuccessorTree/`. This includes Lean deprecation and linter advice; the workflow passed.

**Mechanical local fixes:** `if_pos/if_neg` → `ite_eq_left/ite_eq_right`, `dif_pos/dif_neg` → `dite_eq_left/dite_eq_right`, and `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`. Review exact build results, since an alias replacement that looks simple may expose a signature mismatch.

**Separately scheduled work:** unnecessary `simpa`, unused `simp` arguments and tactic lines need proof-by-proof changes; `module` conversion crosses package boundaries. Never disable global linter checks just to lower the warning count.

**Workflow:** GitHub's Node.js 20 deprecation warns on `actions/checkout@v4`; upgrade to v5. Lake's missing-manifest notes during first dependency resolution and Git's temporary 'master' hint do not indicate mathematical errors.

Keep exact per-file warning provenance when checking a changed CI run.