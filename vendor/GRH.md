# Source of the compact GRH proof

`grh-compact/src` contains all 794 production Lean files of the compact edition from `lsernau/grh-lean`, commit `72fead102f663d5c7a407964a13dc0cf9d977207`. The source files are copied verbatim. The proof is due to Levent Alpöge with Claude. The upstream project credits Anthropic colleagues and Claude for the shorter rewriting. [Original project and attribution](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact) · [License](grh-compact/LICENSE) · [Notice](grh-compact/NOTICE) · [Mathlib attribution](grh-compact/ATTRIBUTION.md)

The local Lake package uses upstream's compiler options, Lean 4.35.0 and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The distribution includes the upstream proof, its five-statement axiom audit and its documentation. The optional Comparator challenge fixture, its configuration, and its separate Lake target are omitted. [Formal statements](grh-compact/src/Statements.lean) · [Proofs](grh-compact/src/Main.lean) · [Axiom audit](grh-compact/scripts/PrintAxioms.lean)

`git rev-parse HEAD:vendor/grh-compact/src` gives `b834f80c6399db99d54ce171ba541c4a95a4f90f`, the same Git tree as `grh-compact/src` at the pinned upstream commit.
