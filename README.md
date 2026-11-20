# JSP-000375 · Erdős 462

For some absolute positive constants $C,c$, every sufficiently large real $x$ satisfies

$$
\sum_{\substack{x\le m\le x+C\sqrt{x}(\log x)^2\\m\text{ composite}}}
\frac{P^-(m)}m\ge c,
$$

where $P^-(m)$ is the least prime divisor. The [mathematical proof](PROOF.md) derives this from ordinary RH, hence also from Dirichlet GRH. This is the original proof repository of lixiang90 for [awards PR #5616](https://github.com/TheJustinSunPrize/awards/pull/5616). The downstream deduction and Lean source were developed with OpenAI Codex. The input from prime distribution is classical. Levent Alpöge announced the upstream GRH proof with Claude.

## The checked theorem

[`JSP375.erdos_462_of_selberg`](SelbergSemiprimes.lean) proves the full quantified composite-sum statement from one explicit, fixed-length Selberg mean-square estimate for weighted prime counts. Lean constructs the intervals, bounds the number of deficient pairs, counts distinct semiprimes in the required interval and proves a uniform lower bound. If $K$ is the absolute constant in that estimate, the checked argument takes $C=1+640K$ and $c=C/1920$.

[`JSP375.erdos_462`](SelbergSemiprimes.lean) takes both `DirichletGRH` and the implication `RiemannHypothesis → SelbergThetaEstimate` as theorem arguments. The latter remains to be proved in Lean. The mathematical proof derives that estimate from Saffari and Vaughan's (6.4) and (6.21), with the powers of the interval length calculated explicitly. The independent build accepts upstream GRH as a premise. [Derivation and references](PROOF.md#the-version-checked-in-lean) · [Alpöge's upstream statement](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Statements.lean#L5-L7)

| Source | Checked step |
| --- | --- |
| [Hypothesis.lean](SelbergSemiprimes/Hypothesis.lean) | Modulus one and the completed zeta functional equation derive mathlib's ordinary RH from the Dirichlet hypothesis. |
| [Variance.lean](SelbergSemiprimes/Variance.lean) | Each deficient bin forces at least $H^3/32$ of variance on its half-bin. Disjoint bins can be counted against one integral. |
| [Grid.lean](SelbergSemiprimes/Grid.lean) | The reciprocal intervals are disjoint within their family and every product falls inside the prescribed interval. |
| [Selection.lean](SelbergSemiprimes/Selection.lean) | At least $X/(10H)$ indices have adequate prime mass in both intervals. |
| [Counting.lean](SelbergSemiprimes/Counting.lean) | The smaller factor is the least prime divisor. The product map is injective and its weights contribute to the original inclusive sum. |
| [SelbergSemiprimes.lean](SelbergSemiprimes.lean) | The selected rectangles supply $c$, with one $C$ working for every sufficiently large real starting point. |

## Reproduction

From this repository with Elan installed, run the following commands. The toolchain file selects Lean 4.22.0-rc4 and the Lake manifest pins mathlib and all transitive dependencies. The cache command downloads precompiled mathlib packages.

```sh
lake exe cache get
lake build
lake env lean SelbergSemiprimes.lean
```

The audited declarations report only `propext`, `Classical.choice` and `Quot.sound`. The mean-square implication is an explicit parameter of the GRH theorem. It remains a dependency even though it does not appear in the axiom list. The award PR requests mathematical-solution review.
