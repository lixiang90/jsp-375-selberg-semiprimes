# JSP-000375 · Erdős 462

For some absolute positive constants $C,c$, every sufficiently large real $x$ satisfies

$$
\sum_{\substack{x\le m\le x+C\sqrt{x}(\log x)^2\\m\text{ composite}}}
\frac{P^-(m)}m\ge c,
$$

where $P^-(m)$ is the least prime divisor. The [mathematical proof](PROOF.md) derives this from ordinary RH, hence also from Dirichlet GRH. This is the original proof repository of lixiang90 for [awards PR #5616](https://github.com/TheJustinSunPrize/awards/pull/5616). The downstream deduction and Lean source were developed with OpenAI Codex. The input from prime distribution is classical. Levent Alpöge announced the upstream GRH proof with Claude.

## The checked theorem

[`JSP375.erdos_462_of_selberg`](SelbergSemiprimes/Deduction.lean) proves the full quantified composite-sum statement from one explicit, fixed-length Selberg mean-square estimate for weighted prime counts. Lean constructs the intervals, bounds the number of deficient pairs, counts distinct semiprimes in the required interval and proves a uniform lower bound. If $K$ is the absolute constant in that estimate, the checked argument takes $C=1+640K$ and $c=C/1920$.

[`JSP375.erdos_462_of_rh` and `JSP375.erdos_462`](SelbergSemiprimes.lean) take just ordinary RH and just Dirichlet GRH, respectively. This repository proves the implication starting at that hypothesis. The build imports Steve Hubbard's Lean Lab discrete Selberg theorem and proves the transfers from prime powers to primes and from integer to real windows. The GRH proof archive is external to the build. [Derivation of the formal bridge](PROOF.md#the-formal-bridge-from-rh) · [Upstream Selberg source](https://github.com/sthubbar/goldbach-lean/blob/93b86c05bb441be2ac0b3f06cc4c8624f8e8d0eb/entries/languascozaccagnini2012/LeanLab/PNTPort/Selberg/SumC.lean#L29-L35) · [Alpöge's upstream statement](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Statements.lean#L5-L7)

| Source | Checked step |
| --- | --- |
| [Hypothesis.lean](SelbergSemiprimes/Hypothesis.lean) | Modulus one and the completed zeta functional equation derive mathlib's ordinary RH from the Dirichlet hypothesis. |
| [PrimePowers.lean](SelbergSemiprimes/PrimePowers.lean) | Proper prime powers contribute at most a constant times $NL$ to their discrete mean square. |
| [Discrete.lean](SelbergSemiprimes/Discrete.lean) and [DiscreteBounds.lean](SelbergSemiprimes/DiscreteBounds.lean) | Instantiate the pinned RH theorem on integer windows and convert its bound for the second Chebyshev function to a bound for primes. |
| [RealWindows.lean](SelbergSemiprimes/RealWindows.lean) | Two adjacent integer lengths bound each real window. Unit intervals convert the discrete sums to the required integral. |
| [Variance.lean](SelbergSemiprimes/Variance.lean) | Each deficient bin forces at least $H^3/32$ of variance on its half-bin. Disjoint bins can be counted against one integral. |
| [Grid.lean](SelbergSemiprimes/Grid.lean) | The reciprocal intervals are disjoint within their family and every product falls inside the prescribed interval. |
| [Selection.lean](SelbergSemiprimes/Selection.lean) | At least $X/(10H)$ indices have adequate prime mass in both intervals. |
| [Counting.lean](SelbergSemiprimes/Counting.lean) | The smaller factor is the least prime divisor. The product map is injective and its weights contribute to the original inclusive sum. |
| [Deduction.lean](SelbergSemiprimes/Deduction.lean) | The selected rectangles supply $c$, with one $C$ working for every sufficiently large real starting point. |
| [SelbergSemiprimes.lean](SelbergSemiprimes.lean) | Combine the proven mean square and the interval argument into the RH and Dirichlet GRH targets. |

## Reproduction

From this repository with Elan installed, run the following commands. The toolchain file selects Lean 4.35.0-rc3 and the Lake manifest pins mathlib, Hubbard's number-theory library and their transitive dependencies. The cache command downloads precompiled mathlib packages.

```sh
lake exe cache get
lake build
lake env lean SelbergSemiprimes.lean
lake env leanchecker SelbergSemiprimes LeanLab.PNTPort.Selberg.SumC
```

The audited main theorems report only `propext`, `Classical.choice` and `Quot.sound`. Ordinary RH or Dirichlet GRH appears as an explicit theorem argument. The award PR links the resulting conditional formalization for mathematical-solution review.
