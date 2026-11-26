# JSP-000375 · Erdős 462

For some absolute positive constants $C,c$, every sufficiently large real $x$ satisfies

$$
\sum_{\substack{x\le m\le x+C\sqrt{x}(\log x)^2\\m\text{ composite}}}
\frac{P^-(m)}m\ge c,
$$

where $P^-(m)$ is the least prime divisor. The Lean theorem `JSP375.erdos_462 : JSP375.Erdos462` proves this bound unconditionally. It applies the short-interval deduction to mathlib's `RiemannHypothesis`, proved in the included compact GRH source. This is lixiang90's original repository for the downstream proof, developed with OpenAI Codex. [Mathematical proof](PROOF.md) · [Compact source and attribution](vendor/GRH.md) · [Awards PR #5616](https://github.com/TheJustinSunPrize/awards/pull/5616)

## The checked theorem

[`JSP375.erdos_462_of_selberg`](SelbergSemiprimes/Deduction.lean) proves the full quantified composite-sum statement from one explicit, fixed-length Selberg mean-square estimate for weighted prime counts. Lean constructs the intervals, bounds the number of deficient pairs, counts distinct semiprimes in the required interval and proves a uniform lower bound. If $K$ is the absolute constant in that estimate, the checked argument takes $C=1+640K$ and $c=C/1920$.

The intermediate theorem `JSP375.erdos_462_of_rh` uses Steve Hubbard's Lean Lab discrete Selberg theorem and transfers the estimate from prime powers to primes and from integer to real windows. The final theorem supplies the compact proof's `riemannHypothesis : RiemannHypothesis`. The conditional Dirichlet formulation is available as `JSP375.erdos_462_of_dirichletGRH`. [Final composition](SelbergSemiprimes.lean) · [Transfer argument](PROOF.md#the-formal-bridge-from-rh) · [Upstream Selberg source](https://github.com/sthubbar/lean-lab-ci/blob/b2227987a4d27d724204d48257accd4e0936c5d4/LeanLab/LeanLab/PNTPort/Selberg/SumC.lean#L24-L30)

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
| [SelbergSemiprimes.lean](SelbergSemiprimes.lean) | Apply the compact ordinary RH theorem to the Selberg and interval deductions to obtain the full lower bound. |

## Reproduction

From this repository with Elan installed, run the following commands. The proof and the local GRH package use Lean 4.35.0 and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The Lake manifest pins Hubbard's number-theory library and the transitive dependencies. The cache command downloads precompiled mathlib packages.

```sh
lake exe cache get
lake build
lake env lean verification/Unconditional.lean
lake env leanchecker SelbergSemiprimes LeanLab.PNTPort.Selberg.SumC
```

The audit expands the interval, composite filter, and least-prime-factor weight in the theorem statement. It prints the transitive axioms of the ordinary RH, Selberg and final theorems. [Statement audit](verification/Unconditional.lean) · [Upstream Lean theorem](vendor/grh-compact/src/Main.lean) · [Final Lean theorem](SelbergSemiprimes.lean)
