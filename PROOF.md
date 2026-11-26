# A uniform lower bound for least prime factors in short intervals

**JSP-000375 · Erdős problem 462**

Let $P^-(m)$ be the least prime divisor of $m>1$. There are absolute constants $C,c>0$ and $x_0$ such that every real $x\ge x_0$ satisfies

$$
\sum_{\substack{x<m\le x+C\sqrt{x}(\log x)^2\\m\ \mathrm{composite}}}
       \frac{P^-(m)}{m}\ \ge c .
$$

In fact it suffices to count products of two distinct primes $p<q$ with $\sqrt{x}/2<p\le 3\sqrt{x}/4$ and $4\sqrt{x}/3<q\le 3\sqrt{x}$. The constant $C$ is chosen once for all $x$. All logarithms are natural. This implies the lower bound in the prize catalog and also covers the inclusive lower endpoint in Erdős and Graham's formulation. [Erdős and Graham, printed p. 92](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf#page=88) · [JSP-000375](https://github.com/TheJustinSunPrize/awards/blob/10e0ab6e7503b6db769029d7d68cc4ca42c011d7/problems/catalog-0301-0400.md#JSP-000375)

## Proof

The compact proof included in this project establishes `riemannHypothesis : RiemannHypothesis` for the Riemann zeta function. It supplies the premise of the Selberg estimate used below. [Compact RH theorem](vendor/grh-compact/src/Main.lean) · [Final Lean proof](SelbergSemiprimes.lean)

Write $\psi(t)=\sum_{n\le t}\Lambda(n)$, where $\Lambda$ is the von Mangoldt function. The Selberg integral bound under RH gives an absolute $K>0$ such that, for large $X$ and $1\le h\le X$,

$$
\int_0^{3X}\!|\psi(t+h)-\psi(t)-h|^2\,dt
       \le K Xh(\log X)^2. \tag{1}
$$

Indeed the fixed-length bound up to $Y$ is $O(Yh\log^2(2Y/h))$ for $1\le h\le Y$. Take $Y=3X$. [Goldston and Suriajaya, equations (15) and (17)](https://arxiv.org/pdf/2110.14250#page=4) · [Saffari and Vaughan](https://doi.org/10.5802/aif.649)

Fix $A=1+640K$. Set $X=\sqrt{x}$, $H=A(\log X)^2$ and $h=H/2$. In all that follows $X$ is sufficiently large for this fixed $A$. Put $J=\lfloor X/(4H)\rfloor$. For $0\le j<J$ let

$$
u_j=X/2+jH,\qquad v_j=x/u_j,\qquad
I_j=(u_j,u_j+H],\qquad Q_j=(v_j,v_j+H].
$$

The intervals $I_j$ are disjoint and lie in $(X/2,3X/4]$. The intervals $Q_j$ lie in $(4X/3,3X]$ and are disjoint, since consecutive left endpoints are separated by

$$v_j-v_{j+1}=\frac{X^2H}{u_ju_{j+1}}\ge\frac{16}{9}H.$$

Every pair $p\in I_j,\ q\in Q_j$ satisfies $x<pq\le x+4XH$. Indeed $u_jv_j=x$ and $(u_j+H)(v_j+H)-x=H(u_j+v_j+H)\le4XH$ for large $X$. Thus each rectangle of paired intervals lies inside the required product range.

Call a bin $(b,b+H]$ deficient if $\psi(b+H)-\psi(b)<H/4$. For each $t\in[b,b+h]$ its subinterval $(t,t+h]$ then has $\psi$-mass less than $H/4=h/2$. The integral in (1) over $[b,b+h]$ is at least $H^3/32$. Summing over either disjoint family gives at most $16KX(\log X)^2/H^2$ deficient bins per family. Consequently, at most

$$
32K\frac{X(\log X)^2}{H^2}
 =\frac{32K}{A}\frac XH
 <\frac{X}{20H}
$$

indices have a deficient bin on either side. Also discard every index for which either bin contains a proper prime power $r^k$, $k\ge2$. Below $3X$ there are $O(\sqrt X\log X)$ such powers, by counting bases and exponents. Each belongs to at most one bin per family. The number of indices discarded here is $o(X/H)$ and hence at most $X/(20H)$ for large $X$. Since $J\ge X/(5H)$ eventually, at least $X/(10H)$ indices remain.

For every remaining index each bin contains at least $H/(4\log(3X))$ primes, since its $\psi$-mass is at least $H/4$ and consists entirely of primes of weight at most $\log(3X)$. Each product $m=pq$ so obtained has $p<q$. Its contribution is $1/q\ge1/(3X)$. Unique factorization and disjointness of the $I_j$ count every product once. We conclude that

$$
\sum_{\substack{x<m\le x+4XH\\m\ \mathrm{composite}}}\frac{P^-(m)}m
 \ge \frac{X}{10H}
       \left(\frac{H}{4\log(3X)}\right)^2\frac1{3X}
 =\frac{H}{480\log^2(3X)}
 \ge\frac A{1920}.
$$

Here $\log(3X)\le2\log X$ for $X\ge3$. Finally $4XH=A\sqrt{x}(\log x)^2$. Taking $C=A$ and $c=A/1920$ proves the theorem. All bounds are uniform in the starting point $x$.

## The version checked in Lean

The Lean proof uses the same grid and weights. It applies the mean square to the first Chebyshev function $\vartheta(t)=\sum_{p\le t}\log p$. A lower bound on a $\vartheta$-increment immediately gives a count of primes, so this version requires no estimate for the number of boxes containing higher prime powers.

Here is the exact analytic input. On ordinary RH there exist $K>0$ and $X_0$ such that, whenever $X\ge X_0$ and $1\le h\le X/20$,

$$
\int_{X/2}^{3X}\big(\vartheta(t+h)-\vartheta(t)-h\big)^2\,dt
\le KXh(\log X)^2.
$$

The factor $h$ matters when $h$ grows with $X$. In the scanned original, Saffari and Vaughan's printed display (6.20) on p. 24 has $h^2x$. The bound used here follows directly from their **(6.4)** on p. 20 and **(6.21)** on p. 25. For $Y=X/2,X,2X$, write $J(Y,h)$ for the integral over $[Y,2Y]$. Our range has $h\le Y/6$. Equation (6.21) bounds $J(Y,h)$ by a constant times

$$
\frac{Y}{h}\int_{h/(3Y)}^{3h/Y}
 \int_Y^{3Y}\big(\vartheta(u+u\delta)-\vartheta(u)-u\delta\big)^2\,du\,d\delta .
$$

Apply (6.4) on $[Y,2Y]$ and $[2Y,4Y]$. The inner integral is $O(\delta Y^2\log^2(2/\delta))$. Throughout the outer integral $\log(2/\delta)\le\log(6Y/h)$, and integrating $\delta$ gives $O((h/Y)^2)$. Thus $J(Y,h)\ll Yh\log^2(6Y/h)$. Summing the three dyadic estimates gives the displayed input because $h\ge1$ and $Y\asymp X$. Either convention for the inclusion of a prime at an endpoint gives the same integral, since it changes the integrand on a measure-zero set. [Saffari–Vaughan, (6.4)](https://aif.centre-mersenne.org/item/10.5802/aif.649.pdf#page=21) · [(6.20) as printed](https://aif.centre-mersenne.org/item/10.5802/aif.649.pdf#page=25) · [(6.21)](https://aif.centre-mersenne.org/item/10.5802/aif.649.pdf#page=26)

Take $A=1+640K$, $X=\sqrt{x}$ and $H=A\log^2X$ as above. For all sufficiently large $X$, $2\le H\le X/20$. Each deficient bin contributes $H^3/32$ to the variance, so each family has at most $X/(40H)$ deficient bins. The grid has at least $X/(5H)$ indices, leaving at least $X/(10H)$ with adequate bins on both sides. Each good bin contains at least $H/(4\log(3X))\ge H/(8\log X)$ primes. Multiplication is injective on the selected ordered pairs because the smaller prime is recovered as the least prime factor. Each contributes at least $1/(3X)$ to the inclusive composite sum. Its lower bound is therefore

$$
\frac{X}{10H}\left(\frac{H}{8\log X}\right)^2\frac{1}{3X}
=\frac A{1920}.
$$

## The formal bridge from RH

The Lean proof invokes Steve Hubbard's Lean Lab theorem **selberg_sum_c** with its upper summation limit $M=N$. On ordinary RH it yields

$$
\sum_{k<N}\big(\psi(k+L)-\psi(k)-L\big)^2\ll NL(\log N+3)^2\qquad(1\le L\le N).
$$

Indeed $\log(N/L)\le\log N$, $1/\sqrt L\le1$ and $L^2\le NL$. The dependency is pinned to Steve Hubbard's public Lean Lab build mirror at the same Lean and mathlib versions as the compact GRH proof. The earlier release-candidate build used the Languasco–Zaccagnini distribution of this theorem. [Hubbard's theorem and proof](https://github.com/sthubbar/lean-lab-ci/blob/b2227987a4d27d724204d48257accd4e0936c5d4/LeanLab/LeanLab/PNTPort/Selberg/SumC.lean#L24-L30) · [Earlier distribution and attribution](https://github.com/sthubbar/goldbach-lean/blob/93b86c05bb441be2ac0b3f06cc4c8624f8e8d0eb/entries/languascozaccagnini2012/PORTING.md)

Put $F=\psi-\vartheta$. This is the nondecreasing weight of proper prime powers. Mathlib proves $0\le F(y)\le B\sqrt y$ for an absolute $B>0$. For $d_k=F(k+L)-F(k)$, cancellation of the two sums gives $\sum_{k<N}d_k\le L F(N+L)$. Since $0\le d_k\le F(N+L)$, it follows that $\sum_{k<N}d_k^2\le L F(N+L)^2\le 2B^2 NL$. Applying $(u-v)^2\le2u^2+2v^2$ gives the same order of variance for $\vartheta$ on integer windows. [Mathlib's prime-power estimate](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Chebyshev.lean#L592-L603) · [Formal transfer to primes](SelbergSemiprimes/PrimePowers.lean)

For a real starting point $t$ and real length $h$, put $k=\lfloor t\rfloor$ and $L=\lfloor h\rfloor$. The integer upper endpoint is either $k+L$ or $k+L+1$. If $E_j(k)=\vartheta(k+j)-\vartheta(k)-j$, monotonicity bounds the real error between $E_L(k)-1$ and $E_{L+1}(k)+1$. Its square is at most $2(E_L(k)^2+E_{L+1}(k)^2+1)$. Integrating over unit intervals and applying both integer-window bounds gives the required $O(Xh\log^2 X)$, uniformly for $1\le h\le X/20$ and $X\ge e^4$. [Real-window proof](SelbergSemiprimes/RealWindows.lean) · [Main theorem](SelbergSemiprimes.lean)

## Sources and attribution

The question is due to Paul Erdős and Ronald Graham. The short-interval mean-square theorem is classical. Xu Zhang's October 2026 revision gives a uniform result under its bounded-fluctuation Hypothesis 1.5. The paired intervals above use only the ordinary RH input (1). The large constant permitted by the original question makes the union of the two exceptional sets small enough. [Zhang, Hypothesis 1.5 and Theorem 1.7](https://arxiv.org/html/2608.24930v2#S1)

Levent Alpöge announced an upstream proof with Claude on 20 November 2026. Its compact rewriting supplies the ordinary RH theorem directly in this build. The downstream argument and integration were developed with OpenAI Codex for the submitting GitHub account lixiang90. [Alpöge's announcement](https://alpo.ge/remark.pdf) · [Compact source and attribution](vendor/GRH.md)
