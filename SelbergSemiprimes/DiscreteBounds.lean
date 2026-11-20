import SelbergSemiprimes.PrimePowers

open Finset Real
open scoped BigOperators

namespace JSP375

/-- The fixed integer length variance for primes, with an absolute constant. -/
theorem theta_discrete_of_psi {C : ℝ} (hc : 0 ≤ C)
    (psi : ∀ N L : ℕ, 1 ≤ L → L ≤ N →
      (∑ m ∈ range N, incrementError Chebyshev.psi m L ^ 2) ≤
        C * (N * L * (Real.log (N / L) + 3) ^ 2 +
          N * ((Real.log N + 2) ^ 2 / Real.sqrt L) + (L : ℝ) ^ 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N L : ℕ, 1 ≤ L → L ≤ N →
      (∑ m ∈ range N, incrementError Chebyshev.theta m L ^ 2) ≤
        K * N * L * (Real.log N + 3) ^ 2 := by
  obtain ⟨D, hd, diff⟩ := prime_powers_energy
  refine ⟨6 * C + D, by positivity, ?_⟩
  intro N L h1 h2
  have l1 : (1 : ℝ) ≤ L := by exact_mod_cast h1
  have ln : (L : ℝ) ≤ N := by exact_mod_cast h2
  have n1 : (1 : ℝ) ≤ N := l1.trans ln
  have l0 : (0 : ℝ) < L := by linarith
  have n0 : (0 : ℝ) < N := by linarith
  have logN := Real.log_nonneg n1
  let B := (Real.log N + 3) ^ 2
  have b1 : 1 ≤ B := by dsimp [B]; nlinarith [sq_nonneg (Real.log N)]
  have ratio : 1 ≤ (N : ℝ) / L := (le_div_iff₀ l0).2 (by simpa using ln)
  have logr := Real.log_nonneg ratio
  have lr : Real.log ((N : ℝ) / L) ≤ Real.log N :=
    Real.log_le_log (by positivity) (div_le_self n0.le l1)
  have main : (N : ℝ) * L * (Real.log (N / L) + 3) ^ 2 ≤ N * L * B := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have second : (Real.log N + 2) ^ 2 / Real.sqrt L ≤ B := by
    exact (div_le_self (sq_nonneg _) (Real.one_le_sqrt.2 l1)).trans
      (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have prod_ge : (N : ℝ) * L ≤ N * L * B := le_mul_of_one_le_right (by positivity) b1
  have n_le : (N : ℝ) ≤ N * L := le_mul_of_one_le_right n0.le l1
  have second' : (N : ℝ) * ((Real.log N + 2) ^ 2 / Real.sqrt L) ≤ N * L * B :=
    mul_le_mul n_le second (by positivity) (by positivity)
  have last : (L : ℝ) ^ 2 ≤ N * L * B :=
    (by simpa only [sq] using (mul_le_mul_of_nonneg_right ln l0.le) : (L : ℝ) ^ 2 ≤ N * L).trans prod_ge
  have q := psi N L h1 h2
  have hpsi : (∑ m ∈ range N, incrementError Chebyshev.psi m L ^ 2) ≤ C * (3 * (N * L * B)) :=
    q.trans (mul_le_mul_of_nonneg_left (by linarith) hc)
  have d := diff N L h2
  change _ ≤ (6 * C + D) * N * L * B
  nlinarith [mul_le_mul_of_nonneg_left prod_ge hd.le]

end JSP375
