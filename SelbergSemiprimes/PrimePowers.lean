import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace JSP375

noncomputable def incrementError (f : ℝ → ℝ) (m L : ℕ) : ℝ :=
  f ((m : ℝ) + L) - f m - L

private theorem sum_increments (F : ℕ → ℝ) (mono : Monotone F) (pos : ∀ n, 0 ≤ F n)
    (N L : ℕ) :
    ∑ k ∈ range N, (F (k + L) - F k) ≤ (L : ℝ) * F (N + L) := by
  have exch : (∑ k ∈ range N, F (L + k)) - ∑ k ∈ range N, F k =
      (∑ j ∈ range L, F (N + j)) - ∑ j ∈ range L, F j := by
    have h := Finset.sum_range_add F L N
    rw [Nat.add_comm L N, Finset.sum_range_add F N L] at h
    linarith
  rw [Finset.sum_sub_distrib]
  simp_rw [Nat.add_comm _ L]
  rw [exch]
  have upper : (∑ j ∈ range L, F (N + j)) ≤ ∑ _j ∈ range L, F (N + L) :=
    Finset.sum_le_sum fun j hj => mono (by have := Finset.mem_range.mp hj; omega)
  simp at upper
  rw [Nat.add_comm L N]
  linarith [Finset.sum_nonneg (fun j (_ : j ∈ range L) => pos j)]

/-- Proper prime powers have total von Mangoldt weight O(√N).
Over sliding intervals of length L each unit of that weight appears at most L times. -/
theorem prime_powers_energy :
    ∃ D : ℝ, 0 < D ∧ ∀ N L : ℕ, L ≤ N →
      (∑ m ∈ range N, (incrementError Chebyshev.theta m L) ^ 2) ≤
        2 * (∑ m ∈ range N, (incrementError Chebyshev.psi m L) ^ 2) + D * N * L := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let B := |C| + 1
  have hb : 0 < B := by dsimp [B]; positivity
  have cB : C ≤ B := by dsimp [B]; linarith [le_abs_self C]
  refine ⟨2 * (2 * B ^ 2), by positivity, ?_⟩
  intro N L hL
  let F (n : ℕ) := Chebyshev.psi n - Chebyshev.theta n
  have pos (n : ℕ) : 0 ≤ F n := sub_nonneg.mpr (Chebyshev.theta_le_psi n)
  have mono : Monotone F := by
    intro i j hij
    dsimp [F]
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Chebyshev.psi_sub_theta_eq_sum_not_prime]
    simp only [Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.filter_subset_filter
      intro k hk
      obtain ⟨ha, hb'⟩ := Finset.mem_Ioc.mp hk
      exact Finset.mem_Ioc.mpr ⟨ha, hb'.trans hij⟩
    · exact fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
  let M := F (N + L)
  have hM : 0 ≤ M := pos _
  have bound : M ≤ B * Real.sqrt ((N : ℝ) + L) := by
    have q := hC ((N : ℝ) + L)
    simpa only [M, F, Nat.cast_add] using q.trans (mul_le_mul_of_nonneg_right cB (Real.sqrt_nonneg _))
  have M2 : M ^ 2 ≤ 2 * B ^ 2 * N := by
    have q := pow_le_pow_left₀ hM bound 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at q
    have les : (L : ℝ) ≤ N := by exact_mod_cast hL
    nlinarith [mul_le_mul_of_nonneg_left les (sq_nonneg B)]
  let d (k : ℕ) := F (k + L) - F k
  have d0 (k : ℕ) : 0 ≤ d k := sub_nonneg.mpr (mono (by omega))
  have dq (k : ℕ) (hk : k ∈ range N) : d k ≤ M := by
    have hk' := Finset.mem_range.mp hk
    dsimp [d, M]
    linarith [mono (show k + L ≤ N + L by omega), pos k]
  have dsq : (∑ k ∈ range N, d k ^ 2) ≤ (L : ℝ) * M ^ 2 := by
    calc
      _ ≤ ∑ k ∈ range N, d k * M := Finset.sum_le_sum fun k hk => by
        rw [sq]; exact mul_le_mul_of_nonneg_left (dq k hk) (d0 k)
      _ = (∑ k ∈ range N, d k) * M := (Finset.sum_mul _ _ _).symm
      _ ≤ ((L : ℝ) * M) * M := mul_le_mul_of_nonneg_right (sum_increments F mono pos N L) hM
      _ = _ := by ring
  have each (k : ℕ) : incrementError Chebyshev.theta k L ^ 2 ≤
      2 * incrementError Chebyshev.psi k L ^ 2 + 2 * d k ^ 2 := by
    have he : incrementError Chebyshev.theta k L = incrementError Chebyshev.psi k L - d k := by
      dsimp [incrementError, d, F]; push_cast; ring
    rw [he]; nlinarith [sq_nonneg (incrementError Chebyshev.psi k L + d k)]
  have sum := Finset.sum_le_sum (s := range N) fun k _ => each k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at sum
  nlinarith [mul_le_mul_of_nonneg_left M2 (Nat.cast_nonneg (α := ℝ) L)]

end JSP375
