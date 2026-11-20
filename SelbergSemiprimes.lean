import SelbergSemiprimes.Counting
import SelbergSemiprimes.Selection
import SelbergSemiprimes.Hypothesis
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Finset Set Filter
open scoped BigOperators ENNReal Asymptotics

namespace JSP375

private theorem mass_at_scale {X H K : ℝ} (hx : 3 ≤ X) (hK : 0 < K) (hh : 0 < H)
    (size : H ≤ X / 20) (scale : H = (1 + 640 * K) * (Real.log X) ^ 2)
    (estimate : variance X (H / 2) ≤ ENNReal.ofReal (K * X * (H / 2) * (Real.log X) ^ 2)) :
    (1 + 640 * K) / 1920 ≤ compositeMass (X ^ 2) (X ^ 2 + 4 * X * H) := by
  classical
  have hx0 : 0 < X := by linarith
  have logX : 0 < Real.log X := Real.log_pos (by linarith)
  have log3X : 0 < Real.log (3 * X) := Real.log_pos (by linarith)
  have hlog : Real.log (3 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    linarith [Real.log_le_log (by norm_num : (0:ℝ) < 3) hx]
  obtain ⟨G, sub, many, good⟩ := select_rectangles hx hK hh size scale estimate
  let P := primesThrough (4 * X)
  let L (j : ℕ) := window P (leftStart X H j) H
  let R (j : ℕ) := window P (rightStart X H j) H
  let boxes (j : ℕ) := (L j) ×ˢ (R j)
  let S := G.biUnion boxes
  have dis : (↑G : Set ℕ).PairwiseDisjoint boxes := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    intro z zi zj
    obtain ⟨_, li, ui⟩ := Finset.mem_filter.mp (Finset.mem_product.mp zi).1
    obtain ⟨_, lj, uj⟩ := Finset.mem_filter.mp (Finset.mem_product.mp zj).1
    rcases lt_or_gt_of_ne ne with h | h
    · linarith [left_separated (X := X) hh h]
    · linarith [left_separated (X := X) hh h]
  let w := H / (8 * Real.log X)
  have w0 : 0 ≤ w := by dsimp [w]; positivity
  have wlog : w ≤ H / (4 * Real.log (3 * X)) :=
    div_le_div_of_nonneg_left hh.le (by positivity) (by linarith)
  have both (j : ℕ) (hj : j ∈ G) : w ≤ ((L j).card : ℝ) ∧ w ≤ ((R j).card : ℝ) := by
    obtain ⟨_, hu⟩ := left_bounds hh (sub hj)
    obtain ⟨_, hv⟩ := right_bounds hx0 hh (sub hj)
    exact ⟨wlog.trans (window_count (by linarith) (good j hj).1 log3X),
      wlog.trans (window_count (by linarith) (good j hj).2 log3X)⟩
  have count : (G.card : ℝ) * w ^ 2 ≤ (S.card : ℝ) := by
    have eqc : S.card = ∑ j ∈ G, (L j).card * (R j).card := by
      rw [show S = G.biUnion boxes from rfl, Finset.card_biUnion dis]
      simp [boxes]
    rw [eqc, Nat.cast_sum]
    calc
      _ = ∑ _j ∈ G, w ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj => by
        rw [Nat.cast_mul, sq]
        exact mul_le_mul (both j hj).1 (both j hj).2 w0 (by positivity)
  have total := mass_of_pairs (x := X ^ 2) (y := X ^ 2 + 4 * X * H) (Q := 3 * X) S (by
    intro z hz
    obtain ⟨j, hj, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hz
    obtain ⟨hpP, hpl, hpu⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqP, hql, hqu⟩ := Finset.mem_filter.mp hq
    exact ⟨(Finset.mem_filter.mp hpP).2, (Finset.mem_filter.mp hqP).2,
      rectangle hx0 hh size (sub hj) ⟨hpl, hpu⟩ ⟨hql, hqu⟩⟩)
  calc
    (1 + 640 * K) / 1920 = (X / (10 * H) * w ^ 2) / (3 * X) := by
      dsimp [w]
      field_simp [ne_of_gt hx0, ne_of_gt logX, ne_of_gt hh]
      rw [scale]
      ring
    _ ≤ (S.card : ℝ) / (3 * X) := by
      exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_right many (sq_nonneg w)).trans count) (by positivity)
    _ ≤ _ := total

/-- Exactly one uniform pair of positive constants works for every sufficiently
large real starting point. The sum includes composites only, at both endpoints. -/
def Erdos462 : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    c ≤ compositeMass x (x + C * Real.sqrt x * (Real.log x) ^ 2)

/-- All downstream steps after the classical Selberg mean square. -/
theorem erdos_462_of_selberg (selberg : SelbergThetaEstimate) : Erdos462 := by
  obtain ⟨K, hK, X₀, estimate⟩ := selberg
  let A := 1 + 640 * K
  have ha : 0 < A := by dsimp [A]; positivity
  have growth : (fun X : ℝ => (Real.log X) ^ 2) =o[atTop] (fun X : ℝ => X) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)
  have eventuallyScale : ∀ᶠ X : ℝ in atTop,
      A / 1920 ≤ compositeMass (X ^ 2) (X ^ 2 + 4 * X * (A * (Real.log X) ^ 2)) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ), eventually_ge_atTop X₀,
      Real.tendsto_log_atTop.eventually_ge_atTop 2,
      growth.bound (show 0 < 1 / (20 * A) by positivity)] with X hX large hlog hg
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log X)),
      abs_of_nonneg (by linarith : 0 ≤ X)] at hg
    have size : A * (Real.log X) ^ 2 ≤ X / 20 := by
      have hb : (Real.log X) ^ 2 ≤ X / (20 * A) := by
        simpa only [div_eq_inv_mul, mul_one] using hg
      nlinarith [(le_div_iff₀ (by positivity : 0 < 20 * A)).mp hb]
    have hA : 1 ≤ A := by dsimp [A]; linarith
    have hH : 2 ≤ A * (Real.log X) ^ 2 := by
      have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hlog 2
      nlinarith [mul_le_mul_of_nonneg_right hA (sq_nonneg (Real.log X))]
    exact mass_at_scale hX hK (by linarith) size rfl
      (estimate X large _ (by linarith) (by linarith))
  obtain ⟨T, hT⟩ := eventually_atTop.mp eventuallyScale
  refine ⟨A, A / 1920, ha, by positivity, (max T 3) ^ 2, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := (sq_nonneg _).trans hx
  have hs : max T 3 ≤ Real.sqrt x := by
    simpa only [Real.sqrt_sq (le_trans (by norm_num : (0 : ℝ) ≤ 3) (le_max_right T 3))] using
      Real.sqrt_le_sqrt hx
  have result := hT (Real.sqrt x) ((le_max_left _ _).trans hs)
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    nth_rw 1 [← Real.sq_sqrt hx0]
    simp [Real.log_pow]
  rw [Real.sq_sqrt hx0] at result
  rw [hlog]
  convert result using 2
  ring

/-- The remaining analytic implication is explicit in the type. -/
theorem erdos_462 (grh : DirichletGRH) (saffari_vaughan : RiemannHypothesis → SelbergThetaEstimate) :
    Erdos462 := erdos_462_of_selberg (saffari_vaughan (riemannHypothesis_of_dirichletGRH grh))

#print axioms erdos_462_of_selberg
#print axioms erdos_462

end JSP375
