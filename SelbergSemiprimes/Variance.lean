import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open Finset Set MeasureTheory
open scoped BigOperators ENNReal

namespace JSP375

noncomputable def primesThrough (y : ℝ) : Finset ℕ := (range (⌊y⌋₊ + 1)).filter Nat.Prime

noncomputable def window (P : Finset ℕ) (b H : ℝ) : Finset ℕ :=
  P.filter fun p => b < (p : ℝ) ∧ (p : ℝ) ≤ b + H

noncomputable def thetaIncrement (P : Finset ℕ) (b H : ℝ) : ℝ :=
  ∑ p ∈ window P b H, Real.log p

noncomputable def variance (X h : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc (X / 2) (3 * X),
    ENNReal.ofReal ((thetaIncrement (primesThrough (4 * X)) t h - h) ^ 2)

/-- A fixed-length consequence of Saffari–Vaughan (6.4) and (6.21) under RH.
Cover [X/2,3X] by three dyadic intervals. For t in this range and h ≤ X/20,
truncating the prime set at 4X leaves every increment unchanged. -/
def SelbergThetaEstimate : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℝ, 1 ≤ h → h ≤ X / 20 →
    variance X h ≤ ENNReal.ofReal (K * X * h * (Real.log X) ^ 2)

theorem increment_mono {P : Finset ℕ} {b t H h : ℝ} (hb : b ≤ t) (hh : t + h ≤ b + H) :
    thetaIncrement P t h ≤ thetaIncrement P b H := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hP, hl, hu⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hP, hb.trans_lt hl, hu.trans hh⟩
  · intro p _ _
    by_cases hp : p = 0
    · simp [hp]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)

theorem window_count {P : Finset ℕ} {b H X : ℝ}
    (hmax : b + H ≤ 3 * X) (hmass : H / 4 ≤ thetaIncrement P b H)
    (hlog : 0 < Real.log (3 * X)) :
    H / (4 * Real.log (3 * X)) ≤ ((window P b H).card : ℝ) := by
  have bound : thetaIncrement P b H ≤ ((window P b H).card : ℝ) * Real.log (3 * X) := by
    calc
      _ ≤ ∑ _p ∈ window P b H, Real.log (3 * X) := Finset.sum_le_sum fun p hp => by
        by_cases h : p = 0
        · simpa [h] using hlog.le
        · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h) ((mem_filter.mp hp).2.2.trans hmax)
      _ = _ := by simp
  apply (div_le_iff₀ (by positivity)).2
  linarith

/-- Each deficient bin forces H³/32 of nonnegative variance on a disjoint
half-bin. All counting and integration in this implication are internal. -/
theorem deficient_bins {X H : ℝ} (hH : 0 < H) (D : Finset ℕ) (b : ℕ → ℝ)
    (sep : (↑D : Set ℕ).PairwiseDisjoint (fun j => Ioc (b j) (b j + H / 2)))
    (inside : ∀ j ∈ D, X / 2 ≤ b j ∧ b j + H / 2 ≤ 3 * X)
    (deficit : ∀ j ∈ D, thetaIncrement (primesThrough (4 * X)) (b j) H < H / 4) :
    ENNReal.ofReal ((D.card : ℝ) * H ^ 3 / 32) ≤ variance X (H / 2) := by
  classical
  let U := ⋃ j ∈ D, Ioc (b j) (b j + H / 2)
  have hm : MeasurableSet U := D.measurableSet_biUnion (fun _ _ => measurableSet_Ioc)
  have vol : volume U = ENNReal.ofReal ((D.card : ℝ) * (H / 2)) := by
    dsimp [U]
    rw [measure_biUnion_finset sep (fun _ _ => measurableSet_Ioc)]
    simp [Real.volume_Ioc, ENNReal.ofReal_mul]
  have sub : U ⊆ Ioc (X / 2) (3 * X) := by
    intro t ht
    obtain ⟨j, hj, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨(inside j hj).1.trans_lt ht.1, ht.2.trans (inside j hj).2⟩
  have point (t : ℝ) (ht : t ∈ U) :
      ENNReal.ofReal ((H / 4) ^ 2) ≤
        ENNReal.ofReal ((thetaIncrement (primesThrough (4 * X)) t (H / 2) - H / 2) ^ 2) := by
    obtain ⟨j, hj, ht⟩ := mem_iUnion₂.mp ht
    have inc := (increment_mono (P := primesThrough (4 * X)) ht.1.le
      (show t + H / 2 ≤ b j + H by linarith [ht.2])).trans_lt (deficit j hj)
    apply ENNReal.ofReal_le_ofReal
    calc
      (H / 4) ^ 2 ≤ (H / 2 - thetaIncrement (primesThrough (4 * X)) t (H / 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = _ := by ring
  calc
    _ = ENNReal.ofReal ((H / 4) ^ 2) * volume U := by
      rw [vol, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ = ∫⁻ _t in U, ENNReal.ofReal ((H / 4) ^ 2) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ t in U, ENNReal.ofReal ((thetaIncrement (primesThrough (4 * X)) t (H / 2) - H / 2) ^ 2) :=
      setLIntegral_mono' hm point
    _ ≤ _ := lintegral_mono_set sub

#print axioms deficient_bins

end JSP375
