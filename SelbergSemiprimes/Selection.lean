import SelbergSemiprimes.Grid
import SelbergSemiprimes.Variance

open Finset Set MeasureTheory
open scoped BigOperators ENNReal

namespace JSP375

private theorem disjoint_bins {I : Finset ℕ} {b : ℕ → ℝ} {W : ℝ}
    (apart : ∀ i ∈ I, ∀ j ∈ I, i < j → b i + W ≤ b j ∨ b j + W ≤ b i) :
    (↑I : Set ℕ).PairwiseDisjoint (fun j => Ioc (b j) (b j + W)) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro t hti htj
  obtain hij | hji := lt_or_gt_of_ne hij
  · rcases apart i hi j hj hij with h | h <;> linarith [hti.1, hti.2, htj.1, htj.2]
  · rcases apart j hj i hi hji with h | h <;> linarith [hti.1, hti.2, htj.1, htj.2]

theorem select_rectangles {X H K : ℝ} (hx : 3 ≤ X) (hK : 0 < K) (hh : 0 < H)
    (size : H ≤ X / 20) (scale : H = (1 + 640 * K) * (Real.log X) ^ 2)
    (estimate : variance X (H / 2) ≤ ENNReal.ofReal (K * X * (H / 2) * (Real.log X) ^ 2)) :
    ∃ G : Finset ℕ, G ⊆ grid X H ∧ X / (10 * H) ≤ (G.card : ℝ) ∧
      ∀ j ∈ G, H / 4 ≤ thetaIncrement (primesThrough (4 * X)) (leftStart X H j) H ∧
        H / 4 ≤ thetaIncrement (primesThrough (4 * X)) (rightStart X H j) H := by
  classical
  let I := grid X H
  let P := primesThrough (4 * X)
  let bad (b : ℕ → ℝ) := I.filter (fun j => thetaIncrement P (b j) H < H / 4)
  have hx0 : 0 < X := by linarith
  have budget (b : ℕ → ℝ)
      (inside : ∀ j ∈ I, X / 2 ≤ b j ∧ b j + H / 2 ≤ 3 * X)
      (apart : ∀ i ∈ I, ∀ j ∈ I, i < j → b i + H / 2 ≤ b j ∨ b j + H / 2 ≤ b i) :
      ((bad b).card : ℝ) * H ≤ X / 40 := by
    have sub : bad b ⊆ I := filter_subset _ _
    have sep := disjoint_bins (I := bad b) (b := b) (W := H / 2) (by
      intro i hi j hj hij; exact apart i (sub hi) j (sub hj) hij)
    have raw := (deficient_bins hh (bad b) b sep (fun j hj => inside j (sub hj))
      (fun _ hj => (mem_filter.mp hj).2)).trans estimate
    have bound := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp raw
    have aux : 0 ≤ H - 640 * K * (Real.log X) ^ 2 := by nlinarith [sq_nonneg (Real.log X)]
    exact le_of_mul_le_mul_right
      (show (((bad b).card : ℝ) * H) * H ^ 2 ≤ (X / 40) * H ^ 2 by
        nlinarith [mul_nonneg aux (mul_nonneg hx0.le hh.le)])
      (sq_pos_of_pos hh)
  let D := bad (leftStart X H)
  let E := bad (rightStart X H)
  have hD : (D.card : ℝ) * H ≤ X / 40 := by
    apply budget
    · intro j hj
      obtain ⟨a, b⟩ := left_bounds hh hj
      exact ⟨a, by linarith⟩
    · intro i hi j hj hij
      exact Or.inl (by linarith [left_separated (X := X) hh hij])
  have hE : (E.card : ℝ) * H ≤ X / 40 := by
    apply budget
    · intro j hj
      obtain ⟨a, b⟩ := right_bounds hx0 hh hj
      exact ⟨by linarith, by linarith⟩
    · intro i hi j hj hij
      exact Or.inr (by linarith [right_separated hx0 hh hi hj hij])
  let G := I \ (D ∪ E)
  have subDE : D ∪ E ⊆ I := Finset.union_subset (filter_subset _ _) (filter_subset _ _)
  have cardG : G.card + (D ∪ E).card = I.card :=
    Finset.card_sdiff_add_card_eq_card subDE
  have gone : (I.card : ℝ) ≤ G.card + (D.card + E.card : ℕ) := by
    exact_mod_cast (show I.card ≤ G.card + (D.card + E.card) by
      linarith [Finset.card_union_le D E])
  push_cast at gone
  have boards : X / 4 ≤ ((I.card : ℝ) + 1) * H := by
    have hf := Nat.lt_floor_add_one (X / (4 * H))
    have hj : I.card = ⌊X / (4 * H)⌋₊ := Finset.card_range _
    rw [hj]
    nlinarith [(div_lt_iff₀ (by positivity : 0 < 4 * H)).mp hf]
  refine ⟨G, Finset.sdiff_subset, (div_le_iff₀ (by positivity)).2 ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right gone hh.le]
  · intro j hj
    obtain ⟨hi, hde⟩ := Finset.mem_sdiff.mp hj
    constructor
    · by_contra! he
      exact hde (Finset.mem_union_left E (Finset.mem_filter.mpr ⟨hi, he⟩))
    · by_contra! he
      exact hde (Finset.mem_union_right D (Finset.mem_filter.mpr ⟨hi, he⟩))

#print axioms select_rectangles

end JSP375
