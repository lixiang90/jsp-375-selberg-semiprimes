import Mathlib.Tactic

open Finset Set

namespace JSP375

noncomputable def grid (X H : ℝ) := Finset.range ⌊X / (4 * H)⌋₊
noncomputable def leftStart (X H : ℝ) (j : ℕ) := X / 2 + j * H
noncomputable def rightStart (X H : ℝ) (j : ℕ) := X ^ 2 / leftStart X H j

theorem left_bounds {X H : ℝ} (hh : 0 < H) {j : ℕ} (hj : j ∈ grid X H) :
    X / 2 ≤ leftStart X H j ∧ leftStart X H j + H ≤ 3 * X / 4 := by
  have hj' : j + 1 ≤ ⌊X / (4 * H)⌋₊ := Finset.mem_range.mp hj
  have hfloor := Nat.floor_le (show 0 ≤ X / (4 * H) by
    by_contra! h
    rw [Nat.floor_of_nonpos h.le] at hj'
    omega)
  have hle : (j : ℝ) + 1 ≤ X / (4 * H) := le_trans (by exact_mod_cast hj') hfloor
  have hm := (le_div_iff₀ (by positivity)).mp hle
  constructor
  · unfold leftStart; linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hh.le]
  · unfold leftStart; linarith

theorem right_bounds {X H : ℝ} (hx : 0 < X) (hh : 0 < H) {j : ℕ} (hj : j ∈ grid X H) :
    X ≤ rightStart X H j ∧ rightStart X H j ≤ 2 * X := by
  obtain ⟨ha, hb⟩ := left_bounds hh hj
  have hu : 0 < leftStart X H j := by linarith
  constructor
  · apply (le_div_iff₀ hu).2
    nlinarith [mul_nonneg hx.le (show 0 ≤ X - leftStart X H j by linarith)]
  · apply (div_le_iff₀ hu).2
    nlinarith [mul_nonneg hx.le (show 0 ≤ leftStart X H j - X / 2 by linarith)]

theorem left_separated {X H : ℝ} (hh : 0 < H) {i j : ℕ} (hij : i < j) :
    leftStart X H i + H ≤ leftStart X H j := by
  have hn : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  unfold leftStart
  linarith [mul_le_mul_of_nonneg_right hn hh.le]

theorem right_separated {X H : ℝ} (hx : 0 < X) (hh : 0 < H)
    {i j : ℕ} (hi : i ∈ grid X H) (hj : j ∈ grid X H) (hij : i < j) :
    rightStart X H j + H ≤ rightStart X H i := by
  obtain ⟨ai, bi⟩ := left_bounds hh hi
  obtain ⟨aj, bj⟩ := left_bounds hh hj
  have ui : 0 < leftStart X H i := by linarith
  have uj : 0 < leftStart X H j := by linarith
  have hg : H ≤ leftStart X H j - leftStart X H i := by linarith [left_separated (X := X) hh hij]
  have hm : leftStart X H i * leftStart X H j ≤ X * X :=
    mul_le_mul (by linarith) (by linarith) uj.le hx.le
  unfold rightStart
  calc
    _ = (X ^ 2 + H * leftStart X H j) / leftStart X H j := by field_simp
    _ ≤ _ := (div_le_div_iff₀ uj ui).2 (by
      nlinarith [mul_le_mul_of_nonneg_right hm hh.le, mul_le_mul_of_nonneg_left hg (sq_nonneg X)])

theorem rectangle {X H : ℝ} (hx : 0 < X) (hh : 0 < H) (hsize : H ≤ X / 20)
    {j : ℕ} (hj : j ∈ grid X H) {p q : ℕ}
    (hp : (p : ℝ) ∈ Ioc (leftStart X H j) (leftStart X H j + H))
    (hq : (q : ℝ) ∈ Ioc (rightStart X H j) (rightStart X H j + H)) :
    p < q ∧ X ^ 2 < (p : ℝ) * q ∧ (p : ℝ) * q ≤ X ^ 2 + 4 * X * H ∧ (q : ℝ) ≤ 3 * X := by
  obtain ⟨al, bl⟩ := left_bounds hh hj
  obtain ⟨ar, br⟩ := right_bounds hx hh hj
  have hl : 0 < leftStart X H j := by linarith
  have hv : 0 < rightStart X H j := hx.trans_le ar
  have huv : leftStart X H j * rightStart X H j = X ^ 2 := by unfold rightStart; field_simp
  have hpq : (p : ℝ) < q := by linarith [hp.2, hq.1]
  refine ⟨by exact_mod_cast hpq, ?_, ?_, by linarith [hq.2]⟩
  · rw [← huv]
    exact mul_lt_mul_of_pos_right hp.1 hv |>.trans (mul_lt_mul_of_pos_left hq.1 (hl.trans hp.1))
  · have hm := mul_le_mul hp.2 hq.2 (Nat.cast_nonneg (α := ℝ) q) (by linarith)
    have hb : leftStart X H j + rightStart X H j + H ≤ 4 * X := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hb hh.le]

end JSP375
