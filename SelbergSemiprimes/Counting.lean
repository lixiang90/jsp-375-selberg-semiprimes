import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace JSP375

/-- The catalog uses the inclusive lower endpoint. -/
noncomputable def composites (x y : ℝ) : Finset ℕ :=
  (range (⌊y⌋₊ + 1)).filter fun m => 1 < m ∧ ¬ m.Prime ∧ x ≤ (m : ℝ) ∧ (m : ℝ) ≤ y

noncomputable def weight (m : ℕ) : ℝ := (m.minFac : ℝ) / m

noncomputable def compositeMass (x y : ℝ) : ℝ := ∑ m ∈ composites x y, weight m

theorem minFac_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (p * q).minFac = p := by
  have h1 : p * q ≠ 1 := by nlinarith [hp.two_le, hq.two_le, Nat.mul_le_mul hp.two_le hq.two_le]
  have hf := Nat.minFac_prime h1
  have hle := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
  rcases hf.dvd_mul.mp (Nat.minFac_dvd _) with h | h
  · exact ((Nat.dvd_prime hp).mp h).resolve_left hf.ne_one
  · have he := ((Nat.dvd_prime hq).mp h).resolve_left hf.ne_one
    omega

theorem semiprime_weight {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    weight (p * q) = 1 / (q : ℝ) := by
  rw [weight, minFac_semiprime hp hq hpq, Nat.cast_mul]
  have hpn : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [div_mul_eq_div_div, div_self hpn]

/-- Ordered distinct prime factors make the product map injective on these pairs.
The inequality counts terms of the original inclusive composite-only sum. -/
theorem mass_of_pairs {x y Q : ℝ} (S : Finset (ℕ × ℕ))
    (data : ∀ z ∈ S, z.1.Prime ∧ z.2.Prime ∧ z.1 < z.2 ∧
      x < (z.1 : ℝ) * z.2 ∧ (z.1 : ℝ) * z.2 ≤ y ∧ (z.2 : ℝ) ≤ Q) :
    (S.card : ℝ) / Q ≤ compositeMass x y := by
  classical
  let f (z : ℕ × ℕ) := z.1 * z.2
  have inj : Set.InjOn f (↑S : Set (ℕ × ℕ)) := by
    intro a ha b hb he
    obtain ⟨pa, qa, ab, _⟩ := data a ha
    obtain ⟨pb, qb, bb, _⟩ := data b hb
    have eqp := congrArg Nat.minFac he
    change (a.1 * a.2).minFac = (b.1 * b.2).minFac at eqp
    rw [minFac_semiprime pa qa ab, minFac_semiprime pb qb bb] at eqp
    apply Prod.ext eqp
    change a.1 * a.2 = b.1 * b.2 at he
    rw [← eqp] at he
    exact Nat.eq_of_mul_eq_mul_left pa.pos he
  have sub : S.image f ⊆ composites x y := by
    intro m hm
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hm
    obtain ⟨hp, hq, _, hx, hy, _⟩ := data z hz
    have hcast : (f z : ℝ) ≤ y := by simpa [f] using hy
    have hnat := Nat.le_floor hcast
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
    exact ⟨by dsimp [f]; nlinarith [Nat.mul_le_mul hp.two_le hq.two_le],
      Nat.not_prime_mul hp.ne_one hq.ne_one, by simpa [f] using hx.le, hcast⟩
  calc
    (S.card : ℝ) / Q = ∑ _z ∈ S, 1 / Q := by simp [div_eq_mul_inv]
    _ ≤ ∑ z ∈ S, weight (f z) := Finset.sum_le_sum fun z hz => by
      obtain ⟨hp, hq, hpq, _, _, hQ⟩ := data z hz
      change 1 / Q ≤ weight (z.1 * z.2)
      rw [semiprime_weight hp hq hpq]
      exact one_div_le_one_div_of_le (by exact_mod_cast hq.pos) hQ
    _ = ∑ m ∈ S.image f, weight m := (Finset.sum_image inj).symm
    _ ≤ compositeMass x y := Finset.sum_le_sum_of_subset_of_nonneg sub (by
      intro m _ _; unfold weight; positivity)

#print axioms mass_of_pairs

end JSP375
