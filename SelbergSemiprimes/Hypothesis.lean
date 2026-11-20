import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic

namespace JSP375

/-- The right-half-plane formulation in Alpöge's public theorem. -/
def DirichletGRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

theorem riemannHypothesis_of_dirichletGRH (grh : DirichletGRH) : RiemannHypothesis := by
  have right (z : ℂ) (hz : 1 / 2 < z.re) (hone : z ≠ 1) : riemannZeta z ≠ 0 := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      grh 1 (1 : DirichletCharacter ℂ 1) z hz (Or.inr hone)
  intro s hz htriv hone
  have hs : s ≠ 0 := by
    intro he
    subst s
    norm_num [riemannZeta_zero] at hz
  have hgamma : Complex.Gammaℝ s ≠ 0 := by
    rintro he
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp he
    cases n with
    | zero => exact hs (by simpa using hn)
    | succ k => exact htriv ⟨k, by rw [hn]; push_cast; ring⟩
  apply le_antisymm
  · exact le_of_not_gt fun h => right s h hone hz
  · by_contra! h
    have href : (1 - s : ℂ).re > 1 / 2 := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hc : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs, div_eq_zero_iff] at hz
      exact hz.resolve_right hgamma
    have h0 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hone)
    apply right (1 - s) href (by intro he; apply hs; linear_combination -he)
    rw [riemannZeta_def_of_ne_zero h0, completedRiemannZeta_one_sub, hc, zero_div]

#print axioms riemannHypothesis_of_dirichletGRH

end JSP375
