import SelbergSemiprimes

example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    let y := x + C * Real.sqrt x * (Real.log x) ^ 2
    c ≤ ((Finset.range (⌊y⌋₊ + 1)).filter
      (fun m : ℕ => 1 < m ∧ ¬m.Prime ∧ x ≤ (m : ℝ) ∧ (m : ℝ) ≤ y)).sum
        (fun m : ℕ => (m.minFac : ℝ) / (m : ℝ)) :=
  JSP375.erdos_462

#check @JSP375.erdos_462
#print axioms riemannHypothesis
#print axioms LeanLab.PNTPort.Selberg.selberg_sum_c
#print axioms JSP375.erdos_462_of_rh
#print axioms JSP375.erdos_462
