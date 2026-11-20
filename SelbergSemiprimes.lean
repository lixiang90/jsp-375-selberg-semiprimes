import SelbergSemiprimes.Deduction
import SelbergSemiprimes.Discrete
import SelbergSemiprimes.RealWindows
import SelbergSemiprimes.Hypothesis

namespace JSP375

theorem selberg_theta_of_rh (rh : RiemannHypothesis) : SelbergThetaEstimate := by
  obtain ⟨K, hp, h⟩ := theta_discrete_of_rh rh
  exact real_variance_of_discrete hp h

/-- Ordinary RH suffices for the original composite-only lower bound. -/
theorem erdos_462_of_rh (rh : RiemannHypothesis) : Erdos462 :=
  erdos_462_of_selberg (selberg_theta_of_rh rh)

theorem erdos_462 (grh : DirichletGRH) : Erdos462 :=
  erdos_462_of_rh (riemannHypothesis_of_dirichletGRH grh)

#check @erdos_462_of_rh
#check @erdos_462
#print axioms LeanLab.PNTPort.Selberg.selberg_sum_c
#print axioms erdos_462_of_selberg
#print axioms selberg_theta_of_rh
#print axioms erdos_462_of_rh
#print axioms erdos_462

end JSP375
