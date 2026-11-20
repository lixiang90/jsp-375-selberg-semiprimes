import SelbergSemiprimes.DiscreteBounds
import LeanLab.PNTPort.Selberg.SumC

open Finset
open scoped BigOperators

namespace JSP375

/-- Instantiate Steve Hubbard's Lean Lab RH theorem at M = N. -/
theorem theta_discrete_of_rh (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ N L : ℕ, 1 ≤ L → L ≤ N →
      (∑ m ∈ range N, incrementError Chebyshev.theta m L ^ 2) ≤
        K * N * L * (Real.log N + 3) ^ 2 := by
  obtain ⟨C, hc, psi⟩ := LeanLab.PNTPort.Selberg.selberg_sum_c hRH
  exact theta_discrete_of_psi hc (fun N L hl hn => psi N L N hl hn le_rfl)

end JSP375
