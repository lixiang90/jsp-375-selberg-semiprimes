import SelbergSemiprimes.Variance
import SelbergSemiprimes.PrimePowers

open Finset Set MeasureTheory
open scoped ENNReal BigOperators

namespace JSP375

private theorem window_eq_theta {T b h : ℝ} (hb : 0 ≤ b) (hh : 0 ≤ h) (ht : b + h ≤ T) :
    thetaIncrement (primesThrough T) b h = Chebyshev.theta (b + h) - Chebyshev.theta b := by
  classical
  let A (y : ℝ) := (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime
  have spec (y : ℝ) (hy : 0 ≤ y) (p : ℕ) : p ∈ A y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
    simp only [A, Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff hy]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.pos, h.2⟩, h.1⟩⟩
  have bh : 0 ≤ b + h := by linarith
  have sub : A b ⊆ A (b + h) := by
    intro p hp; exact (spec _ bh p).2 ⟨((spec _ hb p).1 hp).1, by linarith [((spec _ hb p).1 hp).2]⟩
  have eq : window (primesThrough T) b h = A (b + h) \ A b := by
    ext p
    simp only [window, primesThrough, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
      Nat.le_floor_iff (bh.trans ht), Finset.mem_sdiff, spec _ bh, spec _ hb]
    constructor
    · rintro ⟨⟨_, hp⟩, pl, pu⟩
      exact ⟨⟨hp, pu⟩, fun e => pl.not_ge e.2⟩
    · rintro ⟨⟨hp, pu⟩, he⟩
      exact ⟨⟨pu.trans ht, hp⟩, lt_of_not_ge (fun e => he ⟨hp, e⟩), pu⟩
  rw [thetaIncrement, eq, Finset.sum_sdiff_eq_sub sub]
  rfl

private theorem integral_floor (N : ℕ) (f : ℕ → ℝ≥0∞) :
    (∫⁻ t in Set.Ico (0 : ℝ) N, f ⌊t⌋₊) = ∑ m ∈ range N, f m := by
  induction N with
  | zero => simp
  | succ N ih =>
    have eq : Set.Ico (0 : ℝ) ((N : ℝ) + 1) = Set.Ico (0 : ℝ) N ∪ Set.Ico (N : ℝ) (N + 1) := by
      ext t; simp only [Set.mem_Ico, Set.mem_union]; constructor
      · rintro ⟨h0, ht⟩
        exact (lt_or_ge t (N : ℝ)).elim (fun h => Or.inl ⟨h0, h⟩) (fun h => Or.inr ⟨h, ht⟩)
      · rintro (⟨h0, ht⟩ | ⟨hl, ht⟩)
        · exact ⟨h0, by linarith⟩
        · exact ⟨(Nat.cast_nonneg N).trans hl, ht⟩
    have dis : Disjoint (Set.Ico (0:ℝ) N) (Set.Ico N (N + 1)) :=
      Set.disjoint_left.mpr (fun _ a b => a.2.not_ge b.1)
    rw [Nat.cast_succ, eq, lintegral_union measurableSet_Ico dis, ih, Finset.sum_range_succ]
    congr 1
    calc
      _ = ∫⁻ _t in Set.Ico (N : ℝ) (N+1), f N := setLIntegral_congr_fun measurableSet_Ico
        (fun t ht => congrArg f ((Nat.floor_eq_iff ((Nat.cast_nonneg N).trans ht.1)).2 ht))
      _ = _ := by simp [Real.volume_Ico]

private theorem between_sq {a b z : ℝ} (lo : a - 1 ≤ z) (hi : z ≤ b + 1) :
    z ^ 2 ≤ 2 * (a ^ 2 + b ^ 2 + 1) := by
  by_cases hz : 0 ≤ z
  · nlinarith [pow_le_pow_left₀ hz hi 2, sq_nonneg (b - 1), sq_nonneg a]
  · have h := pow_le_pow_left₀ (show 0 ≤ -z by linarith) (show -z ≤ 1 - a by linarith) 2
    nlinarith [sq_nonneg (a + 1), sq_nonneg b]

private theorem sandwich {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    (Chebyshev.theta (t + h) - Chebyshev.theta t - h) ^ 2 ≤
      2 * (incrementError Chebyshev.theta ⌊t⌋₊ ⌊h⌋₊ ^ 2 +
        incrementError Chebyshev.theta ⌊t⌋₊ (⌊h⌋₊ + 1) ^ 2 + 1) := by
  let k := ⌊t⌋₊
  let L := ⌊h⌋₊
  have tf : (k : ℝ) ≤ t := Nat.floor_le ht
  have hf : (L : ℝ) ≤ h := Nat.floor_le hh
  have th : t < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hl : h < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have val : Chebyshev.theta (k : ℝ) = Chebyshev.theta t := by simp [Chebyshev.theta, k]
  have floor_end : (⌊t+h⌋₊ : ℝ) ≤ (k : ℝ) + L + 1 := by
    have bound : ⌊t+h⌋₊ < k + L + 2 := by
      apply (Nat.floor_lt (by positivity)).2
      push_cast; linarith
    exact_mod_cast (show ⌊t+h⌋₊ ≤ k + L + 1 by omega)
  have val_end : Chebyshev.theta (⌊t+h⌋₊ : ℝ) = Chebyshev.theta (t+h) := by simp [Chebyshev.theta]
  have lo := Chebyshev.theta_mono (show (k : ℝ) + L ≤ t + h by linarith)
  have hi := Chebyshev.theta_mono floor_end
  rw [val_end] at hi
  change _ ≤ 2 * (incrementError Chebyshev.theta k L ^ 2 + incrementError Chebyshev.theta k (L+1) ^ 2 + 1)
  apply between_sq
  · unfold incrementError; rw [val]; linarith
  · unfold incrementError; rw [val]; push_cast; rw [← add_assoc]; linarith

theorem real_variance_of_discrete {K : ℝ} (hK : 0 < K)
    (discrete : ∀ N L : ℕ, 1 ≤ L → L ≤ N →
      (∑ m ∈ range N, incrementError Chebyshev.theta m L ^ 2) ≤
        K * N * L * (Real.log N + 3) ^ 2) :
    SelbergThetaEstimate := by
  classical
  refine ⟨400 * K + 20, by positivity, Real.exp 4, ?_⟩
  intro X hX h h1 hmax
  have x4 : 4 ≤ X := le_trans (by linarith [Real.add_one_le_exp (4 : ℝ)]) hX
  have x0 : 0 < X := by linarith
  have log4 : 4 ≤ Real.log X := (Real.le_log_iff_exp_le x0).2 hX
  have h0 : 0 ≤ h := by linarith
  let N := ⌊3 * X⌋₊ + 1
  let L := ⌊h⌋₊
  have nGT : 3 * X < (N : ℝ) := by simpa [N] using Nat.lt_floor_add_one (3 * X)
  have nLE : (N : ℝ) ≤ 4 * X := by dsimp [N]; push_cast; linarith [Nat.floor_le (show 0 ≤ 3 * X by positivity)]
  have lGE : 1 ≤ L := (Nat.le_floor_iff h0).2 (by simpa using h1)
  have lLE : (L : ℝ) ≤ h := Nat.floor_le h0
  have lN' : (L : ℝ) + 1 ≤ (N : ℝ) := by linarith
  have lN : L + 1 ≤ N := by exact_mod_cast lN'
  let e (m j : ℕ) := incrementError Chebyshev.theta m j ^ 2
  let f (m : ℕ) := 2 * (e m L + e m (L+1) + 1)
  have f0 (m : ℕ) : 0 ≤ f m := by dsimp [f, e]; positivity
  have compare : variance X h ≤ ENNReal.ofReal (∑ m ∈ range N, f m) := by
    calc
      _ ≤ ∫⁻ t in Set.Ioc (X / 2) (3 * X), ENNReal.ofReal (f ⌊t⌋₊) :=
        setLIntegral_mono' measurableSet_Ioc (fun t ht => by
          apply ENNReal.ofReal_le_ofReal
          rw [window_eq_theta (by linarith [ht.1]) h0 (by linarith [ht.2])]
          exact sandwich (by linarith [ht.1]) h0)
      _ ≤ ∫⁻ t in Set.Ico (0 : ℝ) N, ENNReal.ofReal (f ⌊t⌋₊) :=
        lintegral_mono_set (fun t ht => ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 nGT⟩)
      _ = _ := by
        rw [integral_floor N (fun m => ENNReal.ofReal (f m)), ENNReal.ofReal_sum_of_nonneg (fun m _ => f0 m)]
  have logn : Real.log N + 3 ≤ 3 * Real.log X := by
    have qa := Real.log_le_log (by linarith : (0:ℝ) < N) nLE
    rw [Real.log_mul (by norm_num) x0.ne'] at qa
    linarith [Real.log_le_log (by norm_num : (0:ℝ) < 4) x4]
  have lognpos := Real.log_nonneg (show (1:ℝ) ≤ N by linarith)
  have E (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (hjh : (j : ℝ) ≤ 2 * h) :
      (∑ m ∈ range N, e m j) ≤ 72 * K * X * h * (Real.log X) ^ 2 := by
    apply (discrete N j hj hjN).trans
    calc
      _ ≤ K * (4 * X) * (2 * h) * (3 * Real.log X) ^ 2 := by gcongr
      _ = _ := by ring
  have e0 := E L lGE (by omega) (by linarith)
  have e1 := E (L+1) (by omega) lN (by push_cast; linarith)
  have base : (N : ℝ) ≤ 4 * X * h * (Real.log X) ^ 2 := by
    exact nLE.trans (le_trans (le_mul_of_one_le_right (by positivity) h1)
      (le_mul_of_one_le_right (by positivity) (by nlinarith [sq_nonneg (Real.log X - 1)])))
  apply compare.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [f, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  nlinarith [mul_nonneg (by positivity : 0 ≤ K * X * h) (sq_nonneg (Real.log X)),
    mul_nonneg (by positivity : 0 ≤ X * h) (sq_nonneg (Real.log X))]

end JSP375
