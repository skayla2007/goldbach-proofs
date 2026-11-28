import Mathlib
import Conjectures.Cuts.Refute381823bab84c203ff962aeb2
import Conjectures.Goldbach.ExplicitPsiSubTheta
import Conjectures.Goldbach.MertensAbelBridge

open Finset hiding tsum_subtype
open Filter MeasureTheory Asymptotics Real
open scoped Topology Interval

-- child 1 zh: 筛法范围的切比雪夫 ψ 误差：10^6 ≤ x ≤ 10^10 时不超过 0.94√x。
-- child 1 en: Certify the Chebyshev psi error at most 0.94 sqrt(x) on [10^6, 10^10].
-- child 2 zh: Büthe 有限大区间的 ψ 误差：10^10 ≤ x ≤ 10^19 时不超过 0.94√x。
-- child 2 en: Certify the Chebyshev psi error at most 0.94 sqrt(x) on [10^10, 10^19].
-- child 3 zh: 过渡段的显式 ψ 误差：x ≥ 10^19 且 log x ≤ 3000 时不超过 8.75e-7 x/log x。
-- child 3 en: Bound the psi error by 8.75e-7 x/log x for x >= 10^19 and log x <= 3000.
-- child 4 zh: 无穷远段的显式 θ 误差：x > 2 且 log x ≥ 3000 时不超过 9e-7 x/log x。
-- child 4 en: Bound the theta error by 9e-7 x/log x for x > 2 and log x >= 3000.

set_option maxHeartbeats 6000000 in
theorem Conjectures.Cuts.Cut6572343416ef8333dfbf78a2
    (hSieve : ∀ x : ℝ, (10 : ℝ)^6 ≤ x → x ≤ (10 : ℝ)^10 →
      |Chebyshev.psi x - x| ≤ (0.94 : ℝ) * Real.sqrt x)
    (hFinite : ∀ x : ℝ, (10 : ℝ)^10 ≤ x → x ≤ (10 : ℝ)^19 →
      |Chebyshev.psi x - x| ≤ (0.94 : ℝ) * Real.sqrt x)
    (hTable : ∀ x : ℝ, (10 : ℝ)^19 ≤ x → Real.log x ≤ 3000 →
      |Chebyshev.psi x - x| ≤ (8.75e-7 : ℝ) * x / Real.log x)
    (hTail : ∀ x > (2 : ℝ), (3000 : ℝ) ≤ Real.log x →
      |Chebyshev.theta x - x| ≤ (9e-7 : ℝ) * x / Real.log x) :
    (let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); ∀ x : ℝ, (10 : ℝ) ^ 12 < x → Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + (6.836e-6 : ℝ) / Real.log x) := by
  let FinitePsiEstimate : Prop :=
    ∀ t : ℝ, (10 : ℝ)^6 ≤ t → t ≤ (10 : ℝ)^19 → |Chebyshev.psi t - t| ≤ (0.94 : ℝ) * √t

  have le_root_of_pow_le {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
      (n : ℕ) (hn : 0 < n) (h : a ^ n ≤ x) :
      a ≤ x ^ ((n : ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos ha hx (by exact_mod_cast hn)).2
    rwa [Real.rpow_natCast]

  have root_le_self {x : ℝ} (hx : 1 ≤ x) {a : ℝ} (ha : a ≤ 1) :
      x ^ a ≤ x := by
    calc
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx ha
      _ = _ := Real.rpow_one x

  have sqrt_le_div_of_sq_le {a x : ℝ} (ha : 0 < a) (hx : a^2 ≤ x) :
      √x ≤ x / a := by
    have hx0 : 0 ≤ x := (sq_nonneg a).trans hx
    have hs : a ≤ √x := by
      have h := Real.sqrt_le_sqrt hx
      rwa [Real.sqrt_sq_eq_abs, abs_of_pos ha] at h
    apply (le_div_iff₀ ha).2
    exact (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg x)).trans_eq (Real.mul_self_sqrt hx0)

  have psi_near_sqrt (h : FinitePsiEstimate) {t : ℝ}
      (ht : (10 : ℝ)^6 ≤ t) (ht' : t ≤ (10 : ℝ)^19) :
      (0.999 : ℝ) * t ≤ Chebyshev.psi t ∧ Chebyshev.psi t ≤ (1.001 : ℝ) * t := by
    have hs := sqrt_le_div_of_sq_le (show (0 : ℝ) < 1000 by norm_num)
      ((by norm_num : (1000 : ℝ)^2 ≤ (10 : ℝ)^6).trans ht)
    obtain ⟨hlo, hhi⟩ := abs_le.mp (h t ht ht')
    constructor <;> linarith

  have log_four_le : Real.log 4 ≤ (1.387 : ℝ) := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]

  have psi_le_five_point_four {t : ℝ} (ht : 0 ≤ t) :
      Chebyshev.psi t ≤ (5.4 : ℝ) * t := by
    have h := Chebyshev.psi_le_const_mul_self ht
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith [log_four_le]) ht)

  have finite_theta_from_psi (h : FinitePsiEstimate) {x : ℝ}
      (hx : (10 : ℝ)^12 ≤ x) (hx' : x ≤ (10 : ℝ)^19) :
      0 ≤ x - Chebyshev.theta x ∧ x - Chebyshev.theta x ≤ 2 * √x := by
    have hx2 : 2 ≤ x := (by norm_num : (2 : ℝ) ≤ (10 : ℝ)^12).trans hx
    have hx1 : 1 ≤ x := by linarith
    have hxp : 0 < x := by linarith
    have hroot2 : x ^ (2 : ℝ)⁻¹ = √x := by
      rw [Real.sqrt_eq_rpow, one_div]
    have hbigSq : (10 : ℝ)^6 ≤ √x := by
      have hs := Real.sqrt_le_sqrt hx
      have h : Real.sqrt ((10 : ℝ)^12) = (10 : ℝ)^6 := by
        rw [show (10 : ℝ)^12 = ((10 : ℝ)^6)^2 by norm_num, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by positivity)]
      rwa [h] at hs
    have hsx : √x ≤ x := by
      rw [← hroot2]
      exact root_le_self hx1 (by norm_num)
    have h3 : x ^ (3 : ℝ)⁻¹ ≤ (0.01 : ℝ) * √x := by
      have h6 : 100 ≤ x ^ (6 : ℝ)⁻¹ :=
        le_root_of_pow_le (by norm_num) hxp.le 6 (by decide)
          ((by norm_num : (100 : ℝ)^6 ≤ (10 : ℝ)^12).trans hx)
      have hprod : x ^ (3 : ℝ)⁻¹ * x ^ (6 : ℝ)⁻¹ = √x := by
        rw [← Real.rpow_add hxp, ← hroot2]
        congr 1
        norm_num
      have hp := mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hxp.le (3 : ℝ)⁻¹)
      rw [hprod] at hp
      linarith
    have h5 : x ^ (5 : ℝ)⁻¹ ≤ (0.0005 : ℝ) * √x := by
      have hp3 : (2000 : ℝ)^10 ≤ x^3 := by
        calc
          _ ≤ (((10 : ℝ)^12)^3) := by norm_num
          _ ≤ _ := by gcongr
      have h310 : (2000 : ℝ) ≤ x ^ (3 / 10 : ℝ) := by
        have hR := le_root_of_pow_le (by norm_num) (by positivity) 10 (by decide) hp3
        rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hxp.le] at hR
        norm_num at hR ⊢
        exact hR
      have hprod : x ^ (5 : ℝ)⁻¹ * x ^ (3 / 10 : ℝ) = √x := by
        rw [← Real.rpow_add hxp, ← hroot2]
        congr 1
        norm_num
      have hp := mul_le_mul_of_nonneg_left h310 (Real.rpow_nonneg hxp.le (5 : ℝ)⁻¹)
      rw [hprod] at hp
      linarith
    have hψ2 := psi_near_sqrt h hbigSq (hsx.trans hx')
    have hψ3 := psi_le_five_point_four (Real.rpow_nonneg hxp.le (3 : ℝ)⁻¹)
    have hψ5 := psi_le_five_point_four (Real.rpow_nonneg hxp.le (5 : ℝ)⁻¹)
    have hlo := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hxp.le
    have hhi := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
    rw [hroot2] at hlo hhi
    have hψ7 := Chebyshev.psi_nonneg (x ^ (7 : ℝ)⁻¹)
    have hψ := abs_le.mp (h x ((by norm_num : (10 : ℝ)^6 ≤ (10 : ℝ)^12).trans hx) hx')
    constructor
    · linarith [hψ2.1, hψ.2, Chebyshev.psi_nonneg (x ^ (3 : ℝ)⁻¹), Real.sqrt_nonneg x]
    · linarith [hψ2.2, hψ.1]

  have log_cutoff_bounds :
      40 ≤ Real.log ((10 : ℝ)^19) ∧ Real.log ((10 : ℝ)^19) ≤ 44 := by
    rw [Real.log_pow, Real.log_ten_eq]
    norm_num
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_five_gt_d9,
      Real.log_two_lt_d9, Real.log_five_lt_d9]

  have log_div_sqrt_le {x : ℝ} (hx : (10 : ℝ)^19 ≤ x) :
      Real.log x / √x ≤ (1.5e-8 : ℝ) := by
    have hbase : Real.exp 2 ≤ (10 : ℝ)^19 :=
      (Real.le_log_iff_exp_le (by positivity)).1 (by linarith [log_cutoff_bounds.1])
    have hmono := Real.log_div_sqrt_antitoneOn
      (show (10 : ℝ)^19 ∈ Set.Ici (Real.exp 2) from hbase)
      (show x ∈ Set.Ici (Real.exp 2) from hbase.trans hx) hx
    have hden : (3e9 : ℝ) ≤ √((10 : ℝ)^19) := by
      have h := Real.sqrt_le_sqrt (by norm_num : (3e9 : ℝ)^2 ≤ (10 : ℝ)^19)
      rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)] at h
    refine hmono.trans ((div_le_iff₀ (by positivity)).2 (log_cutoff_bounds.2.trans ?_))
    exact (show (44 : ℝ) ≤ (1.5e-8 : ℝ) * 3e9 by norm_num).trans
      (mul_le_mul_of_nonneg_left hden (by norm_num))

  have log_div_sixth_root_le {x : ℝ} (hx : (10 : ℝ)^19 ≤ x) :
      Real.log x / x ^ (1 / 6 : ℝ) ≤ (0.044 : ℝ) := by
    have hbase : Real.exp ((1 / 6 : ℝ)⁻¹) ≤ (10 : ℝ)^19 := by
      rw [show (1 / 6 : ℝ)⁻¹ = 6 by norm_num]
      exact (Real.le_log_iff_exp_le (by positivity)).1
        ((by norm_num : (6 : ℝ) ≤ 40).trans log_cutoff_bounds.1)
    have hmono := Real.log_div_self_rpow_antitoneOn (by norm_num : 0 < (1 / 6 : ℝ))
      (show (10 : ℝ)^19 ∈ Set.Ici (Real.exp ((1 / 6 : ℝ)⁻¹)) from hbase)
      (show x ∈ Set.Ici (Real.exp ((1 / 6 : ℝ)⁻¹)) from hbase.trans hx) hx
    have hden : (1000 : ℝ) ≤ ((10 : ℝ)^19) ^ (1 / 6 : ℝ) := by
      rw [one_div]
      exact le_root_of_pow_le (by norm_num) (by norm_num) 6 (by decide) (by norm_num)
    refine hmono.trans ((div_le_iff₀ (by positivity)).2 (log_cutoff_bounds.2.trans ?_))
    exact (show (44 : ℝ) ≤ (0.044 : ℝ) * 1000 by norm_num).trans
      (mul_le_mul_of_nonneg_left hden (by norm_num))

  have large_prime_power_correction {x : ℝ} (hx : (10 : ℝ)^19 ≤ x) :
      0 ≤ Chebyshev.psi x - Chebyshev.theta x ∧
        Chebyshev.psi x - Chebyshev.theta x ≤ (2.25e-8 : ℝ) * x / Real.log x := by
    have hx2 : 2 ≤ x := (by norm_num : (2 : ℝ) ≤ (10 : ℝ)^19).trans hx
    have hx0 : 0 < x := by linarith
    have hlog := Real.log_pos (show 1 < x by linarith)
    have hs : 0 < √x := Real.sqrt_pos.2 hx0
    have hratio := (div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)).1 (log_div_sixth_root_le hx)
    have hprod : x ^ (1 / 3 : ℝ) * x ^ (1 / 6 : ℝ) = √x := by
      rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]
      congr 1
      norm_num
    have hc := mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hx0.le (1 / 3))
    have hc' : x ^ (1 / 3 : ℝ) * Real.log x ≤ (0.044 : ℝ) * √x := by
      calc
        _ ≤ x ^ (1 / 3 : ℝ) * ((0.044 : ℝ) * x ^ (1 / 6 : ℝ)) := hc
        _ = _ := by rw [← hprod]; ring
    obtain ⟨hn, hmain⟩ := Conjectures.Goldbach.ExplicitPsiSubTheta_aux.bound hx2
    have hsmall : Chebyshev.psi x - Chebyshev.theta x ≤ (1.5 : ℝ) * √x := by
      linarith [mul_le_mul_of_nonneg_right log_four_le hs.le]
    refine ⟨hn, hsmall.trans ((le_div_iff₀ hlog).2 ?_)⟩
    have h := (div_le_iff₀ hs).1 (log_div_sqrt_le hx)
    have h' := mul_le_mul_of_nonneg_left h hs.le
    have hs2 := Real.sq_sqrt hx0.le
    nlinarith [mul_le_mul_of_nonneg_left h' (show (0 : ℝ) ≤ 1.5 by norm_num)]

  have large_theta_from_psi {x : ℝ} (hx : (10 : ℝ)^19 ≤ x)
      (h : |Chebyshev.psi x - x| ≤ (8.75e-7 : ℝ) * x / Real.log x) :
      |Chebyshev.theta x - x| ≤ (9e-7 : ℝ) * x / Real.log x := by
    have hx1 : 1 < x := (by norm_num : (1 : ℝ) < (10 : ℝ)^19).trans_le hx
    have hl := Real.log_pos hx1
    obtain ⟨hp, hq⟩ := large_prime_power_correction hx
    calc
      _ = |(Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x)| := by congr 1; ring
      _ ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := abs_sub _ _
      _ ≤ (8.75e-7 : ℝ) * x / Real.log x + (2.25e-8 : ℝ) * x / Real.log x :=
        by exact add_le_add h (by rwa [abs_of_nonneg hp])
      _ ≤ _ := by
        have hq : 0 ≤ x / Real.log x := by positivity
        simp only [mul_div_assoc]
        linarith






  let theta := GoldbachMertensSum.theta
  let w := GoldbachMertensSum.w
  let g := GoldbachMertensSum.g

  have theta_eq_chebyshev (x : ℝ) : theta x = Chebyshev.theta x := by
    unfold theta GoldbachMertensSum.theta Chebyshev.theta
    have hs : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by
      ext n
      simp only [mem_Icc, mem_Ioc]
      omega
    rw [hs]

  let sumInclusive (x : ℝ) : ℝ :=
    ∑ p ∈ (Ioc 0 ⌊x⌋₊).filter Nat.Prime, 1 / (p : ℝ)

  let sumStrict (x : ℝ) : ℝ :=
    ∑ p ∈ (range (Nat.ceil x)).filter Nat.Prime, 1 / (p : ℝ)

  let constant : ℝ :=
    Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))

  have constant_eq : constant = Mertens.M := by
    rw [Mertens.M.eq]
    unfold constant
    have h := Mertens.γ.eq_eulerMascheroni
    rw [h]
    congr 1
    let primes : Set ℕ := {p | Nat.Prime p}
    let term (p : ℕ) : ℝ := Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)
    let e : Nat.Primes ≃ primes :=
      { toFun := fun p => ⟨p.1, p.2⟩
        invFun := fun p => ⟨p.1, p.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      (∑' p : Nat.Primes, term p.1) = ∑' p : primes, term p.1 :=
        e.tsum_eq (fun p : primes => term p.1)
      _ = ∑' p : ℕ, primes.indicator term p := tsum_subtype primes term
      _ = _ := by
        apply tsum_congr
        intro p
        by_cases hp : Nat.Prime p <;> simp [primes, term, Set.indicator, hp]

  let err (x : ℝ) : ℝ := sumInclusive x - Real.log (Real.log x) - constant

  have err_tendsto : Tendsto err atTop (𝓝 0) := by
    unfold err sumInclusive
    rw [constant_eq]
    exact (isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'

  have w_pos {t : ℝ} (ht : 2 ≤ t) : 0 < w t := by
    have hlog := Real.log_pos (show 1 < t by linarith)
    unfold w GoldbachMertensSum.w
    positivity

  have g_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ g t := by
    have hlog := Real.log_pos (show 1 < t by linarith)
    unfold g GoldbachMertensSum.g
    positivity

  let edge (x : ℝ) : ℝ := (theta x - x) * w x
  let density (x : ℝ) : ℝ := (x - theta x) * g x

  have density_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable density volume a b := by
    unfold density
    simp only [sub_mul]
    exact (GoldbachMertensSmooth.baseline_integrable ha hab).sub
      (GoldbachMertensSum.theta_mul_g_integrable ha hab)

  have err_eq_edge_add_integral {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
      err a = err b + edge a - edge b + ∫ t in a..b, density t := by
    have hIncl :
        sumInclusive b - sumInclusive a =
          ∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, 1/(p:ℝ) := by
      unfold sumInclusive
      have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
      have hu : (Ioc 0 ⌊a⌋₊).filter Nat.Prime ∪
          (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime = (Ioc 0 ⌊b⌋₊).filter Nat.Prime := by
        ext p
        by_cases hp : Nat.Prime p
        · simp only [mem_union, mem_filter, mem_Ioc, hp, and_true]
          omega
        · simp [hp]
      have hd : Disjoint ((Ioc 0 ⌊a⌋₊).filter Nat.Prime)
          ((Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime) := by
        rw [Finset.disjoint_left]
        intro p hp hq
        simp only [mem_filter, mem_Ioc] at hp hq
        omega
      rw [← hu, sum_union hd]
      ring
    have haForm := GoldbachMertensSum.abel_reciprocal_sum ha hab
    have hbase := GoldbachMertensSmooth.baseline ha hab
    change b * w b - a * w a + (∫ t in a..b, t * g t) =
      Real.log (Real.log b) - Real.log (Real.log a) at hbase
    rw [← hIncl] at haForm
    unfold density edge err
    simp only [sub_mul]
    have hid : IntervalIntegrable (fun t => t * g t) volume a b :=
      GoldbachMertensSmooth.baseline_integrable ha hab
    have htheta : IntervalIntegrable (fun t => theta t * g t) volume a b :=
      GoldbachMertensSum.theta_mul_g_integrable ha hab
    rw [intervalIntegral.integral_sub hid htheta]
    change sumInclusive b - sumInclusive a =
      theta b * w b - theta a * w a + ∫ t in a..b, theta t * g t at haForm
    linarith

  have sumInclusive_eventually_eq_sumStrict {x : ℝ} (hx : 1 < x) :
      ∀ᶠ t in 𝓝[<] x, sumInclusive t = sumStrict x := by
    let n := Nat.ceil x
    have hn : 0 < n := Nat.ceil_pos.mpr (by linarith)
    have hpred : ((n - 1 : ℕ) : ℝ) < x :=
      Nat.lt_ceil.mp (by omega : n - 1 < Nat.ceil x)
    have hevent : ∀ᶠ t in 𝓝[<] x, ((n - 1 : ℕ) : ℝ) < t :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hpred)
    have hleft : ∀ᶠ t in 𝓝[<] x, t ∈ Set.Iio x := self_mem_nhdsWithin
    filter_upwards [hevent, hleft] with t ht ht'
    have hfloor : ⌊t⌋₊ = n - 1 := by
      have hlo : n - 1 ≤ ⌊t⌋₊ :=
        (Nat.le_floor_iff (by linarith [show (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) by positivity])).2 ht.le
      have hup : ⌊t⌋₊ < n := by
        apply Nat.floor_lt (by linarith [show (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) by positivity]) |>.2
        exact lt_of_lt_of_le ht' (Nat.le_ceil x)
      omega
    unfold sumInclusive sumStrict
    congr 1
    ext p
    by_cases hp : Nat.Prime p
    · have hp₀ := hp.pos
      simp only [mem_filter, mem_Ioc, mem_range, hfloor, hp, and_true]
      change (0 < p ∧ p ≤ n - 1) ↔ p < n
      omega
    · simp [hp]

  have strict_of_inclusive
      (h : ∀ x : ℝ, (10 : ℝ)^12 < x →
        Real.log (Real.log x) + constant - (2.964e-6 : ℝ) / Real.log x ≤ sumInclusive x ∧
        sumInclusive x ≤ Real.log (Real.log x) + constant + (6.836e-6 : ℝ) / Real.log x) :
      ∀ x : ℝ, (10 : ℝ)^12 < x →
        Real.log (Real.log x) + constant - (2.964e-6 : ℝ) / Real.log x ≤ sumStrict x ∧
        sumStrict x ≤ Real.log (Real.log x) + constant + (6.836e-6 : ℝ) / Real.log x := by
    intro x hx
    have hx1 : 1 < x := by linarith [show (1 : ℝ) < (10 : ℝ)^12 by norm_num]
    have hne : x ≠ 0 := by linarith
    have hl := Real.log_pos hx1
    have hlog : ContinuousAt Real.log x := Real.continuousAt_log hne
    have hloglog : ContinuousAt (fun t => Real.log (Real.log t)) x :=
      (Real.continuousAt_log hl.ne').comp hlog
    have hlow : ContinuousAt (fun t : ℝ => Real.log (Real.log t) + constant -
          (2.964e-6 : ℝ) / Real.log t) x :=
      (hloglog.add continuousAt_const).sub (continuousAt_const.div hlog hl.ne')
    have hupp : ContinuousAt (fun t : ℝ => Real.log (Real.log t) + constant +
          (6.836e-6 : ℝ) / Real.log t) x :=
      (hloglog.add continuousAt_const).add (continuousAt_const.div hlog hl.ne')
    have he : ∀ᶠ t in 𝓝[<] x, (10 : ℝ)^12 < t :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hx)
    have : (𝓝[<] x).NeBot := nhdsLT_neBot_of_exists_lt ⟨(0 : ℝ), by linarith⟩
    have hsEq := sumInclusive_eventually_eq_sumStrict hx1
    constructor
    · refine le_of_tendsto_of_tendsto (b := 𝓝[<] x)
        (hlow.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds ?_
      filter_upwards [he, hsEq] with t ht hEq
      exact (h t ht).1.trans_eq hEq
    · refine le_of_tendsto_of_tendsto (b := 𝓝[<] x) tendsto_const_nhds
        (hupp.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [he, hsEq] with t ht hEq
      exact hEq.symm.trans_le (h t ht).2

  let start : ℝ := (10 : ℝ)^12
  let split : ℝ := (10 : ℝ)^19

  have start_le_split : start ≤ split := by norm_num [start, split]
  have two_le_start : 2 ≤ start := by norm_num [start]

  have log_ge_24 {x : ℝ} (hx : start ≤ x) : 24 ≤ Real.log x := by
    have h2 : (2 : ℝ)^36 ≤ x := (by norm_num [start] : (2 : ℝ)^36 ≤ start).trans hx
    have h := Real.log_le_log (by positivity : 0 < (2 : ℝ)^36) h2
    rw [Real.log_pow] at h
    norm_num at h
    linarith [Real.log_two_gt_d9]

  have inv_log_le {x : ℝ} (hx : start ≤ x) :
      1 / Real.log x ≤ 1 / 24 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact log_ge_24 hx

  have inv_sqrt_le {x : ℝ} (hx : start ≤ x) :
      (Real.sqrt x)⁻¹ ≤ (1e-6 : ℝ) := by
    have hs : (1000000 : ℝ) ≤ Real.sqrt x := by
      have h := Real.sqrt_le_sqrt hx
      rw [show start = (1000000 : ℝ)^2 by norm_num [start],
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)] at h
      exact h
    rw [inv_eq_one_div]
    calc
      _ ≤ 1 / (1000000 : ℝ) := one_div_le_one_div_of_le (by norm_num) hs
      _ = _ := by norm_num

  let MidThetaBound : Prop :=
    ∀ t : ℝ, start ≤ t → t ≤ split →
      0 ≤ t - Chebyshev.theta t ∧ t - Chebyshev.theta t ≤ 2 * Real.sqrt t

  let LargeThetaBound : Prop :=
    ∀ t : ℝ, split ≤ t → |Chebyshev.theta t - t| ≤ (9e-7 : ℝ) * t / Real.log t

  have mid_edge (h : MidThetaBound) {t : ℝ} (ht : start ≤ t) (ht' : t ≤ split) :
      -(2e-6 : ℝ) / Real.log t ≤ edge t ∧ edge t ≤ 0 := by
    have ht₂ := two_le_start.trans ht
    have hlog := Real.log_pos (show 1 < t by linarith)
    have ht₀ : 0 < t := by linarith
    have hs := Real.sqrt_pos.2 ht₀
    have hs2 := Real.sq_sqrt ht₀.le
    have he := h t ht ht'
    rw [← theta_eq_chebyshev] at he
    have hw := (w_pos ht₂).le
    constructor
    · calc
        -(2e-6 : ℝ) / Real.log t ≤ -(2 * (Real.sqrt t)⁻¹) / Real.log t := by
          apply div_le_div_of_nonneg_right _ hlog.le
          linarith [inv_sqrt_le ht]
        _ = -(2 * Real.sqrt t) * w t := by
          unfold w GoldbachMertensSum.w
          field_simp [hlog.ne', ht₀.ne', hs.ne']
          nlinarith
        _ ≤ edge t := mul_le_mul_of_nonneg_right (by linarith [he.2]) hw
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [he.1]) hw

  have large_edge (h : LargeThetaBound) {t : ℝ} (ht : split ≤ t) :
      |edge t| ≤ (9e-7 : ℝ) / Real.log t ^ 2 := by
    have ht₂ := two_le_start.trans (start_le_split.trans ht)
    have ht₀ : 0 < t := by linarith
    have hl := Real.log_pos (show 1 < t by linarith)
    unfold edge
    rw [abs_mul, abs_of_nonneg (w_pos ht₂).le]
    calc
      _ ≤ (9e-7 : ℝ) * t / Real.log t * w t :=
        mul_le_mul_of_nonneg_right (by simpa only [theta_eq_chebyshev] using h t ht)
          (w_pos ht₂).le
      _ = _ := by
        unfold w GoldbachMertensSum.w
        field_simp [ht₀.ne', hl.ne']

  let tailKernel (t : ℝ) : ℝ := 1 / (t * Real.log t ^ 2)
  let midKernel (t : ℝ) : ℝ := 1 / (2 * t * Real.sqrt t)

  have tailKernel_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ tailKernel t := by
    unfold tailKernel
    positivity

  have midKernel_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ midKernel t := by
    unfold midKernel
    positivity

  have tailKernel_integral {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
      (∫ t in a..b, tailKernel t) ≤ 1 / Real.log a := by
    have hpos (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t ∧ 0 < Real.log t := by
      rw [Set.uIcc_of_le hab] at ht
      have ht₂ := ha.trans ht.1
      exact ⟨by linarith, Real.log_pos (by linarith)⟩
    have hInt : IntervalIntegrable tailKernel volume a b := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      obtain ⟨ht₀, hl⟩ := hpos t ht
      unfold tailKernel
      have hd : ContinuousAt (fun y : ℝ => y * Real.log y ^ 2) t :=
        continuousAt_id.mul ((Real.continuousAt_log ht₀.ne').pow 2)
      exact (continuousAt_const.div hd
        (mul_ne_zero ht₀.ne' (pow_ne_zero _ hl.ne'))).continuousWithinAt
    have hDeriv (t : ℝ) (ht : t ∈ Set.uIcc a b) :
        HasDerivAt (fun s => -(Real.log s)⁻¹) (tailKernel t) t := by
      obtain ⟨ht₀, hl⟩ := hpos t ht
      convert ((Real.hasDerivAt_log ht₀.ne').inv hl.ne').neg using 1
      unfold tailKernel
      field_simp [ht₀.ne', hl.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hInt]
    have hb : 2 ≤ b := ha.trans hab
    have hlog := Real.log_pos (show 1 < b by linarith)
    simp only [one_div]
    linarith [inv_nonneg.mpr hlog.le]

  have midKernel_integral {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
      (∫ t in a..b, midKernel t) ≤ (Real.sqrt a)⁻¹ := by
    have hpos (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t := by
      rw [Set.uIcc_of_le hab] at ht
      linarith [ha.trans ht.1]
    have hInt : IntervalIntegrable midKernel volume a b := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      have ht₀ := hpos t ht
      have hs := Real.sqrt_pos.2 ht₀
      unfold midKernel
      have hd : ContinuousAt (fun y : ℝ => 2 * y * Real.sqrt y) t :=
        ((continuousAt_const (y := (2 : ℝ))).mul continuousAt_id).mul
          Real.continuous_sqrt.continuousAt
      exact (continuousAt_const.div hd
        (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ht₀.ne') hs.ne')).continuousWithinAt
    have hDeriv (t : ℝ) (ht : t ∈ Set.uIcc a b) :
        HasDerivAt (fun s => -(Real.sqrt s)⁻¹) (midKernel t) t := by
      have ht₀ := hpos t ht
      have hs := Real.sqrt_pos.2 ht₀
      have hs2 := Real.sq_sqrt ht₀.le
      convert ((Real.hasDerivAt_sqrt ht₀.ne').inv hs.ne').neg using 1
      unfold midKernel
      field_simp [ht₀.ne', hs.ne']
      nlinarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hInt]
    linarith [inv_nonneg.mpr (Real.sqrt_nonneg b)]

  have tail_density (h : LargeThetaBound) {t : ℝ} (ht : split ≤ t) :
      |density t| ≤ (9.5e-7 : ℝ) * tailKernel t := by
    have htStart := start_le_split.trans ht
    have ht₂ := two_le_start.trans htStart
    have ht₀ : 0 < t := by linarith
    have hl := Real.log_pos (show 1 < t by linarith)
    unfold density
    rw [abs_mul, abs_of_nonneg (g_nonneg ht₂), abs_sub_comm]
    calc
      _ ≤ (9e-7 : ℝ) * t / Real.log t * g t :=
        mul_le_mul_of_nonneg_right (by simpa only [theta_eq_chebyshev] using h t ht)
          (g_nonneg ht₂)
      _ = ((9e-7 : ℝ) * (1 + 1 / Real.log t)) * tailKernel t := by
        unfold g GoldbachMertensSum.g tailKernel
        field_simp [ht₀.ne', hl.ne']

      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [inv_log_le htStart])
        (tailKernel_nonneg ht₀.le)

  have mid_density (h : MidThetaBound) {a t : ℝ}
      (ha : start ≤ a) (hat : a ≤ t) (ht : t ≤ split) :
      0 ≤ density t ∧ density t ≤ (4.2 : ℝ) / Real.log a * midKernel t := by
    have htStart := ha.trans hat
    have ht₂ := two_le_start.trans htStart
    have ht₀ : 0 < t := by linarith
    have ha₀ : 0 < a := by linarith [two_le_start.trans ha]
    have hal := Real.log_pos (show 1 < a by linarith [two_le_start.trans ha])
    have hl := Real.log_pos (show 1 < t by linarith)
    have hs := Real.sqrt_pos.2 ht₀
    have hs2 := Real.sq_sqrt ht₀.le
    have hlogMono := Real.log_le_log ha₀ hat
    have he := h t htStart ht
    rw [← theta_eq_chebyshev] at he
    constructor
    · exact mul_nonneg he.1 (g_nonneg ht₂)
    · calc
        density t ≤ (2 * Real.sqrt t) * g t :=
          mul_le_mul_of_nonneg_right he.2 (g_nonneg ht₂)
        _ = ((4 * (1 + 1 / Real.log t)) / Real.log t) * midKernel t := by
          unfold g GoldbachMertensSum.g midKernel
          field_simp [ht₀.ne', hs.ne', hl.ne']
          linear_combination 4 * hs2
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (midKernel_nonneg ht₀.le)
          calc
            _ ≤ (4.2 : ℝ) / Real.log t := div_le_div_of_nonneg_right
              (by linarith [inv_log_le htStart]) hl.le
            _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hal hlogMono


  have tail_integral (h : LargeThetaBound) {a b : ℝ}
      (ha : split ≤ a) (hab : a ≤ b) :
      |∫ t in a..b, density t| ≤ (9.5e-7 : ℝ) / Real.log a := by
    have ha₂ := two_le_start.trans (start_le_split.trans ha)
    have hInt : IntervalIntegrable (fun t => (9.5e-7 : ℝ) * tailKernel t) volume a b := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      intro t ht
      have ht₂ := ha₂.trans ht.1
      have ht₀ : t ≠ 0 := by linarith
      have hl := (Real.log_pos (show 1 < t by linarith)).ne'
      have hlog := Real.continuousAt_log ht₀
      unfold tailKernel
      exact (show ContinuousAt (fun t : ℝ => (9.5e-7 : ℝ) *
          (1 / (t * Real.log t ^ 2))) t by
        fun_prop (disch := positivity)).continuousWithinAt
    calc
      _ ≤ ∫ t in a..b, (9.5e-7 : ℝ) * tailKernel t := by
        rw [← Real.norm_eq_abs]
        apply intervalIntegral.norm_integral_le_of_norm_le hab _ hInt
        refine Filter.Eventually.of_forall ?_
        intro t ht
        simpa only [Real.norm_eq_abs] using tail_density h (ha.trans ht.1.le)
      _ ≤ _ := by
        rw [intervalIntegral.integral_const_mul, ← mul_one_div]
        exact mul_le_mul_of_nonneg_left (tailKernel_integral ha₂ hab) (by norm_num)

  have mid_integral (h : MidThetaBound) {a b : ℝ}
      (ha : start ≤ a) (hab : a ≤ b) (hb : b ≤ split) :
      0 ≤ (∫ t in a..b, density t) ∧
        (∫ t in a..b, density t) ≤ (4.2e-6 : ℝ) / Real.log a := by
    have ha₂ := two_le_start.trans ha
    have hla : 0 < Real.log a := Real.log_pos (by linarith)
    have hInt : IntervalIntegrable (fun t => (4.2 : ℝ) / Real.log a * midKernel t) volume a b := by
      apply ContinuousOn.intervalIntegrable_of_Icc hab
      intro t ht
      have ht₂ := ha₂.trans ht.1
      have ht₀ : 0 < t := by linarith
      have hs := Real.sqrt_pos.2 ht₀
      unfold midKernel
      exact (show ContinuousAt (fun t : ℝ => (4.2 : ℝ) / Real.log a *
        (1 / (2 * t * Real.sqrt t))) t by
        fun_prop (disch := positivity)).continuousWithinAt
    constructor
    · have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b :=
        intervalIntegrable_const
      have hz' := intervalIntegral.integral_mono_on hab hz (density_integrable ha₂ hab)
        (fun _ ht => (mid_density h ha ht.1 (ht.2.trans hb)).1)
      simpa using hz'
    · calc
        _ ≤ ∫ t in a..b, (4.2 : ℝ) / Real.log a * midKernel t :=
          intervalIntegral.integral_mono_on hab (density_integrable ha₂ hab) hInt
            (fun _ ht => (mid_density h ha ht.1 (ht.2.trans hb)).2)
        _ ≤ (4.2 : ℝ) / Real.log a * (Real.sqrt a)⁻¹ := by
          rw [intervalIntegral.integral_const_mul]
          exact mul_le_mul_of_nonneg_left (midKernel_integral ha₂ hab) (by positivity)
        _ ≤ (4.2 : ℝ) / Real.log a * (1e-6 : ℝ) :=
          mul_le_mul_of_nonneg_left (inv_sqrt_le ha) (by positivity)
        _ = _ := by ring

  have density_integral_bounds (hm : MidThetaBound) (hl : LargeThetaBound)
      {a b : ℝ} (ha : start ≤ a) (hab : a ≤ b) (hb : split ≤ b) :
      -(9.5e-7 : ℝ) / Real.log a ≤ (∫ t in a..b, density t) ∧
        (∫ t in a..b, density t) ≤ (5.15e-6 : ℝ) / Real.log a := by
    have ha₂ := two_le_start.trans ha
    have hla : 0 < Real.log a := Real.log_pos (by linarith)
    by_cases hsplit : a ≤ split
    · have hlog := Real.log_le_log (show 0 < a by linarith) hsplit
      have hmono : (9.5e-7 : ℝ) / Real.log split ≤ (9.5e-7 : ℝ) / Real.log a :=
        div_le_div_of_nonneg_left (by norm_num) hla hlog
      have htail := abs_le.mp ((tail_integral hl le_rfl hb).trans hmono)
      rw [← neg_div] at htail
      have hmid := mid_integral hm ha hsplit le_rfl
      rw [← intervalIntegral.integral_add_adjacent_intervals
            (density_integrable ha₂ hsplit) (density_integrable
              (two_le_start.trans start_le_split) hb)]
      obtain ⟨hmlo, hmhi⟩ := hmid
      obtain ⟨htlo, hthi⟩ := htail
      simp only [div_eq_mul_inv] at hmhi htlo hthi ⊢
      constructor
      · exact htlo.trans (le_add_of_nonneg_left hmlo)
      · calc
          _ ≤ (4.2e-6 : ℝ) * (Real.log a)⁻¹ + (9.5e-7 : ℝ) * (Real.log a)⁻¹ :=
            by exact add_le_add hmhi hthi
          _ = _ := by ring
    · have h := abs_le.mp (tail_integral hl (le_of_not_ge hsplit) hab)
      exact ⟨by simpa only [neg_div] using h.1, h.2.trans
        (div_le_div_of_nonneg_right (by norm_num) hla.le)⟩

  have edge_bounds (hm : MidThetaBound) (hl : LargeThetaBound)
      {a : ℝ} (ha : start ≤ a) :
      -(2e-6 : ℝ) / Real.log a ≤ edge a ∧ edge a ≤ (5e-8 : ℝ) / Real.log a := by
    have hla : 0 < Real.log a := Real.log_pos (by linarith [two_le_start.trans ha])
    by_cases hsplit : a ≤ split
    · have h := mid_edge hm ha hsplit
      exact ⟨h.1, h.2.trans (by positivity)⟩
    · have hUpper : (9e-7 : ℝ) / Real.log a ^ 2 ≤ (5e-8 : ℝ) / Real.log a := by
        rw [div_le_div_iff₀ (by positivity) hla]
        have h := mul_nonneg hla.le (sub_nonneg.mpr (log_ge_24 ha))
        nlinarith
      have h := abs_le.mp ((large_edge hl (le_of_not_ge hsplit)).trans hUpper)
      exact ⟨(div_le_div_of_nonneg_right
        (show -(2e-6 : ℝ) ≤ -(5e-8 : ℝ) by norm_num) hla.le).trans
          (by simpa only [neg_div] using h.1), h.2⟩

  have edge_tendsto (hl : LargeThetaBound) : Tendsto edge atTop (𝓝 0) := by
    have hInv : Tendsto (fun x => (Real.log x)⁻¹) atTop (𝓝 0) :=
      Real.tendsto_log_atTop.inv_tendsto_atTop
    have hMajor : Tendsto (fun x => (9e-7 : ℝ) / Real.log x ^ 2) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, ← inv_pow] using
        (tendsto_const_nhds (x := (9e-7 : ℝ))).mul (hInv.pow 2)
    apply squeeze_zero_norm' _ hMajor
    filter_upwards [eventually_ge_atTop split] with x hx
    simpa only [Real.norm_eq_abs] using large_edge hl hx

  have inclusive_from_theta (hm : MidThetaBound) (hl : LargeThetaBound)
      (x : ℝ) (hx : start < x) :
      Real.log (Real.log x) + constant - (2.964e-6 : ℝ) / Real.log x ≤ sumInclusive x ∧
        sumInclusive x ≤ Real.log (Real.log x) + constant + (6.836e-6 : ℝ) / Real.log x := by
    have hlog : 0 < Real.log x := Real.log_pos (by linarith [two_le_start.trans hx.le])
    have hEdge := edge_bounds hm hl hx.le
    have hvanish : Tendsto (fun b => err b - edge b) atTop (𝓝 0) := by
      simpa using err_tendsto.sub (edge_tendsto hl)
    have hLimits :
        ∀ᶠ b in atTop, -(2.95e-6 : ℝ) / Real.log x + (err b - edge b) ≤ err x ∧
          err x ≤ (5.2e-6 : ℝ) / Real.log x + (err b - edge b) := by
      filter_upwards [eventually_ge_atTop x, eventually_ge_atTop split] with b hb hbs
      have hd := density_integral_bounds hm hl hx.le hb hbs
      have he := err_eq_edge_add_integral (two_le_start.trans hx.le) hb
      obtain ⟨hdlo, hdhi⟩ := hd
      obtain ⟨helo, hehi⟩ := hEdge
      simp only [div_eq_mul_inv] at hdlo hdhi helo hehi ⊢
      constructor <;> linarith
    have hlo : -(2.95e-6 : ℝ) / Real.log x ≤ err x := by
      have ht := (tendsto_const_nhds (x := -(2.95e-6 : ℝ) / Real.log x)).add hvanish
      exact le_of_tendsto_of_tendsto (by simpa using ht) tendsto_const_nhds
        (hLimits.mono fun _ hb => hb.1)
    have hup : err x ≤ (5.2e-6 : ℝ) / Real.log x := by
      have ht := (tendsto_const_nhds (x := (5.2e-6 : ℝ) / Real.log x)).add hvanish
      exact le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa using ht)
        (hLimits.mono fun _ hb => hb.2)
    have hlowC : -(2.964e-6 : ℝ) / Real.log x ≤ -(2.95e-6 : ℝ) / Real.log x :=
      div_le_div_of_nonneg_right (by norm_num) hlog.le
    have hupperC : (5.2e-6 : ℝ) / Real.log x ≤ (6.836e-6 : ℝ) / Real.log x :=
      div_le_div_of_nonneg_right (by norm_num) hlog.le
    unfold err at hlo hup
    constructor
    · rw [sub_eq_add_neg, ← neg_div]
      linarith
    · linarith

  have frozen_of_theta_bounds (hm : MidThetaBound) (hl : LargeThetaBound) :
      let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); ∀ x : ℝ, (10 : ℝ) ^ 12 < x → Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + (6.836e-6 : ℝ) / Real.log x := by
    exact strict_of_inclusive (inclusive_from_theta hm hl)

  have hPsi : FinitePsiEstimate := by
    intro x hx hUpper
    rcases le_or_gt x ((10 : ℝ)^10) with h | h
    · exact hSieve x hx h
    · exact hFinite x h.le hUpper
  apply frozen_of_theta_bounds
  · intro x hx hUpper
    exact finite_theta_from_psi hPsi hx hUpper
  · intro x hx
    rcases le_or_gt (Real.log x) 3000 with h | h
    · exact large_theta_from_psi hx (hTable x hx h)
    · have hx2 : 2 < x := (by norm_num : (2 : ℝ) < (10 : ℝ)^19).trans_le hx
      exact hTail x hx2 h.le
