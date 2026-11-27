import Mathlib

open scoped BigOperators

namespace B13InnerLowNearAndEndpointSavingProof

/- Source PEqualNP.Outside.L_b13_weil_hd8006_certificate -/
section

/-! # Counting points on a modular hyperbola in a rectangle

Fourier inversion in the second coordinate expresses the count in terms of a
reciprocal sum on the first interval. We bound its nonzero frequencies with
the complete Weil estimate for composite moduli and a gcd-weighted bound for
the Fourier coefficients of an interval. Applying the same estimate to the
full first interval centers the count at the product of the two lengths times
the totient divided by the square of the modulus. This also covers empty
intervals. The contribution of the zero frequency is computed exactly.

The project formulation cites Igor Shparlinski, Modular Hyperbolas, Theorem 13
and equation (10), https://arxiv.org/abs/1103.2879.
-/

/- Portions adapted from the MathlibNt library of subfish-zhou/goldbach-lean,
Copyright 2026 UyNewNas. Distributed under the Apache License, Version 2.0. A copy of the license
accompanies this repository in LICENSE.
https://github.com/subfish-zhou/goldbach-lean/tree/9d4c3a4010d42aedd9e7231bf94386019cfffccc/MathlibNt/AnalyticNumberTheory/LargeSieve
Each SOURCE comment records the original module name. The modules have
been joined into a single file, with their scopes preserved, and the
proof scripts updated for the toolchain pinned by this repository. -/

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCompletion -/

/-!
# Finite Fourier completion of the reciprocal sum

The modulus is any positive natural number, including one. Neither frequency
is assumed coprime to it. These are finite identities and bounds, not an
assertion of the complete Kloosterman square-root estimate.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {q : ℕ} [NeZero q]

def reciprocalPhase (q : ℕ) [NeZero q] (d : ℤ) (u : ZMod q) : ℂ :=
  if IsUnit u then ZMod.stdAddChar ((d : ZMod q) * u⁻¹) else 0

def completeKloosterman (q : ℕ) [NeZero q] (m : ZMod q) (d : ℤ) : ℂ :=
  ∑ u : ZMod q, ZMod.stdAddChar (m * u) * reciprocalPhase q d u

/-- The integers in the interval are `A, A+1, ..., A+L-1`. -/
def incompleteReciprocal (q : ℕ) [NeZero q] (d A : ℤ) (L : ℕ) : ℂ :=
  ∑ j ∈ range L, reciprocalPhase q d ((A : ZMod q) + (j : ZMod q))

def intervalFourier (q : ℕ) [NeZero q] (A : ℤ) (L : ℕ) (m : ZMod q) : ℂ :=
  ∑ j ∈ range L, ZMod.stdAddChar (m * ((A : ZMod q) + (j : ZMod q)))

theorem completeKloosterman_eq (m : ZMod q) (d : ℤ) :
    completeKloosterman q m d =
      ∑ u : ZMod q, if IsUnit u then
        ZMod.stdAddChar (m * u + (d : ZMod q) * u⁻¹) else 0 := by
  classical
  simp only [completeKloosterman, reciprocalPhase, AddChar.map_add_eq_mul]
  apply sum_congr rfl
  intro u _
  split_ifs <;> simp

theorem dft_reciprocalPhase (d : ℤ) (m : ZMod q) :
    ZMod.dft (reciprocalPhase q d) m = completeKloosterman q (-m) d := by
  simp only [ZMod.dft_apply, completeKloosterman, smul_eq_mul, neg_mul]
  congr 1 with u
  rw [mul_comm u m]

theorem reciprocalPhase_fourier (d : ℤ) (u : ZMod q) :
    reciprocalPhase q d u = (q : ℂ)⁻¹ *
      ∑ m : ZMod q, ZMod.stdAddChar (m * u) * completeKloosterman q (-m) d := by
  have h := congrFun (ZMod.dft.symm_apply_apply (reciprocalPhase q d)) u
  simpa only [ZMod.invDFT_apply, smul_eq_mul, dft_reciprocalPhase] using h.symm

/-- Exact completion, even for intervals longer than a period. -/
theorem incompleteReciprocal_completion (d A : ℤ) (L : ℕ) :
    incompleteReciprocal q d A L = (q : ℂ)⁻¹ *
      ∑ m : ZMod q, intervalFourier q A L m * completeKloosterman q (-m) d := by
  unfold incompleteReciprocal
  simp_rw [reciprocalPhase_fourier]
  rw [← mul_sum, sum_comm]
  simp_rw [← sum_mul]
  rfl

theorem stdAddChar_norm (u : ZMod q) : ‖ZMod.stdAddChar u‖ = 1 := by
  exact Circle.norm_coe (ZMod.toCircle u)


theorem intervalFourier_norm_le_length (A : ℤ) (L : ℕ) (m : ZMod q) :
    ‖intervalFourier q A L m‖ ≤ L := by
  unfold intervalFourier
  simpa only [stdAddChar_norm, sum_const, card_range, nsmul_eq_mul, mul_one] using
    norm_sum_le (range L) (fun j ↦ ZMod.stdAddChar
      (m * ((A : ZMod q) + (j : ZMod q))))

theorem intervalFourier_eq_geom (A : ℤ) (L : ℕ) (m : ZMod q) :
    intervalFourier q A L m =
      ZMod.stdAddChar (m * (A : ZMod q)) *
        ∑ j ∈ range L, (ZMod.stdAddChar m) ^ j := by
  simp only [intervalFourier, mul_add, AddChar.map_add_eq_mul, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [mul_comm m (j : ZMod q), ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

theorem intervalFourier_norm_mul (A : ℤ) (L : ℕ) (m : ZMod q) :
    ‖intervalFourier q A L m‖ * ‖ZMod.stdAddChar m - 1‖ ≤ 2 := by
  rw [intervalFourier_eq_geom, norm_mul, stdAddChar_norm, one_mul, ← norm_mul,
    geom_sum_mul]
  calc
    ‖ZMod.stdAddChar m ^ L - 1‖ ≤ ‖ZMod.stdAddChar m ^ L‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = 2 := by rw [norm_pow, stdAddChar_norm]; norm_num

theorem incompleteReciprocal_norm_le_completion (d A : ℤ) (L : ℕ) (B : ℝ)
    (hB : ∀ m : ZMod q, ‖completeKloosterman q m d‖ ≤ B) :
    ‖incompleteReciprocal q d A L‖ ≤
      (q : ℝ)⁻¹ * (∑ m : ZMod q, ‖intervalFourier q A L m‖) * B := by
  rw [incompleteReciprocal_completion, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (q : ℝ)⁻¹ * ‖∑ m : ZMod q,
        intervalFourier q A L m * completeKloosterman q (-m) d‖
      ≤ (q : ℝ)⁻¹ * ∑ m : ZMod q,
        ‖intervalFourier q A L m‖ * B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (norm_sum_le _ _).trans (sum_le_sum fun m _ ↦ ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hB (-m)) (norm_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

theorem completeKloosterman_modulus_one (m : ZMod 1) (d : ℤ) :
    completeKloosterman 1 m d = 1 := by
  have hu (u : ZMod 1) : IsUnit u := by
    rw [Subsingleton.elim u 1]; exact isUnit_one
  have he (u : ZMod 1) : ZMod.stdAddChar u = 1 := by
    rw [Subsingleton.elim u 0]; simp
  rw [completeKloosterman_eq]
  simp only [hu, if_true, he, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
    Nat.cast_one, one_mul]


private theorem sin_pi_mul_lower {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    2 * min t (1 - t) ≤ Real.sin (Real.pi * t) := by
  have half (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
      2 * s ≤ Real.sin (Real.pi * s) := by
    have h := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hs0)
      (show Real.pi * s ≤ Real.pi / 2 by nlinarith [Real.pi_pos])
    convert h using 1
    field_simp
  by_cases ht : t ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
    exact half t h0 ht
  · rw [min_eq_right (by linarith)]
    have h := half (1 - t) (by linarith) (by linarith)
    simpa only [mul_sub, mul_one, Real.sin_pi_sub] using h

theorem stdAddChar_sub_one_lower (k : ℕ) (hk : k ≤ q) :
    4 * min (k : ℝ) ((q : ℝ) - k) ≤
      (q : ℝ) * ‖ZMod.stdAddChar (k : ZMod q) - 1‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hkR : (k : ℝ) ≤ q := by exact_mod_cast hk
  have ht0 : 0 ≤ (k : ℝ) / q := by positivity
  have ht1 : (k : ℝ) / q ≤ 1 := (div_le_one hq).2 hkR
  have hs := sin_pi_mul_lower ht0 ht1
  have hs0 : 0 ≤ Real.sin (Real.pi * ((k : ℝ) / q)) :=
    (mul_nonneg (by norm_num) (le_min ht0 (by linarith))).trans hs
  have he : ZMod.stdAddChar (k : ZMod q) =
      Complex.exp (Complex.I * ((2 * Real.pi * ((k : ℝ) / q) : ℝ) : ℂ)) := by
    rw [← Int.cast_natCast k, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * ((k : ℝ) / q) / 2 =
    Real.pi * ((k : ℝ) / q) by ring]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hs0)]
  have hmin : min ((k : ℝ) / q) (1 - (k : ℝ) / q) =
      min (k : ℝ) ((q : ℝ) - k) / q := by
    rw [← min_div_div_right hq.le, sub_div, div_self hq.ne']
  rw [hmin] at hs
  have hh := mul_le_mul_of_nonneg_left hs hq.le
  field_simp at hh
  rw [show Real.pi * ((k : ℝ) / q) = (k : ℝ) * Real.pi / q by ring]
  nlinarith

theorem intervalFourier_norm_le_reciprocals (A : ℤ) (L k : ℕ)
    (hk0 : 0 < k) (hkq : k < q) :
    ‖intervalFourier q A L (k : ZMod q)‖ ≤
      (q : ℝ) * ((k : ℝ)⁻¹ + ((q - k : ℕ) : ℝ)⁻¹) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hk : (0 : ℝ) < k := by exact_mod_cast hk0
  have hqk : (0 : ℝ) < (q : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkq)
  have hlow := stdAddChar_sub_one_lower k hkq.le
  have hu := intervalFourier_norm_mul A L (k : ZMod q)
  have hm := mul_le_mul_of_nonneg_left hlow
    (norm_nonneg (intervalFourier q A L (k : ZMod q)))
  have huq := mul_le_mul_of_nonneg_left hu hq.le
  rw [Nat.cast_sub hkq.le]
  by_cases hhalf : (k : ℝ) ≤ (q : ℝ) - k
  · rw [min_eq_left hhalf] at hm
    have hb : ‖intervalFourier q A L (k : ZMod q)‖ ≤ (q : ℝ) / k := by
      apply (le_div_iff₀ hk).2
      nlinarith
    exact hb.trans (by
      rw [div_eq_mul_inv, mul_add]
      exact le_add_of_nonneg_right (by positivity))
  · rw [min_eq_right (le_of_not_ge hhalf)] at hm
    have hb : ‖intervalFourier q A L (k : ZMod q)‖ ≤ (q : ℝ) / ((q : ℝ) - k) := by
      apply (le_div_iff₀ hqk).2
      nlinarith
    exact hb.trans (by
      rw [div_eq_mul_inv, mul_add]
      exact le_add_of_nonneg_left (by positivity))

private theorem sum_zmod_eq_range (f : ZMod q → ℝ) :
    ∑ u : ZMod q, f u = ∑ k ∈ range q, f (k : ZMod q) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ => congrArg f (ZMod.natCast_zmod_val i).symm)


/-- The normalized interval Fourier L1 norm costs only one logarithm. -/
theorem intervalFourier_lone (A : ℤ) (L : ℕ) (hL : L ≤ q) :
    ∑ m : ZMod q, ‖intervalFourier q A L m‖ ≤
      (q : ℝ) * (3 + 2 * Real.log q) := by
  have hq : 0 < q := NeZero.pos q
  rw [sum_zmod_eq_range, sum_range_eq_add_Ico _ hq]
  have hs : ∑ k ∈ Ico 1 q, ‖intervalFourier q A L (k : ZMod q)‖ ≤
      (q : ℝ) * (2 * (harmonic q : ℝ)) := by
    calc
      _ ≤ ∑ k ∈ Ico 1 q,
          (q : ℝ) * ((k : ℝ)⁻¹ + ((q - k : ℕ) : ℝ)⁻¹) :=
        sum_le_sum fun k hk ↦ intervalFourier_norm_le_reciprocals A L k
          (mem_Ico.mp hk).1 (mem_Ico.mp hk).2
      _ = (q : ℝ) * (2 * ∑ k ∈ Ico 1 q, (k : ℝ)⁻¹) := by
        rw [← mul_sum, sum_add_distrib,
          sum_Ico_reflect (fun n : ℕ ↦ (n : ℝ)⁻¹) 1 (m := q) (n := q) (by omega)]
        simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right]
        ring
      _ ≤ _ := by
        gcongr
        rw [harmonic_eq_sum_Icc, Rat.cast_sum]
        simp only [Rat.cast_inv, Rat.cast_natCast]
        exact sum_le_sum_of_subset_of_nonneg
          (fun k hk ↦ mem_Icc.mpr ⟨(mem_Ico.mp hk).1, (mem_Ico.mp hk).2.le⟩)
          (fun _ _ _ ↦ by positivity)
  have hzero : ‖intervalFourier q A L (0 : ZMod q)‖ ≤ (q : ℝ) :=
    (intervalFourier_norm_le_length A L 0).trans (by exact_mod_cast hL)
  have hh := harmonic_le_one_add_log q
  have hp := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ q by positivity)
  simp only [Nat.cast_zero]
  nlinarith

theorem incompleteReciprocal_norm_le_log (d A : ℤ) (L : ℕ) (hL : L ≤ q)
    (B : ℝ) (hB : ∀ m : ZMod q, ‖completeKloosterman q m d‖ ≤ B) :
    ‖incompleteReciprocal q d A L‖ ≤ (3 + 2 * Real.log q) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  refine (incompleteReciprocal_norm_le_completion d A L B hB).trans ?_
  calc
    _ ≤ (q : ℝ)⁻¹ * ((q : ℝ) * (3 + 2 * Real.log q)) * B := by
      gcongr
      exact intervalFourier_lone A L hL
    _ = _ := by field_simp

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanCRT -/

/-!
# Twisted Chinese remaindering for the actual complete Kloosterman sum

The two twists are the integer Bezout coefficients: `m * gcdA m n +
n * gcdB m n = 1`. Thus `gcdB m n` is the inverse of `n` modulo `m`.
No frequency is required to be a unit, and either coprime factor may be one.
These are exact arithmetic identities, not an invocation of a Weil bound.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem stdAddChar_mul_modulus (q r : ℕ) [NeZero q] [NeZero r] (z : ℤ) :
    ZMod.stdAddChar ((r : ZMod (q * r)) * (z : ZMod (q * r))) =
      ZMod.stdAddChar (z : ZMod q) := by
  rw [← Int.cast_natCast r, ← Int.cast_mul, ZMod.stdAddChar_coe,
    ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  field_simp

theorem zmod_map_inv_of_isUnit {q r : ℕ} (f : ZMod q →+* ZMod r)
    {u : ZMod q} (hu : IsUnit u) : f u⁻¹ = (f u)⁻¹ := by
  obtain ⟨v, rfl⟩ := hu
  rw [ZMod.inv_coe_unit]
  exact (Units.coe_map_inv f.toMonoidHom v).symm.trans
    (ZMod.inv_coe_unit (Units.map f.toMonoidHom v)).symm

theorem stdAddChar_crt (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (z : ZMod (m * n)) :
    ZMod.stdAddChar z =
      ZMod.stdAddChar ((m.gcdB n : ZMod m) * (ZMod.chineseRemainder h z).1) *
      ZMod.stdAddChar ((m.gcdA n : ZMod n) * (ZMod.chineseRemainder h z).2) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  have hab : (n : ℤ) * m.gcdB n + (m : ℤ) * m.gcdA n = 1 := by
    have hh := Nat.gcd_eq_gcd_ab m n
    rw [h.gcd_eq_one] at hh
    simpa only [Nat.cast_one, add_comm] using hh.symm
  have he : (a : ZMod (m * n)) =
      (n : ZMod (m * n)) * ((m.gcdB n * a : ℤ) : ZMod (m * n)) +
      (m : ZMod (m * n)) * ((m.gcdA n * a : ℤ) : ZMod (m * n)) := by
    have hh := congrArg (fun t : ℤ ↦ (t : ZMod (m * n))) (congrArg (· * a) hab)
    push_cast at hh
    push_cast
    linear_combination -hh
  have hn : ZMod.stdAddChar
      ((m : ZMod (m * n)) * ((m.gcdA n * a : ℤ) : ZMod (m * n))) =
      ZMod.stdAddChar ((m.gcdA n * a : ℤ) : ZMod n) := by
    rw [← Int.cast_natCast m, ← Int.cast_mul, ZMod.stdAddChar_coe,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
    field_simp
  calc
    _ = ZMod.stdAddChar
        ((n : ZMod (m * n)) * ((m.gcdB n * a : ℤ) : ZMod (m * n))) *
        ZMod.stdAddChar
        ((m : ZMod (m * n)) * ((m.gcdA n * a : ℤ) : ZMod (m * n))) := by
      rw [← AddChar.map_add_eq_mul, ← he]
    _ = _ := by
      rw [stdAddChar_mul_modulus, hn]
      simp only [map_intCast, Int.cast_mul, Prod.fst_intCast, Prod.snd_intCast]

/-- Multiplicativity with both frequencies twisted by the opposite modulus's inverse. -/
theorem completeKloosterman_crt (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a d : ℤ) :
    completeKloosterman (m * n) (a : ZMod (m * n)) d =
      completeKloosterman m ((a * m.gcdB n : ℤ) : ZMod m) (d * m.gcdB n) *
      completeKloosterman n ((a * m.gcdA n : ℤ) : ZMod n) (d * m.gcdA n) := by
  classical
  let e := ZMod.chineseRemainder h
  let f : ZMod (m * n) →+* ZMod m := (RingHom.fst _ _).comp e.toRingHom
  let g : ZMod (m * n) →+* ZMod n := (RingHom.snd _ _).comp e.toRingHom
  have hu (u : ZMod (m * n)) : IsUnit u ↔ IsUnit (f u) ∧ IsUnit (g u) := by
    constructor
    · intro hh
      exact ⟨hh.map f, hh.map g⟩
    · intro hh
      have he : IsUnit (e u) := Prod.isUnit_iff.mpr hh
      simpa using he.map e.symm.toRingHom
  simp_rw [completeKloosterman_eq]
  rw [sum_mul]
  simp_rw [mul_sum]
  let F := fun p : ZMod m × ZMod n ↦
      (if IsUnit p.1 then ZMod.stdAddChar
        (((a * m.gcdB n : ℤ) : ZMod m) * p.1 +
          ((d * m.gcdB n : ℤ) : ZMod m) * p.1⁻¹) else 0) *
      (if IsUnit p.2 then ZMod.stdAddChar
        (((a * m.gcdA n : ℤ) : ZMod n) * p.2 +
          ((d * m.gcdA n : ℤ) : ZMod n) * p.2⁻¹) else 0)
  change _ = ∑ x : ZMod m, ∑ y : ZMod n, F (x, y)
  rw [← Fintype.sum_prod_type F]
  apply Fintype.sum_equiv e.toEquiv
  intro u
  change (if IsUnit u then _ else _) =
    (if IsUnit (f u) then _ else _) * (if IsUnit (g u) then _ else _)
  by_cases hunit : IsUnit u
  · have hfg := (hu u).mp hunit
    simp only [hunit, hfg.1, hfg.2, if_true]
    rw [stdAddChar_crt m n h]
    change ZMod.stdAddChar ((m.gcdB n : ZMod m) *
        f ((a : ZMod (m * n)) * u + (d : ZMod (m * n)) * u⁻¹)) *
      ZMod.stdAddChar ((m.gcdA n : ZMod n) *
        g ((a : ZMod (m * n)) * u + (d : ZMod (m * n)) * u⁻¹)) = _
    simp only [map_add, map_mul, map_intCast, zmod_map_inv_of_isUnit _ hunit,
      Int.cast_mul]
    rw [show f u = (e.toEquiv u).1 from rfl, show g u = (e.toEquiv u).2 from rfl]
    congr 2 <;> ring
  · have hfg := not_and_or.mp (mt (hu u).mpr hunit)
    rcases hfg with hf | hg
    · simp [hunit, hf]
    · simp [hunit, hg]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanDescent -/

/-!
# Common-frequency descent

Reduction of units is surjective even when the removed factor is not coprime
to the retained modulus. Its uniform fibers give a totient ratio, not in
general the removed factor. In particular the modulus-one endpoint is retained.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem completeKloosterman_eq_sum_units (q : ℕ) [NeZero q] (a : ZMod q) (d : ℤ) :
    completeKloosterman q a d =
      ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (a * (u : ZMod q) +
        (d : ZMod q) * (↑u⁻¹ : ZMod q)) := by
  classical
  rw [completeKloosterman_eq]
  symm
  apply Fintype.sum_of_injective Units.val Units.val_injective
  · intro u hu
    have hn : ¬ IsUnit u := by
      rintro ⟨v, rfl⟩
      exact hu ⟨v, rfl⟩
    simp [hn]
  · intro u
    simp [u.isUnit, ZMod.inv_coe_unit]

private theorem sum_comp_surjective_mul_card {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) (F : H → ℂ) :
    (Fintype.card H : ℂ) * (∑ x : G, F (f x)) =
      (Fintype.card G : ℂ) * ∑ y : H, F y := by
  have shift (y : H) : ∑ x : G, F (y * f x) = ∑ x : G, F (f x) := by
    obtain ⟨v, rfl⟩ := hf y
    have ht := Equiv.sum_comp (Equiv.mulLeft v) (fun x : G ↦ F (f x))
    change ∑ x : G, F (f (v * x)) = _ at ht
    simpa only [map_mul] using ht
  have shiftR (x : H) : ∑ y : H, F (y * x) = ∑ y : H, F y :=
    Equiv.sum_comp (Equiv.mulRight x) F
  calc
    _ = ∑ y : H, ∑ x : G, F (y * f x) := by simp only [shift, sum_const,
      card_univ, nsmul_eq_mul]
    _ = ∑ x : G, ∑ y : H, F (y * f x) := sum_comm
    _ = _ := by
      simp_rw [shiftR]
      simp

theorem stdAddChar_mul_modulus_cast (q r : ℕ) [NeZero q] [NeZero r]
    (z : ZMod (q * r)) :
    ZMod.stdAddChar ((r : ZMod (q * r)) * z) =
      ZMod.stdAddChar (ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) z) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective z
  simpa only [map_intCast] using stdAddChar_mul_modulus q r z

/-- Exact descent before division; valid also when `q=1` or either frequency vanishes. -/
theorem completeKloosterman_common_factor_mul (q r : ℕ) [NeZero q] [NeZero r]
    (a d : ℤ) :
    (q.totient : ℂ) *
        completeKloosterman (q * r) ((r * a : ℤ) : ZMod (q * r)) (r * d) =
      ((q * r).totient : ℂ) * completeKloosterman q (a : ZMod q) d := by
  let h : q ∣ q * r := Nat.dvd_mul_right q r
  let f := ZMod.unitsMap h
  let F : (ZMod q)ˣ → ℂ := fun u ↦
    ZMod.stdAddChar ((a : ZMod q) * (↑u : ZMod q) + (d : ZMod q) * (↑u⁻¹ : ZMod q))
  have phase (u : (ZMod (q * r))ˣ) :
      ZMod.stdAddChar (((r * a : ℤ) : ZMod (q * r)) * (↑u : ZMod (q * r)) +
        ((r * d : ℤ) : ZMod (q * r)) * (↑u⁻¹ : ZMod (q * r))) = F (f u) := by
    rw [show ((r * a : ℤ) : ZMod (q * r)) * (↑u : ZMod (q * r)) +
        ((r * d : ℤ) : ZMod (q * r)) * (↑u⁻¹ : ZMod (q * r)) =
        (r : ZMod (q * r)) * ((a : ZMod (q * r)) * (↑u : ZMod (q * r)) +
          (d : ZMod (q * r)) * (↑u⁻¹ : ZMod (q * r))) by push_cast; ring]
    rw [stdAddChar_mul_modulus_cast]
    simp only [map_add, map_mul, map_intCast]
    rfl
  simp_rw [completeKloosterman_eq_sum_units, phase]
  simpa only [ZMod.card_units_eq_totient] using
    sum_comp_surjective_mul_card f (ZMod.unitsMap_surjective h) F

theorem completeKloosterman_common_factor (q r : ℕ) [NeZero q] [NeZero r]
    (a d : ℤ) :
    completeKloosterman (q * r) ((r * a : ℤ) : ZMod (q * r)) (r * d) =
      (((q * r).totient : ℂ) / (q.totient : ℂ)) *
        completeKloosterman q (a : ZMod q) d := by
  have hq : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  apply (mul_left_cancel₀ hq)
  rw [completeKloosterman_common_factor_mul]
  field_simp


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanPrimePower -/

/-!
# Elementary prime-power cancellation

Translation by the last nonzero prime-power layer preserves units. If just
one frequency is divisible by the prime, it multiplies the complete sum by
a nontrivial constant character, forcing the sum to vanish. The argument
works in characteristic two as well; it uses no quadratic Gauss-sum formula.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem completeKloosterman_symm (q : ℕ) [NeZero q] (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d =
      completeKloosterman q (d : ZMod q) a := by
  simp_rw [completeKloosterman_eq_sum_units]
  apply Fintype.sum_equiv (Equiv.inv (ZMod q)ˣ)
  intro u
  change ZMod.stdAddChar ((a : ZMod q) * (↑u : ZMod q) +
      (d : ZMod q) * (↑u⁻¹ : ZMod q)) =
    ZMod.stdAddChar ((d : ZMod q) * (↑u⁻¹ : ZMod q) +
      (a : ZMod q) * (↑(u⁻¹)⁻¹ : ZMod q))
  rw [inv_inv, add_comm]

private theorem shifted_inverse_product {q : ℕ} (u t : ZMod q) (hu : IsUnit u)
    (ht : t ^ 2 = 0) :
    (u + t) * (u⁻¹ - t * (u⁻¹) ^ 2) = 1 := by
  have hi := ZMod.mul_inv_of_unit u hu
  linear_combination (1 - t * u⁻¹) * hi - (u⁻¹) ^ 2 * ht

theorem zmod_isUnit_add_square_zero {q : ℕ} (u t : ZMod q) (ht : t ^ 2 = 0) :
    IsUnit (u + t) ↔ IsUnit u := by
  have step (v s : ZMod q) (hv : IsUnit v) (hs : s ^ 2 = 0) : IsUnit (v + s) :=
    isUnit_iff_exists_inv.mpr ⟨_, shifted_inverse_product v s hv hs⟩
  constructor
  · intro hu
    simpa only [add_neg_cancel_right] using step (u + t) (-t) hu (by simpa using ht)
  · intro hu
    exact step u t hu ht

theorem zmod_inv_add_square_zero {q : ℕ} (u t : ZMod q)
    (hu : IsUnit u) (ht : t ^ 2 = 0) :
    (u + t)⁻¹ = u⁻¹ - t * (u⁻¹) ^ 2 := by
  have hs := shifted_inverse_product u t hu ht
  have hi := ZMod.inv_mul_of_unit (u + t) ((zmod_isUnit_add_square_zero u t ht).mpr hu)
  calc
    _ = (u + t)⁻¹ * ((u + t) * (u⁻¹ - t * (u⁻¹) ^ 2)) := by rw [hs, mul_one]
    _ = _ := by rw [← mul_assoc, hi, one_mul]

theorem completeKloosterman_vanish_of_square_zero_shift (q : ℕ) [NeZero q]
    (a t : ZMod q) (d : ℤ) (ht : t ^ 2 = 0) (hdt : (d : ZMod q) * t = 0)
    (hat : ZMod.stdAddChar (a * t) ≠ 1) :
    completeKloosterman q a d = 0 := by
  classical
  let F : ZMod q → ℂ := fun u ↦
    if IsUnit u then ZMod.stdAddChar (a * u + (d : ZMod q) * u⁻¹) else 0
  have shift (u : ZMod q) : F (u + t) = ZMod.stdAddChar (a * t) * F u := by
    dsimp only [F]
    simp only [zmod_isUnit_add_square_zero u t ht]
    by_cases hu : IsUnit u
    · simp only [hu, if_true]
      rw [zmod_inv_add_square_zero u t hu ht]
      have he : a * (u + t) + (d : ZMod q) * (u⁻¹ - t * (u⁻¹) ^ 2) =
          a * t + (a * u + (d : ZMod q) * u⁻¹) := by
        linear_combination -(u⁻¹) ^ 2 * hdt
      rw [he, AddChar.map_add_eq_mul]
    · simp [hu]
  have hs : ∑ u : ZMod q, F (u + t) = ∑ u : ZMod q, F u :=
    Equiv.sum_comp (Equiv.addRight t) F
  simp_rw [shift, ← mul_sum] at hs
  have hz : (ZMod.stdAddChar (a * t) - 1) * (∑ u : ZMod q, F u) = 0 := by
    linear_combination hs
  rw [completeKloosterman_eq]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hat)

/-- For exponent at least two, unequal frequency valuations give zero after
common-factor descent. No odd-prime hypothesis is used. -/
theorem completeKloosterman_prime_power_vanish (p k : ℕ) [Fact p.Prime]
    (a d : ℤ) (ha : ¬ (p : ℤ) ∣ a) (hd : (p : ℤ) ∣ d) :
    completeKloosterman (p * p ^ (k + 1)) (a : ZMod (p * p ^ (k + 1))) d = 0 := by
  let t : ZMod (p * p ^ (k + 1)) := (p ^ (k + 1) : ℕ)
  have ht : t ^ 2 = 0 := by
    change ((p ^ (k + 1) : ℕ) : ZMod (p * p ^ (k + 1))) ^ 2 = 0
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    refine ⟨p ^ k, ?_⟩
    rw [pow_succ]
    ring
  have hdt : (d : ZMod (p * p ^ (k + 1))) * t = 0 := by
    obtain ⟨b, rfl⟩ := hd
    change ((p * b : ℤ) : ZMod (p * p ^ (k + 1))) * (p ^ (k + 1) : ℕ) = 0
    push_cast
    have hq : (p : ZMod (p * p ^ (k + 1))) * (p : ZMod (p * p ^ (k + 1))) ^ (k + 1) = 0 := by
      rw [← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_self]
    linear_combination (b : ZMod (p * p ^ (k + 1))) * hq
  apply completeKloosterman_vanish_of_square_zero_shift _ _ t d ht hdt
  change ZMod.stdAddChar ((a : ZMod (p * p ^ (k + 1))) *
    ((p ^ (k + 1) : ℕ) : ZMod (p * p ^ (k + 1)))) ≠ 1
  rw [mul_comm (a : ZMod (p * p ^ (k + 1))), stdAddChar_mul_modulus]
  intro hh
  have hz : (a : ZMod p) = 0 :=
    ZMod.injective_stdAddChar (hh.trans (AddChar.map_zero_eq_one ZMod.stdAddChar).symm)
  exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)

theorem completeKloosterman_prime_power_vanish_left (p k : ℕ) [Fact p.Prime]
    (a d : ℤ) (ha : (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    completeKloosterman (p * p ^ (k + 1)) (a : ZMod (p * p ^ (k + 1))) d = 0 := by
  rw [completeKloosterman_symm]
  exact completeKloosterman_prime_power_vanish p k d a hd ha

/-- At exponent one, a single zero frequency gives `-1`, not zero. -/
theorem completeKloosterman_prime_zero_frequency (p : ℕ) [Fact p.Prime]
    (a : ZMod p) (ha : a ≠ 0) :
    completeKloosterman p a 0 = -1 := by
  classical
  have hs : ∑ u : ZMod p, ZMod.stdAddChar (a * u) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p ha)
  rw [completeKloosterman_eq]
  simp only [Int.cast_zero, zero_mul, add_zero]
  calc
    _ = ∑ u : ZMod p, (ZMod.stdAddChar (a * u) - if u = 0 then 1 else 0) := by
      apply sum_congr rfl
      intro u _
      by_cases hu : u = 0 <;> simp [hu, isUnit_iff_ne_zero]
    _ = -1 := by rw [sum_sub_distrib, hs]; simp

theorem completeKloosterman_prime_zero_left (p : ℕ) [Fact p.Prime]
    (d : ℤ) (hd : ¬ (p : ℤ) ∣ d) :
    completeKloosterman p 0 d = -1 := by
  have he := completeKloosterman_symm p 0 d
  simp only [Int.cast_zero] at he
  rw [he]
  exact completeKloosterman_prime_zero_frequency p _ (fun hz ↦
    hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp hz))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanStationary -/

/-!
# Exact stationary-phase localization at square moduli

This is a finite cancellation identity, not a bound assumed on a remainder.
Translation by a square-zero layer removes every nonstationary residue.
The square-modulus specialization works for all positive moduli, including
powers of two, and leaves only the actual quadratic congruence.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem sum_localize_eigenvalue {ι : Type*} [Fintype ι]
    (e : ι ≃ ι) (F c : ι → ℂ) (hc : ∀ x, c (e x) = c x)
    (hF : ∀ x, F (e x) = c x * F x) :
    ∑ x, F x = ∑ x, if c x = 1 then F x else 0 := by
  classical
  let G : ι → ℂ := fun x ↦ if c x = 1 then 0 else F x / (c x - 1)
  have hg (x : ι) : G (e x) - G x = if c x = 1 then 0 else F x := by
    simp only [G, hc, hF]
    by_cases hx : c x = 1
    · simp [hx]
    · simp only [hx, if_false]
      field_simp
  have hz : (∑ x, if c x = 1 then 0 else F x) = 0 := by
    simp_rw [← hg]
    rw [sum_sub_distrib, Equiv.sum_comp, sub_self]
  calc
    _ = (∑ x, if c x = 1 then F x else 0) +
        (∑ x, if c x = 1 then 0 else F x) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = _ := by rw [hz, add_zero]

theorem completeKloosterman_square_zero_localization (q : ℕ) [NeZero q]
    (a t : ZMod q) (d : ℤ) (ht : t ^ 2 = 0) :
    completeKloosterman q a d =
      ∑ u : ZMod q, if IsUnit u ∧ t * (a * u ^ 2 - (d : ZMod q)) = 0 then
        ZMod.stdAddChar (a * u + (d : ZMod q) * u⁻¹) else 0 := by
  classical
  let F : ZMod q → ℂ := fun u ↦
    if IsUnit u then ZMod.stdAddChar (a * u + (d : ZMod q) * u⁻¹) else 0
  let c : ZMod q → ℂ := fun u ↦
    if IsUnit u then ZMod.stdAddChar (t * (a - (d : ZMod q) * (u⁻¹) ^ 2)) else 1
  have hc (u : ZMod q) : c (u + t) = c u := by
    simp only [c, zmod_isUnit_add_square_zero u t ht]
    by_cases hu : IsUnit u
    · simp only [hu, if_true]
      rw [zmod_inv_add_square_zero u t hu ht]
      congr 1
      linear_combination (d : ZMod q) * (2 * (u⁻¹) ^ 3 - t * (u⁻¹) ^ 4) * ht
    · simp [hu]
  have hF (u : ZMod q) : F (u + t) = c u * F u := by
    simp only [F, c, zmod_isUnit_add_square_zero u t ht]
    by_cases hu : IsUnit u
    · simp only [hu, if_true]
      rw [zmod_inv_add_square_zero u t hu ht, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    · simp [hu]
  have hchar (u : ZMod q) (hu : IsUnit u) :
      c u = 1 ↔ t * (a * u ^ 2 - (d : ZMod q)) = 0 := by
    simp only [c, hu, if_true]
    have hi := ZMod.mul_inv_of_unit u hu
    have hzero : ZMod.stdAddChar (t * (a - (d : ZMod q) * (u⁻¹) ^ 2)) = 1 ↔
        t * (a - (d : ZMod q) * (u⁻¹) ^ 2) = 0 := by
      rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q)),
        ZMod.injective_stdAddChar.eq_iff]
    rw [hzero]
    constructor
    · intro hh
      calc
        _ = (t * (a - (d : ZMod q) * (u⁻¹) ^ 2)) * u ^ 2 := by
          calc
            _ = t * (a * u ^ 2 - (d : ZMod q) * (u * u⁻¹) ^ 2) := by rw [hi]; ring
            _ = _ := by ring
        _ = 0 := by rw [hh, zero_mul]
    · intro hh
      calc
        _ = (t * (a * u ^ 2 - (d : ZMod q))) * (u⁻¹) ^ 2 := by
          calc
            _ = t * (a * (u * u⁻¹) ^ 2 - (d : ZMod q) * (u⁻¹) ^ 2) := by rw [hi]; ring
            _ = _ := by ring
        _ = 0 := by rw [hh, zero_mul]
  rw [completeKloosterman_eq]
  change (∑ u, F u) = _
  rw [sum_localize_eigenvalue (Equiv.addRight t) F c hc hF]
  apply sum_congr rfl
  intro u _
  by_cases hu : IsUnit u
  · simp only [hchar u hu, F, hu, if_true, true_and]
  · simp [F, hu]

theorem zmod_mul_modulus_eq_zero_iff (q r : ℕ) [NeZero q] [NeZero r]
    (z : ZMod (q * r)) :
    (r : ZMod (q * r)) * z = 0 ↔
      ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) z = 0 := by
  have hq (x : ZMod q) : ZMod.stdAddChar x = 1 ↔ x = 0 := by
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q)),
      ZMod.injective_stdAddChar.eq_iff]
  have hqr (x : ZMod (q * r)) : ZMod.stdAddChar x = 1 ↔ x = 0 := by
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := q * r)),
      ZMod.injective_stdAddChar.eq_iff]
  rw [← hqr, stdAddChar_mul_modulus_cast, hq]

/-- The remaining stationary condition is the actual quadratic congruence
`a u^2 = d (mod m)`. No primality, oddness, or unit-frequency assumption. -/
theorem completeKloosterman_square_modulus_localization (m : ℕ) [NeZero m]
    (a d : ℤ) :
    completeKloosterman (m * m) (a : ZMod (m * m)) d =
      ∑ u : ZMod (m * m),
        if IsUnit u ∧ (a : ZMod m) *
            (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 = (d : ZMod m)
        then ZMod.stdAddChar ((a : ZMod (m * m)) * u + (d : ZMod (m * m)) * u⁻¹)
        else 0 := by
  have ht : (m : ZMod (m * m)) ^ 2 = 0 := by
    rw [pow_two, ← Nat.cast_mul, ZMod.natCast_self]
  rw [completeKloosterman_square_zero_localization _ _ (m : ZMod (m * m)) _ ht]
  simp only [zmod_mul_modulus_eq_zero_iff, map_sub, map_mul, map_pow, map_intCast,
    sub_eq_zero]

theorem completeKloosterman_square_modulus_norm_le (m : ℕ) [NeZero m] (a d : ℤ) :
    ‖completeKloosterman (m * m) (a : ZMod (m * m)) d‖ ≤
      ((univ.filter fun u : ZMod (m * m) ↦ IsUnit u ∧
        (a : ZMod m) * (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 =
          (d : ZMod m)).card : ℝ) := by
  classical
  rw [completeKloosterman_square_modulus_localization]
  convert norm_sum_le univ (fun u : ZMod (m * m) ↦
    if IsUnit u ∧ (a : ZMod m) *
        (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 = (d : ZMod m)
    then ZMod.stdAddChar ((a : ZMod (m * m)) * u + (d : ZMod (m * m)) * u⁻¹)
    else 0) using 1
  simp only [apply_ite norm, stdAddChar_norm, norm_zero, sum_boole]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanPrimeSquare -/

/-!
# Unconditional square-root cancellation at prime-square moduli

The stationary-phase identity is evaluated using equal-sized reduction
fibers and the two-root bound in a field. This proves the primitive
prime-square case, including `p=2`; the prime-modulus Weil theorem is not used.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem zmod_reduction_fiber_card (q r : ℕ) [NeZero q] [NeZero r] (v : ZMod q) :
    (univ.filter fun u : ZMod (q * r) ↦
      ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) u = v).card = r := by
  classical
  let f := ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q)
  have hf := ZMod.castHom_surjective (Nat.dvd_mul_right q r)
  have hc (w : ZMod q) :
      (univ.filter fun u : ZMod (q * r) ↦ f u = w).card =
        (univ.filter fun u : ZMod (q * r) ↦ f u = v).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f.toAddMonoidHom (hf w) (hf v)
  have hsum := sum_card_fiberwise_eq_card_filter
    (univ : Finset (ZMod (q * r))) (univ : Finset (ZMod q)) f
  simp only [hc, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mem_univ,
    filter_true] at hsum
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos q) hsum

theorem zmod_reduction_preimage_card (q r : ℕ) [NeZero q] [NeZero r]
    (s : Finset (ZMod q)) :
    (univ.filter fun u : ZMod (q * r) ↦
      ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) u ∈ s).card = s.card * r := by
  classical
  rw [← sum_card_fiberwise_eq_card_filter, sum_congr rfl (fun v _ ↦
    zmod_reduction_fiber_card q r v), sum_const, nsmul_eq_mul]
  rfl

theorem completeKloosterman_square_modulus_norm_le_roots (m : ℕ) [NeZero m]
    (a d : ℤ) :
    ‖completeKloosterman (m * m) (a : ZMod (m * m)) d‖ ≤
      (m : ℝ) * ((univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 =
        (d : ZMod m)).card : ℝ) := by
  classical
  refine (completeKloosterman_square_modulus_norm_le m a d).trans ?_
  let s := univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 = (d : ZMod m)
  have hle : (univ.filter fun u : ZMod (m * m) ↦ IsUnit u ∧
      (a : ZMod m) * (ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u) ^ 2 =
        (d : ZMod m)).card ≤
      (univ.filter fun u : ZMod (m * m) ↦
        ZMod.castHom (Nat.dvd_mul_right m m) (ZMod m) u ∈ s).card := by
    apply card_le_card
    intro u hu
    simp only [mem_filter, mem_univ, true_and, s] at hu ⊢
    exact hu.2
  rw [zmod_reduction_preimage_card] at hle
  exact_mod_cast (hle.trans_eq (Nat.mul_comm s.card m))


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerRoots -/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_isUnit_of_reduction_ne_zero (p k : ℕ) [Fact p.Prime]
    (hk : 1 ≤ k) (x : ZMod (p ^ k))
    (hx : ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p) x ≠ 0) :
    IsUnit x := by
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
  intro hd
  apply hx
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff]
  exact hd

theorem oddPrimePower_intCast_isUnit (p k : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) : IsUnit (a : ZMod (p ^ k)) := by
  rcases k with _ | k
  · change IsUnit (a : ZMod 1)
    rw [Subsingleton.elim (a : ZMod 1) 1]
    exact isUnit_one
  apply oddPrimePower_isUnit_of_reduction_ne_zero p (k + 1) (by omega)
  intro hz
  exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp (by
    simpa only [map_intCast] using hz))

theorem oddPrimePower_sq_eq_sq (p k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : 1 ≤ k) (u v : ZMod (p ^ k)) (hu : IsUnit u)
    (he : u ^ 2 = v ^ 2) : u = v ∨ u = -v := by
  let f := ZMod.castHom (dvd_pow_self p (by omega : k ≠ 0)) (ZMod p)
  have hu0 : f u ≠ 0 := (hu.map f).ne_zero
  have hp0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).elim (Fact.out : p.Prime).ne_one hp2
  have hprod : (u - v) * (u + v) = 0 := by linear_combination he
  by_cases hs : f (u + v) = 0
  · have ht : f (u - v) ≠ 0 := by
      intro ht
      have hh : (2 : ZMod p) * f u = 0 := by
        simp only [map_add] at hs
        simp only [map_sub] at ht
        linear_combination hs + ht
      exact (mul_ne_zero hp0 hu0) hh
    have hv := oddPrimePower_isUnit_of_reduction_ne_zero p k hk (u - v) ht
    right
    exact eq_neg_of_add_eq_zero_left ((hv.mul_right_eq_zero).mp hprod)
  · have hv := oddPrimePower_isUnit_of_reduction_ne_zero p k hk (u + v) hs
    left
    exact sub_eq_zero.mp ((hv.mul_left_eq_zero).mp hprod)

theorem oddPrimePower_quadratic_root_card_le_two (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 1 ≤ k) (a d : ZMod (p ^ k))
    (ha : IsUnit a) (hd : IsUnit d) :
    (univ.filter fun u : ZMod (p ^ k) ↦ a * u ^ 2 = d).card ≤ 2 := by
  classical
  let s := univ.filter fun u : ZMod (p ^ k) ↦ a * u ^ 2 = d
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv⟩ := hs
    have hv' : a * v ^ 2 = d := (mem_filter.mp hv).2
    have hsub : s ⊆ {v, -v} := by
      intro u hu
      have hu' := (mem_filter.mp hu).2
      have huunit : IsUnit u := by
        have : IsUnit (a * u ^ 2) := hu'.symm ▸ hd
        exact (isUnit_pow_iff (by omega : 2 ≠ 0)).mp (isUnit_of_mul_isUnit_right this)
      have he : u ^ 2 = v ^ 2 := ha.mul_left_cancel (hu'.trans hv'.symm)
      simpa only [mem_insert, mem_singleton] using
        oddPrimePower_sq_eq_sq p k hp2 hk u v huunit he
    exact (card_le_card hsub).trans (card_insert_le _ _ |>.trans (by simp))
  · change s.card ≤ 2
    rw [not_nonempty_iff_eq_empty.mp hs]
    simp

theorem completeKloosterman_odd_even_power_norm_le (p r : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hr : 1 ≤ r) (a d : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ r * p ^ r) (a : ZMod (p ^ r * p ^ r)) d‖ ≤
      2 * (p : ℝ) ^ r := by
  have hroot := oddPrimePower_quadratic_root_card_le_two p r hp2 hr
    (a : ZMod (p ^ r)) (d : ZMod (p ^ r))
    (oddPrimePower_intCast_isUnit p r a ha) (oddPrimePower_intCast_isUnit p r d hd)
  have hR : ((univ.filter fun u : ZMod (p ^ r) ↦ (a : ZMod (p ^ r)) * u ^ 2 =
      (d : ZMod (p ^ r))).card : ℝ) ≤ 2 := by exact_mod_cast hroot
  refine (completeKloosterman_square_modulus_norm_le_roots (p ^ r) a d).trans ?_
  simpa only [Nat.cast_pow, mul_comm] using
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (p ^ r) : (0 : ℝ) ≤ (p ^ r : ℕ))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerGauss -/

/-!
Elementary quadratic Gauss cancellation by translation and additive orthogonality.
The linear coefficient is unrestricted; no multiplicative character is used.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_quadratic_gauss_norm (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (A B : ZMod p) (hA : A ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (A * x ^ 2 + B * x)‖ = Real.sqrt (p : ℝ) := by
  classical
  let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  let S := ∑ x : ZMod p, ψ (A * x ^ 2 + B * x)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).elim (Fact.out : p.Prime).ne_one hp2
  have hs : S * starRingEnd ℂ S = (p : ℂ) := by
    calc
      _ = ∑ x : ZMod p, ∑ y : ZMod p,
          ψ (A * x ^ 2 + B * x - (A * y ^ 2 + B * y)) := by
        simp only [S, map_sum, sum_mul, mul_sum, sub_eq_add_neg,
          AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
        exact sum_comm
      _ = ∑ y : ZMod p, ∑ x : ZMod p,
          ψ (A * (x + y) ^ 2 + B * (x + y) - (A * y ^ 2 + B * y)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro y _
        exact (Equiv.sum_comp (Equiv.addRight y)
          (fun x ↦ ψ (A * x ^ 2 + B * x - (A * y ^ 2 + B * y)))).symm
      _ = ∑ x : ZMod p, ψ (A * x ^ 2 + B * x) *
          ∑ y : ZMod p, ψ ((2 * A * x) * y) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro x _
        rw [mul_sum]
        apply sum_congr rfl
        intro y _
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      _ = (p : ℂ) := by
        rw [sum_eq_single 0]
        · simp only [mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero,
            AddChar.map_zero_eq_one, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
            mul_one, one_mul]
        · intro x _ hx
          have hzero : ∑ y : ZMod p, ψ ((2 * A * x) * y) = 0 :=
            AddChar.sum_eq_zero_of_ne_one
              (ZMod.isPrimitive_stdAddChar p (mul_ne_zero (mul_ne_zero htwo hA) hx))
          rw [hzero, mul_zero]
        · simp
  have hsq : ‖S‖ ^ 2 = (p : ℝ) := by
    have he := (Complex.mul_conj S).symm.trans hs
    rw [Complex.normSq_eq_norm_sq] at he
    exact_mod_cast he
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Nat.cast_nonneg p)]
  exact hsq

theorem oddPrimePower_sum_reduction (q r : ℕ) [NeZero q] [NeZero r]
    (F : ZMod q → ℂ) :
    (∑ x : ZMod (q * r), F (ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q) x)) =
      (r : ℂ) * ∑ y : ZMod q, F y := by
  classical
  let f := ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q)
  calc
    _ = ∑ y : ZMod q, ∑ x ∈ univ.filter (fun x ↦ f x = y), F (f x) :=
      (sum_fiberwise univ f (fun x ↦ F (f x))).symm
    _ = ∑ y : ZMod q, (r : ℂ) * F y := by
      apply sum_congr rfl
      intro y _
      rw [sum_congr rfl (fun x hx ↦ congrArg F (mem_filter.mp hx).2)]
      simp only [sum_const, nsmul_eq_mul, f, zmod_reduction_fiber_card]
    _ = _ := (mul_sum _ _ _).symm

private theorem oddPrimePower_shifted_inverse_product {q : ℕ} (u t : ZMod q)
    (hu : IsUnit u) (ht : t ^ 3 = 0) :
    (u + t) * (u⁻¹ - t * (u⁻¹) ^ 2 + t ^ 2 * (u⁻¹) ^ 3) = 1 := by
  have hi := ZMod.mul_inv_of_unit u hu
  linear_combination (1 - t * u⁻¹ + t ^ 2 * (u⁻¹) ^ 2) * hi + (u⁻¹) ^ 3 * ht

theorem oddPrimePower_isUnit_add_cube_zero {q : ℕ} (u t : ZMod q)
    (ht : t ^ 3 = 0) : IsUnit (u + t) ↔ IsUnit u := by
  have step (v s : ZMod q) (hv : IsUnit v) (hs : s ^ 3 = 0) : IsUnit (v + s) :=
    isUnit_iff_exists_inv.mpr ⟨_, oddPrimePower_shifted_inverse_product v s hv hs⟩
  constructor
  · intro hu
    simpa only [add_neg_cancel_right] using step (u + t) (-t) hu (by
      rw [neg_pow, ht, mul_zero])
  · exact fun hu ↦ step u t hu ht

theorem oddPrimePower_inv_add_cube_zero {q : ℕ} (u t : ZMod q)
    (hu : IsUnit u) (ht : t ^ 3 = 0) :
    (u + t)⁻¹ = u⁻¹ - t * (u⁻¹) ^ 2 + t ^ 2 * (u⁻¹) ^ 3 := by
  have hs := oddPrimePower_shifted_inverse_product u t hu ht
  have hi := ZMod.inv_mul_of_unit (u + t)
    ((oddPrimePower_isUnit_add_cube_zero u t ht).mpr hu)
  calc
    _ = (u + t)⁻¹ * ((u + t) * (u⁻¹ - t * (u⁻¹) ^ 2 + t ^ 2 * (u⁻¹) ^ 3)) := by
      rw [hs, mul_one]
    _ = _ := by rw [← mul_assoc, hi, one_mul]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerStationary -/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem oddPrimePower_annihilator (q m n : ℕ) [NeZero q] [NeZero m]
    [NeZero n] (hq : q = m * n) (h : m ∣ q) (z : ZMod q) :
    (n : ZMod q) * z = 0 ↔ ZMod.castHom h (ZMod m) z = 0 := by
  subst q
  exact zmod_mul_modulus_eq_zero_iff m n z

theorem oddPrimePower_localization (p m : ℕ) [NeZero p] [NeZero m] (a d : ℤ) :
    completeKloosterman (p * (m * m)) (a : ZMod (p * (m * m))) d =
      ∑ u : ZMod (p * (m * m)),
        if IsUnit u ∧ (a : ZMod m) *
          (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
            (d : ZMod m)
        then ZMod.stdAddChar ((a : ZMod (p * (m * m))) * u +
          (d : ZMod (p * (m * m))) * u⁻¹) else 0 := by
  have ht : ((p * m : ℕ) : ZMod (p * (m * m))) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact ⟨p, by ring⟩
  rw [completeKloosterman_square_zero_localization _ _ (p * m : ℕ) _ ht]
  simp only [oddPrimePower_annihilator _ m (p * m) (by ring)
    (show m ∣ p * (m * m) from ⟨p * m, by ring⟩),
    map_sub, map_mul, map_pow, map_intCast, sub_eq_zero]

theorem oddPrimePower_layer_cube_zero (p m : ℕ) [NeZero p] [NeZero m]
    (hpm : p ∣ m) : (m : ZMod (p * (m * m))) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  obtain ⟨n, hn⟩ := hpm
  exact ⟨n, by rw [hn]; ring⟩

theorem oddPrimePower_stationary_shift (p m : ℕ) [NeZero p] [NeZero m]
    (hpm : p ∣ m) (a d : ℤ) (u t : ZMod (p * (m * m))) :
    (IsUnit (u + (m : ZMod (p * (m * m))) * t) ∧
      (a : ZMod m) *
        (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m)
          (u + (m : ZMod (p * (m * m))) * t)) ^ 2 = (d : ZMod m)) ↔
    (IsUnit u ∧ (a : ZMod m) *
      (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
        (d : ZMod m)) := by
  have ht : ((m : ZMod (p * (m * m))) * t) ^ 3 = 0 := by
    rw [mul_pow, oddPrimePower_layer_cube_zero p m hpm, zero_mul]
  rw [oddPrimePower_isUnit_add_cube_zero _ _ ht]
  simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]

theorem oddPrimePower_stationary_linear_coefficient (p m : ℕ) [NeZero p] [NeZero m]
    (a d : ℤ) (u : ZMod (p * (m * m))) (hu : IsUnit u)
    (hs : (a : ZMod m) *
      (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
        (d : ZMod m)) :
    ∃ c : ℕ, (a : ZMod (p * (m * m))) - (d : ZMod (p * (m * m))) * (u⁻¹) ^ 2 =
      (m : ZMod (p * (m * m))) * (c : ZMod (p * (m * m))) := by
  let f := ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m)
  let L : ZMod (p * (m * m)) := (a : ZMod (p * (m * m))) -
    (d : ZMod (p * (m * m))) * (u⁻¹) ^ 2
  have hi : f u * f u⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
  have hL : f L = 0 := by
    simp only [L, map_sub, map_mul, map_pow, map_intCast]
    change (a : ZMod m) * f u ^ 2 = (d : ZMod m) at hs
    linear_combination (f u⁻¹) ^ 2 * hs - (a : ZMod m) * (f u * f u⁻¹ + 1) * hi
  have hval : m ∣ L.val := by
    apply (ZMod.natCast_eq_zero_iff L.val m).mp
    rw [← map_natCast f, ZMod.natCast_zmod_val]
    exact hL
  obtain ⟨c, hc⟩ := hval
  refine ⟨c, ?_⟩
  change L = _
  rw [← ZMod.natCast_zmod_val L, hc, Nat.cast_mul]

theorem oddPrimePower_stationary_phase (p m : ℕ) [NeZero p] [NeZero m]
    (hpm : p ∣ m) (a d : ℤ) (u t : ZMod (p * (m * m))) (hu : IsUnit u)
    (c : ℕ) (hc : (a : ZMod (p * (m * m))) -
      (d : ZMod (p * (m * m))) * (u⁻¹) ^ 2 =
        (m : ZMod (p * (m * m))) * (c : ZMod (p * (m * m)))) :
    ZMod.stdAddChar ((a : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t) +
      (d : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t)⁻¹) =
    ZMod.stdAddChar ((a : ZMod (p * (m * m))) * u +
      (d : ZMod (p * (m * m))) * u⁻¹) *
    ZMod.stdAddChar
      (ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p)
          ((d : ZMod (p * (m * m))) * (u⁻¹) ^ 3) *
        (ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p) t) ^ 2 +
      (c : ZMod p) * ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p) t) := by
  have ht : ((m : ZMod (p * (m * m))) * t) ^ 3 = 0 := by
    rw [mul_pow, oddPrimePower_layer_cube_zero p m hpm, zero_mul]
  rw [oddPrimePower_inv_add_cube_zero u _ hu ht]
  have he :
      (a : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t) +
        (d : ZMod (p * (m * m))) *
          (u⁻¹ - ((m : ZMod (p * (m * m))) * t) * (u⁻¹) ^ 2 +
            ((m : ZMod (p * (m * m))) * t) ^ 2 * (u⁻¹) ^ 3) =
      ((a : ZMod (p * (m * m))) * u + (d : ZMod (p * (m * m))) * u⁻¹) +
        ((m * m : ℕ) : ZMod (p * (m * m))) *
          ((d : ZMod (p * (m * m))) * (u⁻¹) ^ 3 * t ^ 2 +
            (c : ZMod (p * (m * m))) * t) := by
    push_cast
    linear_combination (m : ZMod (p * (m * m))) * t * hc
  rw [he, AddChar.map_add_eq_mul, stdAddChar_mul_modulus_cast]
  simp only [map_add, map_mul, map_pow, map_natCast]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePowerNorm -/

/-!
Average the localized complete sum over translations by `m`. Each stationary
orbit has a genuine quadratic Gauss norm. This retains the square-root saving
at moduli `p * m²`, rather than estimating the orbit term by term.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_stationary_orbit_norm (p m : ℕ) [Fact p.Prime] [NeZero m]
    (hp2 : p ≠ 2) (hpm : p ∣ m) (a d : ℤ) (hd : ¬ (p : ℤ) ∣ d)
    (u : ZMod (p * (m * m))) (hu : IsUnit u)
    (hs : (a : ZMod m) *
      (ZMod.castHom (show m ∣ p * (m * m) from ⟨p * m, by ring⟩) (ZMod m) u) ^ 2 =
        (d : ZMod m)) :
    ‖∑ t : ZMod (p * (m * m)),
      ZMod.stdAddChar ((a : ZMod (p * (m * m))) *
        (u + (m : ZMod (p * (m * m))) * t) +
        (d : ZMod (p * (m * m))) * (u + (m : ZMod (p * (m * m))) * t)⁻¹)‖ =
      ((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ) := by
  obtain ⟨c, hc⟩ := oddPrimePower_stationary_linear_coefficient p m a d u hu hs
  let f := ZMod.castHom (Nat.dvd_mul_right p (m * m)) (ZMod p)
  let A : ZMod p := f ((d : ZMod (p * (m * m))) * (u⁻¹) ^ 3)
  have hui : IsUnit u⁻¹ := by
    obtain ⟨v, rfl⟩ := hu
    simpa only [ZMod.inv_coe_unit] using (v⁻¹).isUnit
  have hA : A ≠ 0 := by
    simp only [A, map_mul, map_pow, map_intCast]
    exact mul_ne_zero
      (fun h ↦ hd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h))
      (pow_ne_zero _ ((hui.map f).ne_zero))
  simp_rw [oddPrimePower_stationary_phase p m hpm a d u _ hu c hc]
  change ‖∑ t : ZMod (p * (m * m)),
    ZMod.stdAddChar ((a : ZMod (p * (m * m))) * u +
      (d : ZMod (p * (m * m))) * u⁻¹) *
    ZMod.stdAddChar (A * f t ^ 2 + (c : ZMod p) * f t)‖ = _
  rw [← mul_sum, oddPrimePower_sum_reduction p (m * m)
    (fun t ↦ ZMod.stdAddChar (A * t ^ 2 + (c : ZMod p) * t))]
  rw [norm_mul, stdAddChar_norm, one_mul, norm_mul, Complex.norm_natCast,
    oddPrimePower_quadratic_gauss_norm p hp2 A (c : ZMod p) hA]

private theorem oddPrimePower_preimage_card (q m n : ℕ) [NeZero q] [NeZero m]
    [NeZero n] (hq : q = m * n) (h : m ∣ q) (s : Finset (ZMod m)) :
    (univ.filter fun u : ZMod q ↦ ZMod.castHom h (ZMod m) u ∈ s).card = s.card * n := by
  subst q
  exact zmod_reduction_preimage_card m n s

theorem completeKloosterman_odd_square_layer_norm_le_roots (p m : ℕ)
    [Fact p.Prime] [NeZero m] (hp2 : p ≠ 2) (hpm : p ∣ m)
    (a d : ℤ) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p * (m * m)) (a : ZMod (p * (m * m))) d‖ ≤
      (m : ℝ) * Real.sqrt (p : ℝ) *
        ((univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 = (d : ZMod m)).card : ℝ) := by
  classical
  let q := p * (m * m)
  let f := ZMod.castHom (show m ∣ q from ⟨p * m, by dsimp [q]; ring⟩) (ZMod m)
  let S : ZMod q → Prop := fun u ↦ IsUnit u ∧ (a : ZMod m) * f u ^ 2 = (d : ZMod m)
  let F : ZMod q → ℂ := fun u ↦ if S u then
    ZMod.stdAddChar ((a : ZMod q) * u + (d : ZMod q) * u⁻¹) else 0
  let R := univ.filter fun v : ZMod m ↦ (a : ZMod m) * v ^ 2 = (d : ZMod m)
  have hloc : completeKloosterman q (a : ZMod q) d = ∑ u, F u :=
    oddPrimePower_localization p m a d
  have hS (u t : ZMod q) : S (u + (m : ZMod q) * t) ↔ S u :=
    oddPrimePower_stationary_shift p m hpm a d u t
  have horbit (u : ZMod q) :
      ‖∑ t : ZMod q, F (u + (m : ZMod q) * t)‖ =
        if S u then ((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ) else 0 := by
    simp only [F, hS]
    by_cases hu : S u
    · simp only [hu, if_true]
      exact oddPrimePower_stationary_orbit_norm p m hp2 hpm a d hd u hu.1 hu.2
    · simp only [hu, if_false, sum_const_zero, norm_zero]
  have havg : (q : ℂ) * completeKloosterman q (a : ZMod q) d =
      ∑ u : ZMod q, ∑ t : ZMod q, F (u + (m : ZMod q) * t) := by
    have ht (t : ZMod q) :
        ∑ u : ZMod q, F (u + (m : ZMod q) * t) =
          completeKloosterman q (a : ZMod q) d :=
      (Equiv.sum_comp (Equiv.addRight ((m : ZMod q) * t)) F).trans hloc.symm
    rw [sum_comm]
    simp only [ht, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have hN : (q : ℝ) * ‖completeKloosterman q (a : ZMod q) d‖ ≤
      ((univ.filter S).card : ℝ) * (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := by
    have hn := norm_sum_le univ (fun u : ZMod q ↦ ∑ t : ZMod q,
      F (u + (m : ZMod q) * t))
    rw [← havg, norm_mul, Complex.norm_natCast] at hn
    simp_rw [horbit] at hn
    have he : (∑ u : ZMod q,
        if S u then ((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ) else 0) =
        ((univ.filter S).card : ℝ) * (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := by
      calc
        _ = (∑ u : ZMod q, if S u then (1 : ℝ) else 0) *
            (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := by
          rw [sum_mul]
          apply sum_congr rfl
          intro u _
          split_ifs <;> simp
        _ = _ := by rw [sum_boole]
    exact hn.trans_eq he
  have hcard : (univ.filter S).card ≤ R.card * (p * m) := by
    calc
      _ ≤ (univ.filter fun u : ZMod q ↦ f u ∈ R).card := by
        apply card_le_card
        intro u hu
        simp only [mem_filter, mem_univ, true_and, S, R] at hu ⊢
        exact hu.2
      _ = _ := oddPrimePower_preimage_card q m (p * m) (by dsimp [q]; ring) _ R
  have hbound : (q : ℝ) * ‖completeKloosterman q (a : ZMod q) d‖ ≤
      (q : ℝ) * ((m : ℝ) * Real.sqrt (p : ℝ) * (R.card : ℝ)) := by
    calc
      _ ≤ ((univ.filter S).card : ℝ) *
          (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) := hN
      _ ≤ ((R.card * (p * m) : ℕ) : ℝ) *
          (((m * m : ℕ) : ℝ) * Real.sqrt (p : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by dsimp [q]; push_cast; ring
  exact le_of_mul_le_mul_left hbound (show (0 : ℝ) < q by exact_mod_cast (NeZero.pos q))

theorem completeKloosterman_odd_odd_power_norm_le (p r : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hr : 1 ≤ r) (a d : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p * (p ^ r * p ^ r)) (a : ZMod (p * (p ^ r * p ^ r))) d‖ ≤
      2 * (p : ℝ) ^ r * Real.sqrt (p : ℝ) := by
  have hroot := oddPrimePower_quadratic_root_card_le_two p r hp2 hr
    (a : ZMod (p ^ r)) (d : ZMod (p ^ r))
    (oddPrimePower_intCast_isUnit p r a ha) (oddPrimePower_intCast_isUnit p r d hd)
  have hR : ((univ.filter fun u : ZMod (p ^ r) ↦ (a : ZMod (p ^ r)) * u ^ 2 =
      (d : ZMod (p ^ r))).card : ℝ) ≤ 2 := by exact_mod_cast hroot
  refine (completeKloosterman_odd_square_layer_norm_le_roots p (p ^ r) hp2
    (dvd_pow_self p (by omega)) a d hd).trans ?_
  calc
    _ ≤ ((p ^ r : ℕ) : ℝ) * Real.sqrt (p : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    _ = _ := by push_cast; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovHasse -/

/-!
# Hasse differentiation in Stepanov's construction

The divisibility, linear operator, and degree estimates below formalize
Lemma 10 of Gergely Harcos, *Weil's bound for
Kloosterman sums*, printed page 10 (`harcos-weil.pdf`).

The operator is polynomial division of `hasseDeriv k (g * f ^ n)` by
`f ^ (n - k)`. Its factorization is proved, not assumed. No monicity or
characteristic restriction is needed.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

/-- The power forced by Leibniz's rule divides the Hasse derivative.
The truncated exponent also makes the statement valid when `n < k`. -/
theorem stepanov_pow_dvd_hasseDeriv_mul_pow
    {R : Type*} [CommRing R] (f g : R[X]) (n k : ℕ) :
    f ^ (n - k) ∣ hasseDeriv k (g * f ^ n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      by_cases hkn : n + 1 ≤ k
      · simp [Nat.sub_eq_zero_of_le hkn]
      have hkn' : k ≤ n := by omega
      rw [pow_succ, ← mul_assoc, hasseDeriv_mul]
      apply Finset.dvd_sum
      intro ij hij
      have hij' : ij.1 + ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      by_cases hj : ij.2 = 0
      · have hi : ij.1 = k := by omega
        simp only [hj, hi, hasseDeriv_zero, LinearMap.id_apply]
        have he : n + 1 - k = (n - k) + 1 := by omega
        rw [he, pow_succ]
        exact mul_dvd_mul_right (ih k) f
      · have he : n + 1 - k ≤ n - ij.1 := by omega
        exact dvd_mul_of_dvd_left ((pow_dvd_pow f he).trans (ih ij.1)) _

variable {F : Type*} [Field F]

private theorem stepanov_hasse_div_mul (f : F[X]) (hf : f ≠ 0)
    (n k : ℕ) (g : F[X]) :
    (hasseDeriv k (g * f ^ n) / f ^ (n - k)) * f ^ (n - k) =
      hasseDeriv k (g * f ^ n) := by
  rw [mul_comm]
  exact EuclideanDomain.mul_div_cancel' (pow_ne_zero _ hf)
    (stepanov_pow_dvd_hasseDeriv_mul_pow f g n k)

/-- Harcos's `g ↦ g⁽ᵏ⁾` as an actual linear map, for every nonzero `f`.
It is defined for all `k`; the degree estimate below uses `k ≤ n`. -/
def stepanovHasseOperator (f : F[X]) (hf : f ≠ 0) (n k : ℕ) :
    F[X] →ₗ[F] F[X] where
  toFun g := hasseDeriv k (g * f ^ n) / f ^ (n - k)
  map_add' g h := by
    apply mul_right_cancel₀ (pow_ne_zero (n - k) hf)
    rw [stepanov_hasse_div_mul f hf]
    simp only [add_mul, stepanov_hasse_div_mul f hf, map_add]
  map_smul' c g := by
    apply mul_right_cancel₀ (pow_ne_zero (n - k) hf)
    rw [stepanov_hasse_div_mul f hf]
    simp only [RingHom.id_apply, smul_mul_assoc, stepanov_hasse_div_mul f hf, map_smul]


/-- The factorization in Harcos Lemma 10, including the endpoint `k = n`. -/
theorem stepanovHasseOperator_spec (f : F[X]) (hf : f ≠ 0)
    (n k : ℕ) (g : F[X]) :
    hasseDeriv k (g * f ^ n) =
      stepanovHasseOperator f hf n k g * f ^ (n - k) :=
  (stepanov_hasse_div_mul f hf n k g).symm


/-- The natural-degree form of Harcos's estimate; valid also for `g = 0`. -/
theorem stepanovHasseOperator_natDegree_le (f : F[X]) (hf : f ≠ 0)
    (n k : ℕ) (hkn : k ≤ n) (hm : 1 ≤ f.natDegree) (g : F[X]) :
    (stepanovHasseOperator f hf n k g).natDegree ≤
      g.natDegree + k * (f.natDegree - 1) := by
  by_cases hq : stepanovHasseOperator f hf n k g = 0
  · simp only [hq, natDegree_zero, zero_le]
  have hg : g ≠ 0 := by
    intro hg
    apply hq
    rw [hg, map_zero]
  have hd := natDegree_hasseDeriv_le (g * f ^ n) k
  rw [stepanovHasseOperator_spec f hf n k g,
    natDegree_mul hq (pow_ne_zero _ hf),
    natDegree_mul hg (pow_ne_zero _ hf), natDegree_pow, natDegree_pow] at hd
  have hkm : k ≤ g.natDegree + n * f.natDegree := by nlinarith
  have hnm : (n - k) * f.natDegree + k * f.natDegree = n * f.natDegree := by
    rw [← add_mul, Nat.sub_add_cancel hkn]
  have hkm' : k * (f.natDegree - 1) + k = k * f.natDegree := by
    calc
      k * (f.natDegree - 1) + k = k * ((f.natDegree - 1) + 1) := by ring
      _ = k * f.natDegree := by rw [Nat.sub_add_cancel hm]
  have hsub := Nat.sub_add_cancel hkm
  omega

/-- The strict degree bound used to size Stepanov's coefficient system.
Unlike a `natDegree < B` hypothesis, `degree < B` handles `g = 0`, even
when `B = 0`. -/
theorem stepanovHasseOperator_degree_lt (f : F[X]) (hf : f ≠ 0)
    (n k B : ℕ) (hkn : k ≤ n) (hm : 1 ≤ f.natDegree)
    (g : F[X]) (hg : g.degree < (B : WithBot ℕ)) :
    (stepanovHasseOperator f hf n k g).degree <
      ((B + k * (f.natDegree - 1) : ℕ) : WithBot ℕ) := by
  by_cases hq : stepanovHasseOperator f hf n k g = 0
  · rw [hq, degree_zero]
    exact WithBot.bot_lt_coe _
  have hg0 : g ≠ 0 := by
    intro hg0
    apply hq
    rw [hg0, map_zero]
  rw [degree_eq_natDegree hg0] at hg
  rw [degree_eq_natDegree hq]
  exact_mod_cast lt_of_le_of_lt
    (stepanovHasseOperator_natDegree_le f hf n k hkn hm g)
    (Nat.add_lt_add_right (WithBot.coe_lt_coe.mp hg) _)

/-- Harcos Lemma 8: vanishing of the first Hasse derivatives is exactly
divisibility by the corresponding power of the linear factor. -/
theorem stepanov_hasse_vanishing_iff_pow_dvd
    {R : Type*} [CommRing R] (h : R[X]) (x : R) (ell : ℕ) :
    (∀ k < ell, (hasseDeriv k h).eval x = 0) ↔
      (X - C x) ^ ell ∣ h := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  simp only [← taylor_apply, taylor_coeff]

/-- The sum of root multiplicities over any finite set is at most the degree. -/
theorem stepanov_sum_rootMultiplicity_le (h : F[X]) (s : Finset F) :
    ∑ x ∈ s, h.rootMultiplicity x ≤ h.natDegree := by
  classical
  calc
    ∑ x ∈ s, h.rootMultiplicity x = ∑ x ∈ s, h.roots.count x := by
      simp only [count_roots]
    _ ≤ ∑ x ∈ s ∪ h.roots.toFinset, h.roots.count x :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (by intros; exact Nat.zero_le _)
    _ = ∑ x ∈ h.roots.toFinset, h.roots.count x := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x _ hx
      exact Multiset.count_eq_zero.mpr (by simpa only [Multiset.mem_toFinset] using hx)
    _ = h.roots.card := Multiset.toFinset_sum_count_eq _
    _ ≤ h.natDegree := card_roots' h

/-- Finite-root degree bound with a possibly different vanishing order at
each point. The nonzero hypothesis is essential here. -/
theorem stepanov_sum_hasse_orders_le (h : F[X]) (hh : h ≠ 0)
    (s : Finset F) (orders : F → ℕ)
    (hv : ∀ x ∈ s, ∀ k < orders x, (hasseDeriv k h).eval x = 0) :
    ∑ x ∈ s, orders x ≤ h.natDegree := by
  calc
    ∑ x ∈ s, orders x ≤ ∑ x ∈ s, h.rootMultiplicity x := by
      apply Finset.sum_le_sum
      intro x hx
      exact (le_rootMultiplicity_iff hh).mpr
        ((stepanov_hasse_vanishing_iff_pow_dvd h x (orders x)).mp (hv x hx))
    _ ≤ h.natDegree := stepanov_sum_rootMultiplicity_le h s

/-- If a nonzero polynomial vanishes to Hasse order at least `ell` at every
point of a finite set, then `ell` times the number of points is at most its degree. -/
theorem stepanov_card_mul_hasse_order_le (h : F[X]) (hh : h ≠ 0)
    (s : Finset F) (ell : ℕ)
    (hv : ∀ x ∈ s, ∀ k < ell, (hasseDeriv k h).eval x = 0) :
    s.card * ell ≤ h.natDegree := by
  simpa using
    stepanov_sum_hasse_orders_le h hh s (fun _ ↦ ell) hv

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovConstraints -/

/-!
# The actual finite-dimensional Stepanov equations

The two polynomial families have degree strictly less than the integer `B`.
The `k`th equation is Harcos (22), with its two distinct Hasse operators.
No rank or nonzero-solution hypothesis is imposed on the equation matrix.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset Module

variable {F : Type*} [Field F]

def stepanovConstraint (f : F[X]) (hf : f ≠ 0) (ell e : ℕ) (a : F)
    (k : ℕ) {J : ℕ} (r s : Fin J → F[X]) : F[X] :=
  ∑ j, (stepanovHasseOperator f hf ell k (r j) +
    a • stepanovHasseOperator f hf (ell + e) k (s j)) * X ^ j.val

theorem stepanovConstraint_degree_lt (f : F[X]) (hf : f ≠ 0)
    (ell e B J k : ℕ) (a : F) (hk : k ≤ ell) (hm : 1 ≤ f.natDegree)
    (hJ : 0 < J) (r s : Fin J → F[X])
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ)) :
    (stepanovConstraint f hf ell e a k r s).degree <
      ((B + k * (f.natDegree - 1) + (J - 1) : ℕ) : WithBot ℕ) := by
  apply mem_degreeLT.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_degreeLT.mpr
  rw [degree_mul_X_pow]
  have hr' := stepanovHasseOperator_degree_lt f hf ell k B hk hm (r j) (hr j)
  have hs' := stepanovHasseOperator_degree_lt f hf (ell + e) k B
    (by omega) hm (s j) (hs j)
  have hd := (degree_add_le _ _).trans_lt
    (max_lt hr' ((degree_smul_le a _).trans_lt hs'))
  calc
    _ < ((B + k * (f.natDegree - 1) : ℕ) : WithBot ℕ) + (j.val : WithBot ℕ) :=
      WithBot.add_lt_add_right (by simp) hd
    _ ≤ _ := by
      rw [← Nat.cast_add]
      exact_mod_cast Nat.add_le_add_left (show j.val ≤ J - 1 by omega) _

abbrev StepanovCoefficients (F : Type*) [Field F] (J B : ℕ) :=
  Fin J → degreeLT F B × degreeLT F B

def stepanovConstraintMap (f : F[X]) (hf : f ≠ 0)
    (ell e B J : ℕ) (a : F) (hm : 1 ≤ f.natDegree) (hJ : 0 < J) :
    StepanovCoefficients F J B →ₗ[F]
      (k : Fin ell) → degreeLT F (B + k.val * (f.natDegree - 1) + (J - 1)) where
  toFun v k := ⟨stepanovConstraint f hf ell e a k.val
      (fun j => (v j).1) (fun j => (v j).2),
    mem_degreeLT.mpr (stepanovConstraint_degree_lt f hf ell e B J k.val a
      (Nat.le_of_lt k.is_lt) hm hJ _ _
      (fun j => mem_degreeLT.mp (v j).1.property)
      (fun j => mem_degreeLT.mp (v j).2.property))⟩
  map_add' v w := by
    funext k
    apply Subtype.ext
    simp only [stepanovConstraint, Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Submodule.coe_add, map_add, smul_add, add_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  map_smul' c v := by
    funext k
    apply Subtype.ext
    simp only [stepanovConstraint, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Submodule.coe_smul, map_smul, RingHom.id_apply,
      Finset.smul_sum, smul_comm a c]
    apply sum_congr rfl
    intro j _
    rw [← smul_mul_assoc, smul_add]

theorem stepanovCoefficients_finrank (J B : ℕ) :
    finrank F (StepanovCoefficients F J B) = 2 * J * B := by
  have hB : finrank F (degreeLT F B) = B := by
    simpa using (finrank_eq_card_basis (degreeLT.basis F B))
  simp only [StepanovCoefficients, finrank_pi_fintype, finrank_prod, hB, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_cast
  ring

theorem stepanovConstraints_finrank (ell B J m : ℕ) :
    finrank F ((k : Fin ell) → degreeLT F (B + k.val * (m - 1) + (J - 1))) =
      ∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1)) := by
  rw [finrank_pi_fintype]
  apply sum_congr rfl
  intro k _
  simpa using (finrank_eq_card_basis
    (degreeLT.basis F (B + k.val * (m - 1) + (J - 1))))

/-- The precise integer equation count, strictly smaller than the `2JB`
unknown coefficients, produces a nontrivial solution of Harcos (22). -/
theorem stepanov_exists_coefficients (f : F[X]) (hf : f ≠ 0)
    (ell e B J : ℕ) (a : F) (hm : 1 ≤ f.natDegree) (hJ : 0 < J)
    (hcount : (∑ k : Fin ell, (B + k.val * (f.natDegree - 1) + (J - 1))) <
      2 * J * B) :
    ∃ r s : Fin J → F[X],
      (∀ j, (r j).degree < (B : WithBot ℕ)) ∧
      (∀ j, (s j).degree < (B : WithBot ℕ)) ∧
      (∃ j, r j ≠ 0 ∨ s j ≠ 0) ∧
      ∀ k < ell, stepanovConstraint f hf ell e a k r s = 0 := by
  classical
  let L := stepanovConstraintMap f hf ell e B J a hm hJ
  have hn : ¬ Function.Injective L := by
    intro hi
    have hd := LinearMap.finrank_le_finrank_of_injective hi
    rw [stepanovCoefficients_finrank, stepanovConstraints_finrank] at hd
    exact (not_lt_of_ge hd) hcount
  have hex : ∃ v, L v = 0 ∧ v ≠ 0 := by
    by_contra h
    apply hn
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv'
    exact h ⟨v, hv, hv'⟩
  obtain ⟨v, hv, hv0⟩ := hex
  refine ⟨(fun j => (v j).1), (fun j => (v j).2),
    (fun j => mem_degreeLT.mp (v j).1.property),
    (fun j => mem_degreeLT.mp (v j).2.property), ?_, ?_⟩
  · by_contra hn
    apply hv0
    funext j
    apply Prod.ext <;> apply Subtype.ext
    · by_contra h
      exact hn ⟨j, Or.inl h⟩
    · by_contra h
      exact hn ⟨j, Or.inr h⟩
  · intro k hk
    have he := congrArg (fun w => ((w ⟨k, hk⟩ :
      degreeLT F (B + k * (f.natDegree - 1) + (J - 1))) : F[X])) hv
    exact he

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovNonzero -/

/-!
# Nonvanishing of the Stepanov auxiliary polynomial

The argument is the first half of printed page 11 of Gergely Harcos,
*Weil's bound for Kloosterman sums*
(`pages/harcos-stepanov-11.png`).

The nonsquare hypothesis is geometric: it concerns the polynomial after
base change to the algebraic closure, not just squares over the finite field.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

variable {F : Type*} [Field F]

/-- A square times a polynomial cannot be a square unless that polynomial
is a square. Unique factorization supplies the required polynomial quotient. -/
private theorem stepanov_isSquare_of_sq_mul_eq_sq
    {K : Type*} [Field K] (f r t : K[X]) (hr : r ≠ 0)
    (h : r ^ 2 * f = t ^ 2) : IsSquare f := by
  have hdiv : r ^ 2 ∣ t ^ 2 := ⟨f, h.symm⟩
  obtain ⟨u, hu⟩ :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hdiv
  refine ⟨u, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hr)
  rw [h, hu]
  ring

/-- The geometric nonsquare obstruction used after reducing modulo `X^q`. -/
theorem stepanov_sq_mul_eq_const_mul_sq
    (f r s : F[X]) (c : F) (hc : c ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (h : r ^ 2 * f = s ^ 2 * C c) : r = 0 ∧ s = 0 := by
  have hr : r = 0 := by
    by_contra hr
    obtain ⟨a, ha⟩ :=
      IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) c)
        (by decide : 0 < 2)
    apply hf
    apply stepanov_isSquare_of_sq_mul_eq_sq
      (f.map (algebraMap F (AlgebraicClosure F)))
      (r.map (algebraMap F (AlgebraicClosure F)))
      (s.map (algebraMap F (AlgebraicClosure F)) * C a)
      (by simpa using hr)
    have hm := congrArg (Polynomial.map (algebraMap F (AlgebraicClosure F))) h
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      mul_pow, ← C_pow, ha] using hm
  refine ⟨hr, ?_⟩
  rw [hr, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  have hs : s ^ 2 = 0 := (mul_eq_zero.mp h.symm).resolve_right (by simpa using hc)
  by_contra hs0
  exact pow_ne_zero 2 hs0 hs

variable [Fintype F]

/-- Frobenius makes the constant term the entire residue of `f^q` modulo `X^q`. -/
theorem stepanov_X_card_dvd_pow_sub_const (f : F[X]) :
    X ^ Fintype.card F ∣ f ^ Fintype.card F - C (f.eval 0) := by
  obtain ⟨p, hp, n, hprime, hcard⟩ := FiniteField.card' F
  let : CharP F p := hp
  let : Fact p.Prime := ⟨hprime⟩
  have hd : (X : F[X]) ∣ f - C (f.eval 0) := by
    rw [X_dvd_iff]
    simp [coeff_zero_eq_eval_zero]
  have hpow := pow_dvd_pow_of_dvd hd (Fintype.card F)
  have he : (f - C (f.eval 0)) ^ Fintype.card F =
      f ^ Fintype.card F - C (f.eval 0) := by
    rw [hcard, sub_pow_char_pow, ← C_pow, ← hcard, FiniteField.pow_card]
  rwa [he] at hpow

omit [Fintype F] in
private theorem stepanov_natDegree_le_pred {r : F[X]} {B : ℕ}
    (hr : r.degree < (B : WithBot ℕ)) : r.natDegree ≤ B - 1 := by
  by_cases hzero : r = 0
  · simp [hzero]
  rw [degree_eq_natDegree hzero] at hr
  have hr' : r.natDegree < B := by exact_mod_cast hr
  omega

/-- Harcos's residue kernel lemma: a degree-bounded block cannot be divisible
by `X^q`. The degree convention includes zero polynomials even when `B = 0`. -/
theorem stepanov_block_eq_zero_of_X_card_dvd
    (f r s : F[X]) (B : ℕ)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : r.degree < (B : WithBot ℕ)) (hs : s.degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hdiv : X ^ Fintype.card F ∣ r + s * f ^ ((Fintype.card F - 1) / 2)) :
    r = 0 ∧ s = 0 := by
  have he : 2 * ((Fintype.card F - 1) / 2) + 1 = Fintype.card F := by
    obtain ⟨k, hk⟩ := hq
    omega
  have hp : (f ^ ((Fintype.card F - 1) / 2)) ^ 2 * f =
      f ^ Fintype.card F := by
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega
  have hd₁ : X ^ Fintype.card F ∣ r ^ 2 * f - s ^ 2 * f ^ Fintype.card F := by
    have hd := dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left hdiv (r - s * f ^ ((Fintype.card F - 1) / 2))) f
    convert hd using 1
    rw [← hp]
    ring
  have hd₂ := dvd_mul_of_dvd_right (stepanov_X_card_dvd_pow_sub_const f) (s ^ 2)
  have hd : X ^ Fintype.card F ∣ r ^ 2 * f - s ^ 2 * C (f.eval 0) := by
    convert dvd_add hd₁ hd₂ using 1
    ring
  have hrB := stepanov_natDegree_le_pred hr
  have hsB := stepanov_natDegree_le_pred hs
  have hdr : (r ^ 2 * f).natDegree ≤ 2 * (B - 1) + f.natDegree := by
    calc
      _ ≤ (r ^ 2).natDegree + f.natDegree := natDegree_mul_le
      _ ≤ _ := by rw [natDegree_pow]; omega
  have hds : (s ^ 2 * C (f.eval 0)).natDegree ≤ 2 * (B - 1) + f.natDegree := by
    calc
      _ ≤ (s ^ 2).natDegree + (C (f.eval 0)).natDegree := natDegree_mul_le
      _ ≤ _ := by rw [natDegree_pow, natDegree_C]; omega
  have hz : r ^ 2 * f - s ^ 2 * C (f.eval 0) = 0 := by
    apply eq_zero_of_dvd_of_natDegree_lt hd
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt
      ((natDegree_sub_le _ _).trans (max_le hdr hds)) hB
  exact stepanov_sq_mul_eq_const_mul_sq f r s (f.eval 0) hf0 hf (sub_eq_zero.mp hz)

/-- The actual Stepanov block ansatz, before multiplication by `f^ell`. -/
def stepanovAnsatz (f : F[X]) {J : ℕ} (r s : Fin J → F[X]) : F[X] :=
  ∑ j : Fin J,
    (r j + s j * f ^ ((Fintype.card F - 1) / 2)) * X ^ (j.val * Fintype.card F)

private theorem stepanovAnsatz_succ (f : F[X]) {J : ℕ}
    (r s : Fin (J + 1) → F[X]) :
    stepanovAnsatz f r s =
      r 0 + s 0 * f ^ ((Fintype.card F - 1) / 2) +
        stepanovAnsatz f (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ) *
          X ^ Fintype.card F := by
  simp [stepanovAnsatz, Fin.sum_univ_succ, Nat.add_mul, pow_add, Finset.sum_mul,
    mul_assoc]

/-- All coefficients vanish if the actual Stepanov ansatz vanishes.
Successively removing the first block is equivalent to Harcos's choice
of the least nonzero block. -/
theorem stepanovAnsatz_coefficients_eq_zero
    (f : F[X]) {J B : ℕ} (r s : Fin J → F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hz : stepanovAnsatz f r s = 0) : ∀ j, r j = 0 ∧ s j = 0 := by
  induction J with
  | zero => intro j; exact Fin.elim0 j
  | succ J ih =>
      rw [stepanovAnsatz_succ] at hz
      have hdiv : X ^ Fintype.card F ∣
          r 0 + s 0 * f ^ ((Fintype.card F - 1) / 2) := by
        rw [eq_neg_of_add_eq_zero_left hz]
        exact dvd_neg.mpr (dvd_mul_left _ _)
      have hzero := stepanov_block_eq_zero_of_X_card_dvd
        f (r 0) (s 0) B hq hf0 hf (hr 0) (hs 0) hB hdiv
      have htail :
          stepanovAnsatz f (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ) = 0 := by
        have ht :
            stepanovAnsatz f (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ) *
              X ^ Fintype.card F = 0 := by
          simpa only [hzero.1, hzero.2, zero_mul, zero_add] using hz
        exact (mul_eq_zero.mp ht).resolve_right (pow_ne_zero _ X_ne_zero)
      have ht := ih (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ)
        (fun j => hr j.succ) (fun j => hs j.succ) htail
      intro j
      exact Fin.cases hzero (fun i => ht i) j


/-- Harcos page 11: a nontrivial bounded coefficient family gives a nonzero
auxiliary polynomial, under the geometric nonsquare hypothesis. -/
theorem stepanovAnsatz_ne_zero
    (f : F[X]) {J B : ℕ} (r s : Fin J → F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hne : ∃ j, r j ≠ 0 ∨ s j ≠ 0) : stepanovAnsatz f r s ≠ 0 := by
  intro hz
  have hall := stepanovAnsatz_coefficients_eq_zero f r s hq hf0 hf hr hs hB hz
  obtain ⟨j, hj⟩ := hne
  exact hj.elim (fun h => h (hall j).1) (fun h => h (hall j).2)

/-- The same nonvanishing conclusion after the multiplier in Harcos's ansatz. -/
theorem stepanov_pow_mul_ansatz_ne_zero
    (f : F[X]) (ell : ℕ) {J B : ℕ} (r s : Fin J → F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hne : ∃ j, r j ≠ 0 ∨ s j ≠ 0) :
    f ^ ell * stepanovAnsatz f r s ≠ 0 := by
  have hfne : f ≠ 0 := by
    intro hz
    apply hf0
    simp [hz]
  exact mul_ne_zero (pow_ne_zero ell hfne)
    (stepanovAnsatz_ne_zero f r s hq hf0 hf hr hs hB hne)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovVanishing -/

/-!
# Vanishing of the actual Stepanov auxiliary polynomial

This is the passage from (20) to (22) on printed page 11 of Harcos,
*Weil's bound for Kloosterman sums*
(`pages/harcos-stepanov-11.png`). Frobenius kills the positive Hasse
derivatives of `X^(jq)` below order `q`. Factoring out `f^(ell-k)`
additionally requires `k ≤ ell`; the vanishing application uses `k < ell ≤ q`.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- Frobenius forces every positive Hasse derivative of `X^(jq)` below
order `q` to vanish as a polynomial, not just as a function on the field.
The Frobenius residue of `((X + 1)^j)^q` determines its low Taylor
coefficients; evaluating a Hasse monomial at `1` recovers its sole coefficient. -/
theorem stepanov_hasseDeriv_X_card_mul (j k : ℕ)
    (hk : 0 < k) (hkq : k < Fintype.card F) :
    hasseDeriv k ((X : F[X]) ^ (j * Fintype.card F)) = 0 := by
  have hd := stepanov_X_card_dvd_pow_sub_const (((X : F[X]) + C 1) ^ j)
  have hc := (X_pow_dvd_iff.mp hd) k hkq
  have ht : (taylor (1 : F) (X ^ (j * Fintype.card F))).coeff k = 0 := by
    simpa [taylor_X_pow, pow_mul, coeff_sub, coeff_C, coeff_one, Nat.ne_of_gt hk]
      using hc
  have hchoose : ((j * Fintype.card F).choose k : F) = 0 := by
    rw [taylor_coeff, X_pow_eq_monomial, hasseDeriv_monomial] at ht
    simpa using ht
  rw [X_pow_eq_monomial, hasseDeriv_monomial, hchoose, zero_mul, monomial_zero_right]

/-- Below order `q`, a factor `X^(jq)` is constant for Hasse differentiation. -/
theorem stepanov_hasseDeriv_mul_X_card_mul (g : F[X]) (j k : ℕ)
    (hkq : k < Fintype.card F) :
    hasseDeriv k (g * X ^ (j * Fintype.card F)) =
      hasseDeriv k g * X ^ (j * Fintype.card F) := by
  classical
  rw [hasseDeriv_mul, Finset.sum_eq_single (k, 0)]
  · simp
  · intro ij hij hne
    have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hj : 0 < ij.2 := by
      by_contra hn
      have hz : ij.2 = 0 := by omega
      apply hne
      apply Prod.ext <;> simp_all
    rw [stepanov_hasseDeriv_X_card_mul j ij.2 hj (by omega), mul_zero]
  · simp

/-- Equation (20), with the necessary extraction range `k ≤ ell`. -/
theorem stepanov_hasseDeriv_pow_mul_ansatz
    (f : F[X]) (hf : f ≠ 0) (ell k : ℕ) {J : ℕ}
    (r s : Fin J → F[X]) (hk : k ≤ ell) (hkq : k < Fintype.card F) :
    hasseDeriv k (f ^ ell * stepanovAnsatz f r s) =
      f ^ (ell - k) *
        ∑ j : Fin J,
          (stepanovHasseOperator f hf ell k (r j) +
            stepanovHasseOperator f hf (ell + (Fintype.card F - 1) / 2) k (s j) *
              f ^ ((Fintype.card F - 1) / 2)) * X ^ (j.val * Fintype.card F) := by
  classical
  have he : ell + (Fintype.card F - 1) / 2 - k =
      ell - k + (Fintype.card F - 1) / 2 := by omega
  simp only [stepanovAnsatz, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hblock :
      f ^ ell * ((r j + s j * f ^ ((Fintype.card F - 1) / 2)) *
        X ^ (j.val * Fintype.card F)) =
      (r j * f ^ ell + s j * f ^ (ell + (Fintype.card F - 1) / 2)) *
        X ^ (j.val * Fintype.card F) := by
    rw [pow_add]
    ring
  rw [hblock, stepanov_hasseDeriv_mul_X_card_mul _ _ _ hkq, map_add,
    stepanovHasseOperator_spec f hf ell k,
    stepanovHasseOperator_spec f hf (ell + (Fintype.card F - 1) / 2) k,
    he, pow_add]
  ring

/-- Evaluating (20) at `f(x)^((q-1)/2) = a` gives precisely (22). -/
theorem stepanov_hasseDeriv_pow_mul_ansatz_eval
    (f : F[X]) (hf : f ≠ 0) (ell k : ℕ) {J : ℕ}
    (r s : Fin J → F[X]) (a x : F)
    (hk : k < ell) (hell : ell ≤ Fintype.card F)
    (hx : f.eval x ^ ((Fintype.card F - 1) / 2) = a) :
    (hasseDeriv k (f ^ ell * stepanovAnsatz f r s)).eval x =
      f.eval x ^ (ell - k) *
        (stepanovConstraint f hf ell ((Fintype.card F - 1) / 2) a k r s).eval x := by
  rw [stepanov_hasseDeriv_pow_mul_ansatz f hf ell k r s (Nat.le_of_lt hk)
    (lt_of_lt_of_le hk hell)]
  simp only [stepanovConstraint, eval_mul, eval_pow, eval_finsetSum, eval_add,
    eval_X, eval_smul, smul_eq_mul, hx]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.mul_comm j.val, pow_mul, FiniteField.pow_card]
  ring

omit [Fintype F] in
/-- At a zero of `f`, the multiplier `f^ell` itself supplies all required
Hasse vanishing, independently of the coefficient equations. -/
theorem stepanov_hasseDeriv_pow_mul_eval_zero
    (f g : F[X]) (ell k : ℕ) (x : F) (hk : k < ell) (hx : f.eval x = 0) :
    (hasseDeriv k (f ^ ell * g)).eval x = 0 := by
  obtain ⟨u, hu⟩ := stepanov_pow_dvd_hasseDeriv_mul_pow f g ell k
  rw [mul_comm (f ^ ell) g, hu, eval_mul, eval_pow, hx,
    zero_pow (by omega : ell - k ≠ 0), zero_mul]

/-- The actual equation system (22) forces Hasse vanishing of the actual
auxiliary polynomial at the union of the two specified loci. -/
theorem stepanov_constraints_imply_hasse_vanishing
    (f : F[X]) (hf : f ≠ 0) (ell : ℕ) {J : ℕ}
    (r s : Fin J → F[X]) (a : F) (hell : ell ≤ Fintype.card F)
    (hc : ∀ k < ell,
      stepanovConstraint f hf ell ((Fintype.card F - 1) / 2) a k r s = 0) :
    ∀ x : F, f.eval x = 0 ∨ f.eval x ^ ((Fintype.card F - 1) / 2) = a →
      ∀ k < ell, (hasseDeriv k (f ^ ell * stepanovAnsatz f r s)).eval x = 0 := by
  intro x hx k hk
  rcases hx with hx | hx
  · exact stepanov_hasseDeriv_pow_mul_eval_zero f (stepanovAnsatz f r s) ell k x hk hx
  · rw [stepanov_hasseDeriv_pow_mul_ansatz_eval f hf ell k r s a x hk hell hx,
      hc k hk, eval_zero, mul_zero]

omit [Fintype F] in
private theorem stepanov_degree_mul_lt_add_natDegree
    (p g : F[X]) (B : ℕ) (hp : p.degree < (B : WithBot ℕ)) :
    (p * g).degree < ((B + g.natDegree : ℕ) : WithBot ℕ) := by
  calc
    (p * g).degree ≤ p.degree + g.degree := degree_mul_le p g
    _ ≤ p.degree + (g.natDegree : WithBot ℕ) := by
      exact add_le_add le_rfl degree_le_natDegree
    _ < (B : WithBot ℕ) + (g.natDegree : WithBot ℕ) :=
      WithBot.add_lt_add_right (by simp) hp
    _ = _ := by rw [Nat.cast_add]

/-- Degree of the block ansatz, including the empty family and zero
coefficients. The strict `degree` convention also covers `B = 0`. -/
theorem stepanovAnsatz_degree_lt
    (f : F[X]) {J B : ℕ} (r s : Fin J → F[X])
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ)) :
    (stepanovAnsatz f r s).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree +
        (J - 1) * Fintype.card F : ℕ) : WithBot ℕ) := by
  apply mem_degreeLT.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_degreeLT.mpr
  have hr' : (r j).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree : ℕ) : WithBot ℕ) := by
    apply (hr j).trans_le
    exact_mod_cast Nat.le_add_right B ((Fintype.card F - 1) / 2 * f.natDegree)
  have hs' : (s j * f ^ ((Fintype.card F - 1) / 2)).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree : ℕ) : WithBot ℕ) := by
    simpa only [natDegree_pow] using
      stepanov_degree_mul_lt_add_natDegree (s j)
        (f ^ ((Fintype.card F - 1) / 2)) B (hs j)
  have hd := (degree_add_le _ _).trans_lt (max_lt hr' hs')
  rw [degree_mul_X_pow]
  calc
    _ < ((B + (Fintype.card F - 1) / 2 * f.natDegree : ℕ) : WithBot ℕ) +
        ((j.val * Fintype.card F : ℕ) : WithBot ℕ) :=
      WithBot.add_lt_add_right WithBot.coe_ne_bot hd
    _ ≤ _ := by
      rw [← Nat.cast_add]
      exact_mod_cast Nat.add_le_add_left
        (Nat.mul_le_mul_right (Fintype.card F) (show j.val ≤ J - 1 by omega)) _

/-- Degree budget for the actual auxiliary polynomial used in point counting. -/
theorem stepanov_pow_mul_ansatz_degree_lt
    (f : F[X]) (ell : ℕ) {J B : ℕ} (r s : Fin J → F[X])
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ)) :
    (f ^ ell * stepanovAnsatz f r s).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree +
        (J - 1) * Fintype.card F + ell * f.natDegree : ℕ) : WithBot ℕ) := by
  rw [mul_comm]
  simpa only [natDegree_pow] using
    stepanov_degree_mul_lt_add_natDegree (stepanovAnsatz f r s) (f ^ ell)
      (B + (Fintype.card F - 1) / 2 * f.natDegree + (J - 1) * Fintype.card F)
      (stepanovAnsatz_degree_lt f r s hr hs)

/-- Harcos's auxiliary polynomial exists from the actual dimension
inequality, with nonvanishing, degree control, and genuine Hasse vanishing. -/
theorem stepanov_exists_auxiliary_polynomial
    (f : F[X]) (ell B J : ℕ) (a : F)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 1 ≤ f.natDegree) (hJ : 0 < J) (hell : ell ≤ Fintype.card F)
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hcount : (∑ k : Fin ell, (B + k.val * (f.natDegree - 1) + (J - 1))) <
      2 * J * B) :
    ∃ h : F[X], h ≠ 0 ∧
      h.degree < ((B + (Fintype.card F - 1) / 2 * f.natDegree +
        (J - 1) * Fintype.card F + ell * f.natDegree : ℕ) : WithBot ℕ) ∧
      ∀ x : F, f.eval x = 0 ∨ f.eval x ^ ((Fintype.card F - 1) / 2) = a →
        ∀ k < ell, (hasseDeriv k h).eval x = 0 := by
  have hfne : f ≠ 0 := by
    intro hz
    apply hf0
    simp [hz]
  obtain ⟨r, s, hr, hs, hne, hc⟩ :=
    stepanov_exists_coefficients f hfne ell ((Fintype.card F - 1) / 2) B J a hm hJ hcount
  exact ⟨f ^ ell * stepanovAnsatz f r s,
    stepanov_pow_mul_ansatz_ne_zero f ell r s hq hf0 hf hr hs hB hne,
    stepanov_pow_mul_ansatz_degree_lt f ell r s hr hs,
    stepanov_constraints_imply_hasse_vanishing f hfne ell r s a hell hc⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovParameters -/

/-!
# Integer parameters for the Stepanov construction

Harcos, *Weil's bound for Kloosterman sums*, printed
page 12 (`pages/harcos-weil-12.png`). The coefficient spaces have integer
dimension `2 * J * B`; the equation space has the actual dimension
`∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1))`.
The ceiling choices below prove the strict inequality between these dimensions.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

/-- The multiplicity parameter on Harcos's printed page 12. -/
def stepanovEll (q : ℕ) : ℕ := ⌈Real.sqrt (q : ℝ)⌉₊

/-- The integer number of coefficients in each polynomial block. -/
def stepanovB (q m : ℕ) : ℕ := ⌈((q : ℝ) - m) / 2⌉₊

/-- The integer number of blocks in each of the two polynomial families. -/
def stepanovJ (q m ell : ℕ) : ℕ :=
  ⌈(ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q⌉₊


/-- The real form of the exact count, with no rounding of dimensions. -/
theorem stepanov_equation_count_real (ell B J m : ℕ)
    (hell : 0 < ell) (hJ : 0 < J) (hm : 1 ≤ m) :
    ((∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1)) : ℕ) : ℝ) =
      (ell : ℝ) * (B + J - 1) +
        (ell : ℝ) * (ell - 1) / 2 * (m - 1) := by
  have hsum : (∑ k : Fin ell, (k.val : ℝ)) * 2 =
      (ell : ℝ) * (ell - 1) := by
    have h := Finset.sum_range_id_mul_two ell
    rw [← Fin.sum_univ_eq_sum_range] at h
    have h' := congrArg (fun n : ℕ => (n : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hell)), Nat.cast_one] using h'
  push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hJ)),
    Nat.cast_sub hm]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

/-- For `q > 18`, the source's ceiling of the square root satisfies both
the construction's range restriction and the final square-root bound. -/
theorem stepanovEll_bounds {q : ℕ} (hq : 18 < q) :
    0 < stepanovEll q ∧ 3 * stepanovEll q ≤ q ∧ q ≤ stepanovEll q ^ 2 := by
  have hqR : (19 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hs2 := Real.sq_sqrt hq0
  have helo := Nat.le_ceil (Real.sqrt (q : ℝ))
  have hehi := Nat.ceil_lt_add_one hs0
  have hsbound : Real.sqrt (q : ℝ) + 1 ≤ (q : ℝ) / 3 := by
    have hsq : (q : ℝ) ≤ ((q : ℝ) / 3 - 1) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hqR) hq0]
    nlinarith
  have helpos : 0 < stepanovEll q := by
    apply Nat.ceil_pos.mpr
    positivity
  refine ⟨helpos, ?_, ?_⟩
  · have : (3 : ℝ) * stepanovEll q ≤ q := by
      dsimp [stepanovEll]
      linarith
    exact_mod_cast this
  · have : (q : ℝ) ≤ (stepanovEll q : ℝ) ^ 2 := by
      dsimp [stepanovEll]
      nlinarith
    exact_mod_cast this

/-- The ceiling defining the coefficient-block size respects the strict
nonvanishing restriction `2(B-1)+m < q`. -/
theorem stepanovB_bounds {q m : ℕ} (hmq : m < q) :
    0 < stepanovB q m ∧
      ((q : ℝ) - m) / 2 ≤ stepanovB q m ∧
      (stepanovB q m : ℝ) < ((q : ℝ) - m) / 2 + 1 ∧
      2 * (stepanovB q m - 1) + m < q := by
  have hmqR : (m : ℝ) < q := by exact_mod_cast hmq
  have ht : 0 < ((q : ℝ) - m) / 2 := by linarith
  have hpos : 0 < stepanovB q m := Nat.ceil_pos.mpr ht
  have hlo := Nat.le_ceil (((q : ℝ) - m) / 2)
  have hhi := Nat.ceil_lt_add_one (le_of_lt ht)
  refine ⟨hpos, hlo, hhi, ?_⟩
  have hcast : ((stepanovB q m - 1 : ℕ) : ℝ) = stepanovB q m - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos)), Nat.cast_one]
  have : (2 : ℝ) * ((stepanovB q m - 1 : ℕ) : ℝ) + m < q := by
    rw [hcast]
    dsimp [stepanovB]
    linarith
  exact_mod_cast this

/-- Integer rounding of the two block parameters gives strictly more
unknown coefficients than actual coefficient equations. -/
theorem stepanov_parameters_count {q m ell : ℕ}
    (hm : 3 ≤ m) (hmq : 6 * m < q)
    (hell : 0 < ell) (hellq : 3 * ell ≤ q) :
    0 < stepanovJ q m ell ∧
      (∑ k : Fin ell,
        (stepanovB q m + k.val * (m - 1) + (stepanovJ q m ell - 1))) <
        2 * stepanovJ q m ell * stepanovB q m := by
  let B := stepanovB q m
  let J := stepanovJ q m ell
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmqR : (6 : ℝ) * m < q := by exact_mod_cast hmq
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hellqR : (3 : ℝ) * ell ≤ q := by exact_mod_cast hellq
  have hu : 0 < (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q := by positivity
  have hJ : 0 < J := Nat.ceil_pos.mpr hu
  have hJlo : (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q ≤ J :=
    Nat.le_ceil _
  obtain ⟨_, hBlo, hBhi, _⟩ := stepanovB_bounds (show m < q by omega)
  change ((q : ℝ) - m) / 2 ≤ (B : ℝ) at hBlo
  change (B : ℝ) < ((q : ℝ) - m) / 2 + 1 at hBhi
  have hJshift : 0 ≤ (J : ℝ) - (ell : ℝ) / 2 := by
    have : 0 ≤ (ell : ℝ) ^ 2 * m / q := by positivity
    linarith
  have hhalf : (q : ℝ) / 2 ≤ q - m - ell := by linarith
  have hshiftq : (ell : ℝ) ^ 2 * m ≤ ((J : ℝ) - (ell : ℝ) / 2) * q :=
    (div_le_iff₀ hq).mp (by linarith)
  have hshift := mul_le_mul_of_nonneg_left hhalf hJshift
  have hdimension :
      (ell : ℝ) * (((q : ℝ) - m) / 2 + J) +
        (ell : ℝ) ^ 2 / 2 * (m - 1) ≤ (J : ℝ) * (q - m) := by
    nlinarith only [hshiftq, hshift]
  have hcountReal := stepanov_equation_count_real ell B J m hell hJ (by omega)
  have hupper :
      ((∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1)) : ℕ) : ℝ) <
        (ell : ℝ) * (((q : ℝ) - m) / 2 + J) +
          (ell : ℝ) ^ 2 / 2 * (m - 1) := by
    have hmul := mul_lt_mul_of_pos_left hBhi hellR
    have hpay : 0 ≤ (ell : ℝ) * (m - 1) :=
      mul_nonneg (le_of_lt hellR) (by linarith)
    nlinarith only [hcountReal, hmul, hpay]
  have hlower : (J : ℝ) * (q - m) ≤ 2 * J * B := by
    have hmul := mul_le_mul_of_nonneg_left hBlo (show 0 ≤ (2 : ℝ) * J by positivity)
    nlinarith only [hmul]
  refine ⟨hJ, ?_⟩
  have := hupper.trans_le (hdimension.trans hlower)
  exact_mod_cast this

/-- The same rounded parameters meet the source's degree budget.
Only the final step uses `q ≤ ell²`; no parity assumption is needed here. -/
theorem stepanov_parameters_degree {q m ell : ℕ}
    (hm : 3 ≤ m) (hmq : 6 * m < q)
    (hell : 0 < ell) (hellq : 3 * ell ≤ q) (hqsq : q ≤ ell ^ 2) :
    ((stepanovB q m + (q - 1) / 2 * m + (stepanovJ q m ell - 1) * q +
      ell * m : ℕ) : ℝ) <
      (ell : ℝ) * ((q : ℝ) / 2 + 2 * m * ell) := by
  let B := stepanovB q m
  let J := stepanovJ q m ell
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hellqR : (3 : ℝ) * ell ≤ q := by exact_mod_cast hellq
  have hqsqR : (q : ℝ) ≤ (ell : ℝ) ^ 2 := by exact_mod_cast hqsq
  have hu : 0 < (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q := by positivity
  have hJ : 0 < J := Nat.ceil_pos.mpr hu
  have hJhi : (J : ℝ) < (ell : ℝ) / 2 + (ell : ℝ) ^ 2 * m / q + 1 :=
    Nat.ceil_lt_add_one (le_of_lt hu)
  have hBhi : (B : ℝ) < ((q : ℝ) - m) / 2 + 1 :=
    (stepanovB_bounds (show m < q by omega)).2.2.1
  have hJmul : ((J : ℝ) - 1) * q <
      (ell : ℝ) / 2 * q + (ell : ℝ) ^ 2 * m := by
    have h := (lt_div_iff₀ hq).mp
      (show (J : ℝ) - 1 - (ell : ℝ) / 2 < (ell : ℝ) ^ 2 * m / q by linarith)
    nlinarith only [h]
  have hhalf : (2 : ℝ) * (((q - 1) / 2 : ℕ) : ℝ) ≤ q := by
    exact_mod_cast (show 2 * ((q - 1) / 2) ≤ q by omega)
  have hhalfM := mul_le_mul_of_nonneg_right hhalf (show (0 : ℝ) ≤ m by positivity)
  have hellM := mul_le_mul_of_nonneg_right hellqR (show (0 : ℝ) ≤ m by positivity)
  have hmqnonneg : 0 ≤ (q : ℝ) * (m - 3) := by positivity
  have hD :
      ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) =
        (B : ℝ) + (((q - 1) / 2 : ℕ) : ℝ) * m +
          ((J : ℝ) - 1) * q + (ell : ℝ) * m := by
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hJ))]
    rfl
  have hbudget :
      ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) <
        (m : ℝ) * q + (ell : ℝ) * q / 2 + (ell : ℝ) ^ 2 * m := by
    nlinarith only [hD, hBhi, hJmul, hhalfM, hellM, hmqnonneg, hmR]
  have hsqM := mul_le_mul_of_nonneg_right hqsqR (show (0 : ℝ) ≤ m by positivity)
  change ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) < _
  nlinarith only [hbudget, hsqM]

/-- All numerical requirements for the genuine finite-dimensional construction,
including its exact equation count and a strict real degree budget. -/
structure StepanovParameterBounds (q m ell B J : ℕ) : Prop where
  ell_pos : 0 < ell
  ell_le_card : ell ≤ q
  three_mul_ell_le : 3 * ell ≤ q
  card_le_ell_sq : q ≤ ell ^ 2
  B_pos : 0 < B
  J_pos : 0 < J
  coefficient_bound : 2 * (B - 1) + m < q
  equation_count_lt :
    (∑ k : Fin ell, (B + k.val * (m - 1) + (J - 1))) < 2 * J * B
  degree_budget :
    ((B + (q - 1) / 2 * m + (J - 1) * q + ell * m : ℕ) : ℝ) <
      (ell : ℝ) * ((q : ℝ) / 2 + 2 * m * ell)

/-- Harcos's three ceiling choices satisfy every integer constraint.
This numerical theorem is valid even without assuming `q` odd. -/
theorem stepanov_integer_parameters (q m : ℕ) (hm : 3 ≤ m) (hmq : 6 * m < q) :
    StepanovParameterBounds q m (stepanovEll q) (stepanovB q m)
      (stepanovJ q m (stepanovEll q)) := by
  obtain ⟨hell, hellq, hqsq⟩ := stepanovEll_bounds (show 18 < q by omega)
  obtain ⟨hB, _, _, hBq⟩ := stepanovB_bounds (show m < q by omega)
  obtain ⟨hJ, hcount⟩ := stepanov_parameters_count hm hmq hell hellq
  exact ⟨hell, by omega, hellq, hqsq, hB, hJ, hBq, hcount,
    stepanov_parameters_degree hm hmq hell hellq hqsq⟩


/-- The actual auxiliary polynomial with no assumed dimension inequality:
the integer choices above discharge all numerical construction hypotheses.
Both the strict integer degree bound and its real budget are retained. -/
theorem stepanov_exists_auxiliary_polynomial_of_large_card
    {F : Type*} [Field F] [Fintype F] (f : F[X]) (a : F)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    let q := Fintype.card F
    let ell := stepanovEll q
    let B := stepanovB q f.natDegree
    let J := stepanovJ q f.natDegree ell
    ∃ h : F[X], h ≠ 0 ∧
      h.degree < ((B + (q - 1) / 2 * f.natDegree +
        (J - 1) * q + ell * f.natDegree : ℕ) : WithBot ℕ) ∧
      (h.natDegree : ℝ) < (ell : ℝ) * ((q : ℝ) / 2 + 2 * f.natDegree * ell) ∧
      ∀ x : F, f.eval x = 0 ∨ f.eval x ^ ((q - 1) / 2) = a →
        ∀ k < ell, (hasseDeriv k h).eval x = 0 := by
  dsimp only
  have hp := stepanov_integer_parameters (Fintype.card F) f.natDegree hm hmq
  obtain ⟨h, hnz, hdeg, hvan⟩ := stepanov_exists_auxiliary_polynomial f
    (stepanovEll (Fintype.card F)) (stepanovB (Fintype.card F) f.natDegree)
    (stepanovJ (Fintype.card F) f.natDegree (stepanovEll (Fintype.card F)))
    a hq hf0 hf (by omega) hp.J_pos hp.ell_le_card hp.coefficient_bound
    hp.equation_count_lt
  refine ⟨h, hnz, hdeg, ?_, hvan⟩
  have hnat := (natDegree_lt_iff_degree_lt hnz).mpr hdeg
  have hreal :
      (h.natDegree : ℝ) <
        ((stepanovB (Fintype.card F) f.natDegree +
          (Fintype.card F - 1) / 2 * f.natDegree +
          (stepanovJ (Fintype.card F) f.natDegree (stepanovEll (Fintype.card F)) - 1) *
            Fintype.card F + stepanovEll (Fintype.card F) * f.natDegree : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans hp.degree_budget

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovPointCount -/

/-!
# Stepanov's square-root point-count bound

The nonzero auxiliary polynomials and their proved Hasse multiplicities
give the one-sided counts in Harcos (13). The quadratic character then
converts these bounds into the affine point count in Theorem 7.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def stepanovLocus (f : F[X]) (a : F) : Finset F :=
  Finset.univ.filter fun x => f.eval x = 0 ∨
    f.eval x ^ ((Fintype.card F - 1) / 2) = a

theorem stepanov_locus_card_lt (f : F[X]) (a : F)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    ((stepanovLocus f a).card : ℝ) < (Fintype.card F : ℝ) / 2 +
      2 * f.natDegree * stepanovEll (Fintype.card F) := by
  classical
  obtain ⟨h, hnz, _, hdeg, hvan⟩ :=
    stepanov_exists_auxiliary_polynomial_of_large_card f a hq hf0 hf hm hmq
  have hroot := stepanov_card_mul_hasse_order_le h hnz (stepanovLocus f a)
    (stepanovEll (Fintype.card F)) (fun x hx => hvan x
      (by simpa only [stepanovLocus, mem_filter, mem_univ, true_and] using hx))
  have hell := (stepanov_integer_parameters (Fintype.card F) f.natDegree hm hmq).ell_pos
  have hrootR : ((stepanovLocus f a).card : ℝ) *
      (stepanovEll (Fintype.card F) : ℝ) ≤ h.natDegree := by exact_mod_cast hroot
  have hellR : (0 : ℝ) < stepanovEll (Fintype.card F) := by exact_mod_cast hell
  nlinarith

omit [DecidableEq F] in
private theorem stepanov_char_ne_two (hq : Odd (Fintype.card F)) : ringChar F ≠ 2 := by
  intro h
  have hc := FiniteField.even_card_of_char_two h
  obtain ⟨k, hk⟩ := hq
  omega

private theorem stepanov_quadraticChar_locus_bounds (f : F[X])
    (hq : Odd (Fintype.card F)) (x : F) :
    (quadraticChar F (f.eval x) : ℝ) ≤
        2 * (if x ∈ stepanovLocus f 1 then 1 else 0 : ℝ) - 1 ∧
      1 - 2 * (if x ∈ stepanovLocus f (-1) then 1 else 0 : ℝ) ≤
        (quadraticChar F (f.eval x) : ℝ) := by
  classical
  have he : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    obtain ⟨k, hk⟩ := hq
    omega
  have hp := quadraticChar_eq_pow_of_char_ne_two' (stepanov_char_ne_two hq) (f.eval x)
  rw [he] at hp
  by_cases hz : f.eval x = 0
  · simp [stepanovLocus, hz]
  rcases quadraticChar_dichotomy hz with h | h
  · have hx : x ∈ stepanovLocus f 1 := by
      simp only [stepanovLocus, mem_filter, mem_univ, true_and]
      right
      simpa [h] using hp.symm
    rw [h, if_pos hx]
    norm_num
    split_ifs <;> norm_num
  · have hx : x ∈ stepanovLocus f (-1) := by
      simp only [stepanovLocus, mem_filter, mem_univ, true_and]
      right
      simpa [h] using hp.symm
    rw [h, if_pos hx]
    norm_num
    split_ifs <;> norm_num

theorem stepanov_quadraticChar_sum_bound_of_eval_zero_ne (f : F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    |∑ x : F, (quadraticChar F (f.eval x) : ℝ)| <
      4 * f.natDegree * stepanovEll (Fintype.card F) := by
  classical
  have hp := stepanov_locus_card_lt f 1 hq hf0 hf hm hmq
  have hn := stepanov_locus_card_lt f (-1) hq hf0 hf hm hmq
  have hu := sum_le_sum (s := (univ : Finset F))
    (fun x _ => (stepanov_quadraticChar_locus_bounds f hq x).1)
  have hl := sum_le_sum (s := (univ : Finset F))
    (fun x _ => (stepanov_quadraticChar_locus_bounds f hq x).2)
  have hi (a : F) :
      (∑ x : F, (if x ∈ stepanovLocus f a then 1 else 0 : ℝ)) =
        (stepanovLocus f a).card := by simp
  simp only [sum_sub_distrib, ← mul_sum, hi, sum_const, card_univ, nsmul_eq_mul,
    mul_one] at hu hl
  rw [abs_lt]
  constructor <;> linarith

def stepanovPointCount (f : F[X]) : ℕ :=
  (Finset.univ.filter fun xy : F × F => xy.2 ^ 2 = f.eval xy.1).card

/-- The affine point count is exactly `q` plus the quadratic-character sum. -/
theorem stepanovPointCount_eq (f : F[X]) (hq : Odd (Fintype.card F)) :
    (stepanovPointCount f : ℝ) =
      Fintype.card F + ∑ x : F, (quadraticChar F (f.eval x) : ℝ) := by
  classical
  have hfiber (x : F) :
      ((univ.filter fun y : F => y ^ 2 = f.eval x).card : ℝ) =
        (quadraticChar F (f.eval x) : ℝ) + 1 := by
    have h := quadraticChar_card_sqrts (stepanov_char_ne_two hq) (f.eval x)
    simp only [Set.toFinset_ofPred] at h
    exact_mod_cast h
  have hsum : stepanovPointCount f =
      ∑ x : F, (univ.filter fun y : F => y ^ 2 = f.eval x).card := by
    simp only [stepanovPointCount, card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  rw [hsum, Nat.cast_sum]
  simp only [hfiber, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
  ring

/-- Harcos Theorem 7 with the harmless normalization `f(0) ≠ 0` still explicit. -/
theorem stepanov_pointCount_bound_of_eval_zero_ne (f : F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 3 ≤ f.natDegree) (hmq : 6 * f.natDegree < Fintype.card F) :
    |(stepanovPointCount f : ℝ) - Fintype.card F| <
      4 * f.natDegree * ⌈Real.sqrt (Fintype.card F : ℝ)⌉₊ := by
  rw [stepanovPointCount_eq f hq, add_sub_cancel_left]
  exact stepanov_quadraticChar_sum_bound_of_eval_zero_ne f hq hf0 hf hm hmq

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosCurve -/

/-!
# Harcos's affine curve

The final paragraph of Harcos, page 12 (`pages/harcos-weil-12.png`), applies
Theorem 7 to `(X^p - X)^2 - 4ab`.  The geometric nonsquareness below follows
the source's factorization argument, rather than assuming a curve estimate.
The count is the actual affine count, not the count of a projective completion.
The final section removes the auxiliary normalization `f(0) ≠ 0` by translation,
giving Theorem 7 in its original domain.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset

section Algebra

variable {K : Type*} [Field K]

def harcosCurvePolynomial (p : ℕ) (a b : K) : K[X] :=
  (X ^ p - X) ^ 2 - C (4 * a * b)

theorem harcosCurvePolynomial_eval (p : ℕ) (a b x : K) :
    (harcosCurvePolynomial p a b).eval x = (x ^ p - x) ^ 2 - 4 * a * b := by
  simp [harcosCurvePolynomial]

theorem harcosCurvePolynomial_eval_zero (p : ℕ) (hp : 0 < p) (a b : K) :
    (harcosCurvePolynomial p a b).eval 0 = -(4 * a * b) := by
  simp [harcosCurvePolynomial_eval, hp.ne']

theorem harcosCurvePolynomial_natDegree (p : ℕ) (hp : 1 < p) (a b : K) :
    (harcosCurvePolynomial p a b).natDegree = 2 * p := by
  have hdeg : ((X : K[X]) ^ p - X).natDegree = p := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simpa using hp
  simp only [harcosCurvePolynomial, natDegree_sub_C, natDegree_pow, hdeg]

theorem harcosCurvePolynomial_eval_zero_ne (p : ℕ) (hp : 0 < p)
    (htwo : (2 : K) ≠ 0) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (harcosCurvePolynomial p a b).eval 0 ≠ 0 := by
  rw [harcosCurvePolynomial_eval_zero p hp]
  have hfour : (4 : K) ≠ 0 := by
    have := mul_ne_zero htwo htwo
    norm_num at this ⊢
    exact this
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hfour ha) hb)

/-- The source's two factors have degree zero, contradicting their `X^p`
coefficients: their sum has coefficient `2`, which is nonzero. -/
theorem harcosCurvePolynomial_not_isSquare (p : ℕ) (hp : 1 < p)
    (htwo : (2 : K) ≠ 0) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ IsSquare (harcosCurvePolynomial p a b) := by
  rintro ⟨g, hg⟩
  have hc : (4 * a * b : K) ≠ 0 := by
    have hfour : (4 : K) ≠ 0 := by
      have := mul_ne_zero htwo htwo
      norm_num at this ⊢
      exact this
    exact mul_ne_zero (mul_ne_zero hfour ha) hb
  have hprod : (X ^ p - X - g) * (X ^ p - X + g) = C (4 * a * b) := by
    have he : (X ^ p - X : K[X]) ^ 2 - C (4 * a * b) = g * g := hg
    linear_combination he
  have hnz : (X ^ p - X - g) * (X ^ p - X + g) ≠ 0 := by
    rw [hprod]
    exact C_ne_zero.mpr hc
  have hd := congrArg natDegree hprod
  rw [natDegree_mul (mul_ne_zero_iff.mp hnz).1 (mul_ne_zero_iff.mp hnz).2,
    natDegree_C] at hd
  have hm := coeff_eq_zero_of_natDegree_lt
    (p := X ^ p - X - g) (n := p) (by omega)
  have hp' := coeff_eq_zero_of_natDegree_lt
    (p := X ^ p - X + g) (n := p) (by omega)
  have hp1 : 1 ≠ p := by omega
  simp [coeff_sub, coeff_add, coeff_X_pow, coeff_X, hp1] at hm hp'
  apply htwo
  linear_combination hm + hp'

theorem harcosCurvePolynomial_geometrically_not_isSquare
    (p : ℕ) (hp : 1 < p) (htwo : (2 : K) ≠ 0)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ IsSquare ((harcosCurvePolynomial p a b).map
      (algebraMap K (AlgebraicClosure K))) := by
  have hi := (algebraMap K (AlgebraicClosure K)).injective
  have ht : (2 : AlgebraicClosure K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero_iff _ hi).mpr htwo
  simpa [harcosCurvePolynomial, map_ofNat] using
    harcosCurvePolynomial_not_isSquare p hp ht
      (algebraMap K (AlgebraicClosure K) a) (algebraMap K (AlgebraicClosure K) b)
      ((map_ne_zero_iff _ hi).mpr ha) ((map_ne_zero_iff _ hi).mpr hb)

end Algebra

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The actual affine count in the last paragraph of Harcos, page 12. -/
def harcosCurvePointCount (p : ℕ) (a b : F) : ℕ :=
  (univ.filter fun xy : F × F =>
    xy.2 ^ 2 = (xy.1 ^ p - xy.1) ^ 2 - 4 * a * b).card

theorem harcosCurvePointCount_eq_stepanovPointCount (p : ℕ) (a b : F) :
    harcosCurvePointCount p a b = stepanovPointCount (harcosCurvePolynomial p a b) := by
  simp only [harcosCurvePointCount, stepanovPointCount, harcosCurvePolynomial_eval]

/-- Harcos's specialization, with all polynomial hypotheses discharged. -/
theorem harcos_curve_pointCount_bound (p : ℕ) [CharP F p]
    (hp : p.Prime) (hp2 : p ≠ 2) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hq : 12 * p < Fintype.card F) :
    |(harcosCurvePointCount p a b : ℝ) - Fintype.card F| <
      8 * p * ⌈Real.sqrt (Fintype.card F : ℝ)⌉₊ := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have ht : (2 : F) ≠ 0 := by
    exact_mod_cast CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp2
  have hodd : Odd (Fintype.card F) := by
    apply Nat.odd_iff.mpr
    apply FiniteField.odd_card_of_char_ne_two
    simpa only [ringChar.eq F p] using hp2
  have hdeg := harcosCurvePolynomial_natDegree p (by omega) a b
  have h := stepanov_pointCount_bound_of_eval_zero_ne (harcosCurvePolynomial p a b)
    hodd (harcosCurvePolynomial_eval_zero_ne p (by omega) ht a b ha hb)
    (harcosCurvePolynomial_geometrically_not_isSquare p (by omega) ht a b ha hb)
    (by omega) (by omega)
  rw [← harcosCurvePointCount_eq_stepanovPointCount, hdeg] at h
  convert h using 1
  push_cast
  ring

/-- The source's `n ≥ 4` range is inside the range `q > 12p`. -/
theorem harcos_twelve_mul_lt_pow (p n : ℕ) (hp : 3 ≤ p) (hn : 4 ≤ n) :
    12 * p < p ^ n := by
  have h2 : 9 ≤ p ^ 2 := by nlinarith
  have h3 : 27 ≤ p ^ 3 := by nlinarith
  have h4 : 12 * p < p ^ 4 := by nlinarith
  exact h4.trans_le (pow_le_pow_right₀ (by omega) hn)

/-- In characteristic `p`, every finite field of size `p^n`, `n ≥ 4`,
satisfies the specialized estimate, with no assumed curve bound. -/
theorem harcos_curve_pointCount_bound_of_card_eq_pow (p n : ℕ) [CharP F p]
    (hp : p.Prime) (hp2 : p ≠ 2) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcard : Fintype.card F = p ^ n) (hn : 4 ≤ n) :
    |(harcosCurvePointCount p a b : ℝ) - (p : ℝ) ^ n| <
      8 * p * ⌈Real.sqrt ((p : ℝ) ^ n)⌉₊ := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq : 12 * p < Fintype.card F := by
    rw [hcard]
    exact harcos_twelve_mul_lt_pow p n hp3 hn
  simpa only [hcard, Nat.cast_pow] using
    harcos_curve_pointCount_bound p hp hp2 a b ha hb hq

end FiniteField

section Translation

variable {K : Type*} [Field K]


end Translation

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]


end FiniteField

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosTrace -/

/-!
# Harcos's trace-zero count

The last six counting lines of Corollary 3 on Harcos, page 8
(`pages/harcos-stepanov-08.png`), use the actual field trace and the
change of variables `y = 2at - (x^p - x)`.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset

section Trace

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

/-- The relative Artin--Schreier linear map for finite fields. -/
def harcosArtinSchreier : L →ₗ[K] L :=
  (FiniteField.frobeniusAlgHom K L).toLinearMap - LinearMap.id

omit [Fintype L] in
@[simp] theorem harcosArtinSchreier_apply (x : L) :
    harcosArtinSchreier K L x = x ^ Fintype.card K - x := rfl

/-- Frobenius invariance of the actual algebra trace. -/
theorem harcos_trace_pow_card (x : L) :
    Algebra.trace K L (x ^ Fintype.card K) = Algebra.trace K L x :=
  Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic K L) x

theorem harcos_trace_artinSchreier (x : L) :
    Algebra.trace K L (harcosArtinSchreier K L x) = 0 := by
  rw [harcosArtinSchreier_apply, map_sub, harcos_trace_pow_card, sub_self]

omit [Fintype L] in
/-- The fixed points of the relative Frobenius are exactly the embedded base field. -/
theorem harcos_pow_card_eq_self_iff (x : L) :
    x ^ Fintype.card K = x ↔ ∃ c : K, algebraMap K L c = x := by
  classical
  have hr := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := (X ^ Fintype.card K - X : K[X])) (algebraMap K L).injective
    (by rw [FiniteField.roots_X_pow_card_sub_X,
      Polynomial.natDegree_X_pow_sub_X (R := K) Fintype.one_lt_card]; rfl)
  have hn := Polynomial.X_pow_sub_X_ne_zero (R := L) (Fintype.one_lt_card (α := K))
  have hm : (X ^ Fintype.card K - X : L[X]).roots =
      (univ.val : Multiset K).map (algebraMap K L) := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      FiniteField.roots_X_pow_card_sub_X] using hr.symm
  rw [← sub_eq_zero, ← show
    (X ^ Fintype.card K - X : L[X]).IsRoot x ↔
      x ^ Fintype.card K - x = 0 by simp [Polynomial.IsRoot],
    ← Polynomial.mem_roots hn, hm]
  simp

omit [Fintype L] in
theorem harcos_artinSchreier_ker :
    (harcosArtinSchreier K L).ker = (Algebra.linearMap K L).range := by
  ext x
  simp only [LinearMap.mem_ker, harcosArtinSchreier_apply, sub_eq_zero,
    LinearMap.mem_range, Algebra.linearMap_apply, harcos_pow_card_eq_self_iff]

omit [Fintype L] in
theorem harcos_artinSchreier_ker_finrank :
    Module.finrank K (harcosArtinSchreier K L).ker = 1 := by
  rw [harcos_artinSchreier_ker,
    LinearMap.finrank_range_of_inj (algebraMap K L).injective]
  exact Module.finrank_self K

/-- Rank-nullity and nondegeneracy of the trace give additive Hilbert 90 here,
without assuming any trace-zero solvability statement. -/
theorem harcos_artinSchreier_range :
    (harcosArtinSchreier K L).range = (Algebra.trace K L).ker := by
  have hle : (harcosArtinSchreier K L).range ≤ (Algebra.trace K L).ker := by
    rintro _ ⟨x, rfl⟩
    exact harcos_trace_artinSchreier K L x
  apply Submodule.eq_of_le_of_finrank_eq hle
  have ha := LinearMap.finrank_range_add_finrank_ker (harcosArtinSchreier K L)
  have ht := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
  rw [harcos_artinSchreier_ker_finrank] at ha
  rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L)] at ht
  simp only [finrank_top, Module.finrank_self] at ht
  omega

theorem harcos_artinSchreier_exists_iff (c : L) :
    (∃ x : L, x ^ Fintype.card K - x = c) ↔ Algebra.trace K L c = 0 := by
  change c ∈ (harcosArtinSchreier K L).range ↔ c ∈ (Algebra.trace K L).ker
  rw [harcos_artinSchreier_range]

/-- Every nonempty Artin--Schreier fiber has exactly `#K` elements; the empty
fibers are exactly those with nonzero field trace. -/
theorem harcos_artinSchreier_fiber_card [DecidableEq L] [DecidableEq K] (c : L) :
    (univ.filter fun x : L => x ^ Fintype.card K - x = c).card =
      if Algebra.trace K L c = 0 then Fintype.card K else 0 := by
  classical
  change (univ.filter fun x : L => harcosArtinSchreier K L x = c).card = _
  by_cases hc : Algebra.trace K L c = 0
  · rw [if_pos hc]
    obtain ⟨r, hr⟩ := (harcos_artinSchreier_exists_iff K L c).mpr hc
    change harcosArtinSchreier K L r = c at hr
    have hcard : (univ.filter fun x : L => harcosArtinSchreier K L x = 0).card =
        Fintype.card K := by
      simpa only [harcos_artinSchreier_ker_finrank, pow_one,
        Fintype.card_subtype, LinearMap.mem_ker] using
        (Module.card_eq_pow_finrank (K := K) (V := (harcosArtinSchreier K L).ker))
    calc
      _ = (univ.filter fun x : L => harcosArtinSchreier K L x = 0).card := by
        refine card_nbij' (fun x : L => x - r) (fun x : L => x + r) ?_ ?_ ?_ ?_
        · intro x hx
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
          rw [map_sub, hx, hr, sub_self]
        · intro x hx
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
          rw [map_add, hx, hr, zero_add]
        · intro x _
          exact sub_add_cancel x r
        · intro x _
          exact add_sub_cancel_right x r
      _ = Fintype.card K := hcard
  · rw [if_neg hc]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    exact hc ((harcos_artinSchreier_exists_iff K L c).mp ⟨x, hx⟩)

end Trace

section ChangeOfVariables

variable {F : Type*} [Field F]

theorem harcos_artinSchreier_eq_iff_quadratic (s a b t : F) (ht : t ≠ 0) :
    s = a * t + b / t ↔ a * t ^ 2 - s * t + b = 0 := by
  constructor
  · intro h
    have h' := (eq_div_iff ht).mp (show s - a * t = b / t by rw [h]; ring)
    linear_combination -h'
  · intro h
    have h' : (s - a * t) * t = b := by linear_combination -h
    have := (eq_div_iff ht).mpr h'
    linear_combination this

theorem harcos_square_iff_quadratic (htwo : (2 : F) ≠ 0)
    (s a b t : F) (ha : a ≠ 0) :
    (2 * a * t - s) ^ 2 = s ^ 2 - 4 * a * b ↔
      a * t ^ 2 - s * t + b = 0 := by
  have hfour : (4 : F) ≠ 0 := by
    have h := mul_ne_zero htwo htwo
    norm_num at h ⊢
    exact h
  constructor
  · intro h
    have h' : (4 * a) * (a * t ^ 2 - s * t + b) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero hfour ha)
  · intro h
    linear_combination 4 * a * h

theorem harcos_quadratic_parameter_nonzero (s a b t : F) (hb : b ≠ 0)
    (h : a * t ^ 2 - s * t + b = 0) : t ≠ 0 := by
  intro ht
  apply hb
  simpa only [ht, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, zero_add] using h

/-- The explicit inverse substitution `t = (y+s)/(2a)`. -/
theorem harcos_curve_parameter_inverse (htwo : (2 : F) ≠ 0)
    (s a y : F) (ha : a ≠ 0) :
    2 * a * ((y + s) / (2 * a)) - s = y := by
  field_simp [htwo, ha]
  ring

/-- Harcos's change of variables, with nonzero `t` represented by a unit.
Its forward map is exactly `(x,t) ↦ (x,2at-(x^p-x))`; the surjectivity proof
constructs the inverse parameter `(y+(x^p-x))/(2a)`. -/
def harcosCurveArtinSchreierEquiv (p : ℕ) (htwo : (2 : F) ≠ 0)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {xt : F × Fˣ // xt.1 ^ p - xt.1 = a * (xt.2 : F) + b / (xt.2 : F)} ≃
      {xy : F × F // xy.2 ^ 2 = (xy.1 ^ p - xy.1) ^ 2 - 4 * a * b} :=
  Equiv.ofBijective
    (fun xt => ⟨(xt.1.1, 2 * a * (xt.1.2 : F) - (xt.1.1 ^ p - xt.1.1)),
      (harcos_square_iff_quadratic htwo _ a b _ ha).mpr
        ((harcos_artinSchreier_eq_iff_quadratic _ a b _ (Units.ne_zero _)).mp xt.2)⟩)
    (by
      constructor
      · intro xt xu h
        apply Subtype.ext
        have hx := congrArg (fun z => z.1.1) h
        have hy := congrArg (fun z => z.1.2) h
        dsimp only at hx hy
        apply Prod.ext hx
        apply Units.val_injective
        rw [hx] at hy
        have hmul : (2 * a) * (xt.1.2 : F) = (2 * a) * (xu.1.2 : F) := by
          linear_combination hy
        exact mul_left_cancel₀ (mul_ne_zero htwo ha) hmul
      · intro xy
        let s := xy.1.1 ^ p - xy.1.1
        let t := (xy.1.2 + s) / (2 * a)
        have hinv : 2 * a * t - s = xy.1.2 :=
          harcos_curve_parameter_inverse htwo s a xy.1.2 ha
        have hquad : a * t ^ 2 - s * t + b = 0 := by
          apply (harcos_square_iff_quadratic htwo s a b t ha).mp
          rw [hinv]
          exact xy.2
        have ht := harcos_quadratic_parameter_nonzero s a b t hb hquad
        refine ⟨⟨(xy.1.1, Units.mk0 t ht), ?_⟩, ?_⟩
        · exact (harcos_artinSchreier_eq_iff_quadratic s a b t ht).mpr hquad
        · apply Subtype.ext
          exact Prod.ext rfl hinv)


end ChangeOfVariables

section Counts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem harcosCurvePointCount_eq_artinSchreier_pairCount
    (p : ℕ) (htwo : (2 : F) ≠ 0) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCurvePointCount p a b =
      (univ.filter fun xt : F × Fˣ =>
        xt.1 ^ p - xt.1 = a * (xt.2 : F) + b / (xt.2 : F)).card := by
  classical
  simpa only [Fintype.card_subtype, harcosCurvePointCount] using
    (Fintype.card_congr (harcosCurveArtinSchreierEquiv p htwo a b ha hb)).symm

/-- The relative finite-field version of Harcos's trace-zero counting identity. -/
theorem harcosCurvePointCount_eq_card_mul_traceZero
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Algebra K F]
    (htwo : (2 : F) ≠ 0) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCurvePointCount (Fintype.card K) a b =
      Fintype.card K *
        (univ.filter fun t : Fˣ =>
          Algebra.trace K F (a * (t : F) + b / (t : F)) = 0).card := by
  classical
  rw [harcosCurvePointCount_eq_artinSchreier_pairCount _ htwo a b ha hb]
  calc
    _ = ∑ t : Fˣ, (univ.filter fun x : F =>
        x ^ Fintype.card K - x = a * (t : F) + b / (t : F)).card := by
      simp only [card_filter, Fintype.sum_prod_type]
      exact sum_comm
    _ = ∑ t : Fˣ, if Algebra.trace K F (a * (t : F) + b / (t : F)) = 0
        then Fintype.card K else 0 := by
      apply sum_congr rfl
      intro t _
      exact harcos_artinSchreier_fiber_card K F _
    _ = _ := by
      rw [card_filter, mul_sum]
      apply sum_congr rfl
      intro t _
      split_ifs <;> simp


/-- The last six counting lines of Harcos, Corollary 3, page 8. -/
theorem harcosCurvePointCount_eq_prime_mul_traceZero (p : ℕ) [Fact p.Prime]
    [CharP F p] [Algebra (ZMod p) F] (hp2 : p ≠ 2)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCurvePointCount p a b =
      p * (univ.filter fun t : Fˣ =>
        Algebra.trace (ZMod p) F (a * (t : F) + b * (t : F)⁻¹) = 0).card := by
  have htwo : (2 : F) ≠ 0 := by
    exact_mod_cast CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp2
  simpa only [ZMod.card, div_eq_mul_inv] using
    harcosCurvePointCount_eq_card_mul_traceZero (ZMod p) htwo a b ha hb

end Counts

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosCharacter -/
/-!
# Harcos's extension-field character sums

The coefficients belong to the fixed prime field, not to a varying extension.
The trace is `Algebra.trace`; its Frobenius formula and additive-character
orthogonality identify the sum over frequencies with the actual affine count.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

def harcosTraceKloosterman (a b m : ZMod p) : ℂ :=
  ∑ t : Fˣ, ZMod.stdAddChar (m * Algebra.trace (ZMod p) F
    (algebraMap (ZMod p) F a * (t : F) +
      algebraMap (ZMod p) F b * (t : F)⁻¹))


theorem harcosTraceKloosterman_zero (a b : ZMod p) :
    harcosTraceKloosterman p F a b 0 = Fintype.card Fˣ := by
  simp [harcosTraceKloosterman]

theorem harcosTraceKloosterman_frequency_sum (a b : ZMod p) :
    ∑ m : ZMod p, harcosTraceKloosterman p F a b m =
      (p : ℂ) * ((univ.filter fun t : Fˣ =>
        Algebra.trace (ZMod p) F
          (algebraMap (ZMod p) F a * (t : F) +
            algebraMap (ZMod p) F b * (t : F)⁻¹) = 0).card : ℂ) := by
  unfold harcosTraceKloosterman
  rw [sum_comm]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  rw [card_filter, Nat.cast_sum, mul_sum]
  apply sum_congr rfl
  intro t _
  split_ifs <;> simp

theorem harcosTraceKloosterman_sum_eq_curve [CharP F p]
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ m : ZMod p, harcosTraceKloosterman p F a b m =
      (harcosCurvePointCount p (algebraMap (ZMod p) F a)
        (algebraMap (ZMod p) F b) : ℂ) := by
  rw [harcosTraceKloosterman_frequency_sum,
    harcosCurvePointCount_eq_prime_mul_traceZero p hp2 _ _
      (fun h => ha ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm)))
      (fun h => hb ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm))),
    Nat.cast_mul]

theorem harcosTraceKloosterman_nonzero_sum_eq_curve [CharP F p]
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ m ∈ (univ : Finset (ZMod p)).erase 0, harcosTraceKloosterman p F a b m =
      (harcosCurvePointCount p (algebraMap (ZMod p) F a)
        (algebraMap (ZMod p) F b) : ℂ) - (Fintype.card F : ℂ) + 1 := by
  have h := sum_erase_add (univ : Finset (ZMod p))
    (fun m => harcosTraceKloosterman p F a b m) (mem_univ 0)
  rw [harcosTraceKloosterman_sum_eq_curve p F hp2 a b ha hb,
    harcosTraceKloosterman_zero, Fintype.card_units,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Fintype.card F))),
    Nat.cast_one] at h
  linear_combination h


theorem harcosTraceKloosterman_nonzero_sum_bound [CharP F p]
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (n : ℕ) (hcard : Fintype.card F = p ^ n) (hn : 4 ≤ n) :
    ‖∑ m ∈ (univ : Finset (ZMod p)).erase 0,
      harcosTraceKloosterman p F a b m‖ ≤
        8 * (p : ℝ) * ⌈Real.sqrt ((p : ℝ) ^ n)⌉₊ + 1 := by
  have ha' : algebraMap (ZMod p) F a ≠ 0 :=
    fun h => ha ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm))
  have hb' : algebraMap (ZMod p) F b ≠ 0 :=
    fun h => hb ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm))
  have h := harcos_curve_pointCount_bound_of_card_eq_pow p n
    (Fact.out : p.Prime) hp2 _ _ ha' hb' hcard hn
  rw [harcosTraceKloosterman_nonzero_sum_eq_curve p F hp2 a b ha hb, hcard,
    Nat.cast_pow]
  calc
    _ ≤ ‖(harcosCurvePointCount p (algebraMap (ZMod p) F a)
      (algebraMap (ZMod p) F b) : ℂ) - (p : ℂ) ^ n‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
    _ = |(harcosCurvePointCount p (algebraMap (ZMod p) F a)
      (algebraMap (ZMod p) F b) : ℝ) - (p : ℝ) ^ n| + 1 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast p,
          ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, norm_one]
    _ ≤ _ := by linarith

def harcosExtensionKloosterman (a b m : ZMod p) (n : ℕ) : ℂ := by
  letI := Fintype.ofFinite (GaloisField p n)
  letI := Classical.decEq (GaloisField p n)
  exact harcosTraceKloosterman p (GaloisField p n) a b m


theorem harcosExtensionKloosterman_nonzero_sum_bound
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (n : ℕ) (hn : 4 ≤ n) :
    ‖∑ m ∈ (univ : Finset (ZMod p)).erase 0,
      harcosExtensionKloosterman p a b m n‖ ≤
        8 * (p : ℝ) * ⌈Real.sqrt ((p : ℝ) ^ n)⌉₊ + 1 := by
  let := Fintype.ofFinite (GaloisField p n)
  let := Classical.decEq (GaloisField p n)
  apply harcosTraceKloosterman_nonzero_sum_bound p (GaloisField p n) hp2 a b ha hb n
  · simpa only [Nat.card_eq_fintype_card] using GaloisField.card p n (by omega)
  · exact hn

/-- A single constant for all extension degrees. This bounds the sum over
nonzero frequencies, not any individual Kloosterman sum. -/
theorem harcosExtensionKloosterman_total_growth
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (n : ℕ) (hn : 4 ≤ n) :
    ‖∑ m ∈ (univ : Finset (ZMod p)).erase 0,
      harcosExtensionKloosterman p a b m n‖ ≤
        (16 * (p : ℝ) + 1) * Real.sqrt (p : ℝ) ^ n := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hroot : 1 ≤ Real.sqrt (p : ℝ) ^ n :=
    one_le_pow₀ (Real.one_le_sqrt.mpr hp)
  have hsqrt : Real.sqrt ((p : ℝ) ^ n) = Real.sqrt (p : ℝ) ^ n := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), ← pow_mul, mul_comm n 2, pow_mul,
      Real.sq_sqrt (by positivity)]
  have hceil := Nat.ceil_lt_add_one (Real.sqrt_nonneg ((p : ℝ) ^ n))
  rw [hsqrt] at hceil
  have h := harcosExtensionKloosterman_nonzero_sum_bound p hp2 a b ha hb n hn
  rw [hsqrt] at h
  have hpay : (⌈Real.sqrt (p : ℝ) ^ n⌉₊ : ℝ) ≤ 2 * Real.sqrt (p : ℝ) ^ n := by
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hpay (show 0 ≤ 8 * (p : ℝ) by positivity)]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEta -/

/-!
# Harcos's polynomial character

The coefficient formula in Harcos, §3, Definition 4 and Lemma 6
(`pages/harcos-lpolynomial-05.png`). `nextCoeff` is zero on constants;
this includes the degree-zero endpoint in the multiplicativity statement.
-/

noncomputable section

open Finset Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- The actual polynomial character, with zero at polynomials divisible by `X`. -/
def harcosEta (a b : ZMod p) (f : (ZMod p)[X]) : ℂ :=
  if f.coeff 0 = 0 then 0 else
    ZMod.stdAddChar (-a * (f.nextCoeff / f.leadingCoeff) -
      b * (f.coeff 1 / f.coeff 0))

theorem harcosEta_zero (a b : ZMod p) : harcosEta a b 0 = 0 := by
  simp [harcosEta]

theorem harcosEta_C (a b c : ZMod p) :
    harcosEta a b (C c) = if c = 0 then 0 else 1 := by
  simp [harcosEta, nextCoeff_C_eq_zero]

theorem harcosEta_one (a b : ZMod p) : harcosEta a b 1 = 1 := by
  simpa using harcosEta_C a b 1


private theorem nextCoeff_div_leadingCoeff_mul (f g : (ZMod p)[X])
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).nextCoeff / (f * g).leadingCoeff =
      f.nextCoeff / f.leadingCoeff + g.nextCoeff / g.leadingCoeff := by
  have h := (monic_mul_leadingCoeff_inv hf).nextCoeff_mul
    (monic_mul_leadingCoeff_inv hg)
  rw [show (f * C f.leadingCoeff⁻¹) * (g * C g.leadingCoeff⁻¹) =
      (f * g) * C (f.leadingCoeff⁻¹ * g.leadingCoeff⁻¹) by
        rw [map_mul]; ring] at h
  simpa only [nextCoeff_mul_C, leadingCoeff_mul, mul_inv_rev, div_eq_mul_inv,
    mul_comm g.leadingCoeff⁻¹ f.leadingCoeff⁻¹] using h

theorem harcosEta_mul (a b : ZMod p) (f g : (ZMod p)[X]) :
    harcosEta a b (f * g) = harcosEta a b f * harcosEta a b g := by
  by_cases hf : f.coeff 0 = 0
  · simp [harcosEta, mul_coeff_zero, hf]
  by_cases hg : g.coeff 0 = 0
  · simp [harcosEta, mul_coeff_zero, hg]
  have hf' : f ≠ 0 := by intro h; apply hf; simp [h]
  have hg' : g ≠ 0 := by intro h; apply hg; simp [h]
  have hc : (f * g).coeff 1 / (f * g).coeff 0 =
      f.coeff 1 / f.coeff 0 + g.coeff 1 / g.coeff 0 := by
    rw [mul_coeff_one, mul_coeff_zero]
    field_simp
    ring
  rw [mul_coeff_zero] at hc
  simp only [harcosEta, mul_coeff_zero, mul_ne_zero hf hg, hf, hg, if_false]
  rw [nextCoeff_div_leadingCoeff_mul f g hf' hg', hc,
    ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The multiplicative source object for a later Euler-product construction. -/
def harcosEtaHom (a b : ZMod p) : (ZMod p)[X] →*₀ ℂ where
  toFun := harcosEta a b
  map_zero' := harcosEta_zero a b
  map_one' := harcosEta_one a b
  map_mul' := harcosEta_mul a b

theorem harcosEta_X_add_C (a b c : ZMod p) :
    harcosEta a b (X + C c) =
      if c = 0 then 0 else ZMod.stdAddChar (-a * c - b * c⁻¹) := by
  simp [harcosEta, nextCoeff_X_add_C]

theorem harcosEta_X_sub_C (a b t : ZMod p) :
    harcosEta a b (X - C t) =
      if t = 0 then 0 else ZMod.stdAddChar (a * t + b * t⁻¹) := by
  simpa [sub_eq_add_neg] using harcosEta_X_add_C a b (-t)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosLPolynomial -/

/-!
# Actual coefficient sums for Harcos's L-polynomial

The monic polynomials are parametrized by all their lower coefficients, not
by an assumed list of L-function coefficients. Source: Harcos, §3, Theorem 5,
`pages/harcos-lpolynomial-06.png`.
-/

noncomputable section

open Finset Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- A monic polynomial with the given vector of lower coefficients. -/
def harcosMonic (n : ℕ) (v : Fin n → ZMod p) : (ZMod p)[X] :=
  X ^ n + Polynomial.ofFn n v

theorem harcosMonic_monic (n : ℕ) (v : Fin n → ZMod p) :
    (harcosMonic n v).Monic := by
  apply (monic_X_pow n).add_of_left
  simpa using Polynomial.ofFn_degree_lt v

theorem harcosMonic_natDegree (n : ℕ) (v : Fin n → ZMod p) :
    (harcosMonic n v).natDegree = n := by
  unfold harcosMonic
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa using Polynomial.ofFn_degree_lt v

theorem harcosMonic_coeff_lt (n : ℕ) (v : Fin n → ZMod p) (i : ℕ)
    (hi : i < n) : (harcosMonic n v).coeff i = v ⟨i, hi⟩ := by
  simp [harcosMonic, Polynomial.ofFn_coeff_eq_val_of_lt v hi, ne_of_lt hi]

theorem harcosMonic_unique (n : ℕ) (f : (ZMod p)[X])
    (hm : f.Monic) (hd : f.natDegree = n) :
    ∃! v : Fin n → ZMod p, harcosMonic n v = f := by
  refine ⟨fun i ↦ f.coeff i, ?_, ?_⟩
  · ext i
    rcases lt_trichotomy i n with hi | hi | hi
    · exact harcosMonic_coeff_lt n _ i hi
    · subst i
      have he : (harcosMonic n (fun i ↦ f.coeff i)).coeff n = 1 := by
        simpa only [Polynomial.leadingCoeff, harcosMonic_natDegree] using
          (harcosMonic_monic n (fun i ↦ f.coeff i)).leadingCoeff
      rw [he, ← hd, coeff_natDegree, hm.leadingCoeff]
    · rw [coeff_eq_zero_of_natDegree_lt (by rwa [harcosMonic_natDegree]),
        coeff_eq_zero_of_natDegree_lt (by rwa [hd])]
  · intro v hv
    funext i
    have h := congrArg (fun g : (ZMod p)[X] ↦ g.coeff i) hv
    simpa only [harcosMonic_coeff_lt n v i i.isLt] using h

theorem harcosMonic_injective (n : ℕ) :
    Function.Injective (harcosMonic (p := p) n) := by
  intro v w h
  funext i
  have hc := congrArg (fun f : (ZMod p)[X] ↦ f.coeff i) h
  simpa only [harcosMonic_coeff_lt n v i i.isLt,
    harcosMonic_coeff_lt n w i i.isLt] using hc

/-- Exactly the finite set of monic polynomials of degree `n`. -/
def harcosMonicPolynomials (p n : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] :=
  Finset.univ.image (harcosMonic n)

theorem mem_harcosMonicPolynomials (n : ℕ) (f : (ZMod p)[X]) :
    f ∈ harcosMonicPolynomials p n ↔ f.Monic ∧ f.natDegree = n := by
  classical
  constructor
  · intro hf
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨harcosMonic_monic n v, harcosMonic_natDegree n v⟩
  · rintro ⟨hm, hd⟩
    obtain ⟨v, hv, _⟩ := harcosMonic_unique n f hm hd
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩


theorem harcosMonic_zero (v : Fin 0 → ZMod p) : harcosMonic 0 v = 1 := by
  simp [harcosMonic]

theorem harcosMonic_one (v : Fin 1 → ZMod p) :
    harcosMonic 1 v = X + C (v 0) := by
  unfold harcosMonic
  rw [pow_one]
  congr 1
  ext i
  cases i with
  | zero => simp [Polynomial.ofFn_coeff_eq_val_of_lt]
  | succ i =>
    simp [Polynomial.ofFn_coeff_eq_zero_of_ge v (by omega : 1 ≤ i + 1)]

/-- The genuine finite monic-degree coefficient sum of the polynomial character. -/
def harcosCoefficient (a b : ZMod p) (n : ℕ) : ℂ :=
  ∑ v : Fin n → ZMod p, harcosEta a b (harcosMonic n v)

theorem harcosCoefficient_eq_sum_monic (a b : ZMod p) (n : ℕ) :
    harcosCoefficient a b n =
      ∑ f ∈ harcosMonicPolynomials p n, harcosEta a b f := by
  classical
  rw [harcosMonicPolynomials, Finset.sum_image]
  · rfl
  · intro v _ w _ h
    exact harcosMonic_injective n h


theorem harcosCoefficient_zero (a b : ZMod p) : harcosCoefficient a b 0 = 1 := by
  simp [harcosCoefficient, harcosMonic_zero, harcosEta_one]

theorem harcosCoefficient_one (a : ZMod p) (b : ℤ) :
    harcosCoefficient a (b : ZMod p) 1 = completeKloosterman p a b := by
  classical
  rw [harcosCoefficient, completeKloosterman_eq]
  calc
    ∑ v : Fin 1 → ZMod p, harcosEta a (b : ZMod p) (harcosMonic 1 v) =
        ∑ t : ZMod p, harcosEta a (b : ZMod p) (X - C t) := by
      apply Fintype.sum_bijective (fun v : Fin 1 → ZMod p ↦ -v 0)
      · constructor
        · intro v w h
          funext i
          have hi : i = 0 := Subsingleton.elim _ _
          simpa only [hi] using neg_injective h
        · intro t
          exact ⟨fun _ ↦ -t, neg_neg t⟩
      · intro v
        simp [harcosMonic_one, sub_eq_add_neg]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [harcosEta_X_sub_C]
      by_cases ht : t = 0 <;> simp [ht, isUnit_iff_ne_zero]

theorem harcosEta_monic_coefficients (a b : ZMod p) (n : ℕ)
    (hn : 2 ≤ n) (v : Fin n → ZMod p) :
    harcosEta a b (harcosMonic n v) =
      if v ⟨0, by omega⟩ = 0 then 0 else
        ZMod.stdAddChar (-a * v ⟨n - 1, by omega⟩ -
          b * (v ⟨1, by omega⟩ / v ⟨0, by omega⟩)) := by
  have hn' : 0 < (harcosMonic n v).natDegree := by
    rw [harcosMonic_natDegree]; omega
  simp only [harcosEta, nextCoeff_of_natDegree_pos hn', harcosMonic_natDegree,
    (harcosMonic_monic n v).leadingCoeff, div_one,
    harcosMonic_coeff_lt n v 0 (by omega),
    harcosMonic_coeff_lt n v 1 (by omega),
    harcosMonic_coeff_lt n v (n - 1) (by omega)]

private theorem sum_snoc (n : ℕ) (f : (Fin (n + 1) → ZMod p) → ℂ) :
    ∑ v, f v = ∑ t : ZMod p, ∑ w : Fin n → ZMod p, f (Fin.snoc w t) := by
  calc
    _ = ∑ z : ZMod p × (Fin n → ZMod p), f (Fin.snoc z.2 z.1) :=
      Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ ZMod p)).symm
        _ _ (fun _ ↦ by simp [Fin.snocEquiv])
    _ = _ := Fintype.sum_prod_type _

private theorem sum_char_mul (c : ZMod p) :
    ∑ t : ZMod p, ZMod.stdAddChar (c * t) = if c = 0 then (p : ℂ) else 0 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hc)

theorem harcosCoefficient_ge_three (a b : ZMod p) (ha : a ≠ 0)
    (n : ℕ) (hn : 3 ≤ n) : harcosCoefficient a b n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + m = (m + 2) + 1 by omega, harcosCoefficient, sum_snoc, sum_comm]
  apply Finset.sum_eq_zero
  intro w _
  have he (t : ZMod p) :
      harcosEta a b (harcosMonic (m + 2 + 1) (Fin.snoc w t)) =
        if w ⟨0, by omega⟩ = 0 then 0 else
          ZMod.stdAddChar (-a * t) *
            ZMod.stdAddChar (-b * (w ⟨1, by omega⟩ / w ⟨0, by omega⟩)) := by
    rw [harcosEta_monic_coefficients a b _ (by omega)]
    simp [Fin.snoc, Fin.castLT, sub_eq_add_neg, AddChar.map_add_eq_mul]
  simp_rw [he]
  by_cases hw : w ⟨0, by omega⟩ = 0
  · simp only [hw, if_true, sum_const_zero]
  · simp only [hw, if_false, ← Finset.sum_mul, sum_char_mul, neg_ne_zero.mpr ha,
      if_false, zero_mul]

private theorem sum_fin_one (f : ZMod p → ℂ) :
    ∑ v : Fin 1 → ZMod p, f (v 0) = ∑ c : ZMod p, f c := by
  refine Fintype.sum_bijective (fun v : Fin 1 → ZMod p ↦ v 0) ?_ _ _ (fun _ ↦ rfl)
  constructor
  · intro v w h
    funext i
    simpa only [show i = 0 from Subsingleton.elim _ _] using h
  · intro c
    exact ⟨fun _ ↦ c, rfl⟩

theorem harcosCoefficient_two_sum (a b : ZMod p) :
    harcosCoefficient a b 2 =
      ∑ c : ZMod p, if c = 0 then 0 else
        ∑ t : ZMod p, ZMod.stdAddChar ((-a - b / c) * t) := by
  rw [harcosCoefficient, show 2 = 1 + 1 from rfl, sum_snoc]
  have he (t : ZMod p) (w : Fin 1 → ZMod p) :
      harcosEta a b (harcosMonic 2 (Fin.snoc w t)) =
        if w 0 = 0 then 0 else ZMod.stdAddChar ((-a - b / w 0) * t) := by
    rw [harcosEta_monic_coefficients a b 2 (by omega)]
    simp only [Fin.snoc, Fin.castLT, Fin.val_mk]
    simp
    congr 2
    ring
  simp_rw [he]
  conv_lhs =>
    arg 2
    ext t
    rw [sum_fin_one (fun c ↦ if c = 0 then 0 else
      ZMod.stdAddChar ((-a - b / c) * t))]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  by_cases hc : c = 0 <;> simp [hc]

theorem harcosCoefficient_two (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCoefficient a b 2 = (p : ℂ) := by
  classical
  rw [harcosCoefficient_two_sum]
  simp_rw [sum_char_mul]
  have hroot : -b / a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
  have hz (c : ZMod p) (hc : c ≠ 0) : -a - b / c = 0 ↔ c = -b / a := by
    field_simp
    constructor <;> intro h <;> linear_combination -h
  rw [Finset.sum_eq_single (-b / a)]
  · rw [if_neg hroot, if_pos ((hz _ hroot).2 rfl)]
  · intro c _ hc
    by_cases hc0 : c = 0
    · simp [hc0]
    · rw [if_neg hc0, if_neg (fun h ↦ hc ((hz c hc0).1 h))]
  · simp

/-- The formal generating series, before any coefficient evaluation. -/
def harcosLSeries (a b : ZMod p) : PowerSeries ℂ :=
  PowerSeries.mk (harcosCoefficient a b)

/-- The polynomial assembled from the actual degree-zero, one, and two sums. -/
def harcosLPolynomial (a b : ZMod p) : ℂ[X] :=
  ∑ n ∈ Finset.range 3, Polynomial.monomial n (harcosCoefficient a b n)

theorem harcosLPolynomial_coeff (a b : ZMod p) (ha : a ≠ 0) (n : ℕ) :
    (harcosLPolynomial a b).coeff n = harcosCoefficient a b n := by
  classical
  simp only [harcosLPolynomial, finsetSum_coeff, coeff_monomial, Finsupp.single_apply]
  by_cases hn : n < 3
  · simp [hn]
  · rw [harcosCoefficient_ge_three a b ha n (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by have := Finset.mem_range.mp hi; omega)]


theorem harcosLSeries_eq_polynomial (a b : ZMod p) (ha : a ≠ 0) :
    harcosLSeries a b = (harcosLPolynomial a b : PowerSeries ℂ) := by
  ext n
  simp [harcosLSeries, harcosLPolynomial_coeff a b ha]


theorem harcosLPolynomial_eq_coefficients (a b : ZMod p) :
    harcosLPolynomial a b =
      1 + C (harcosCoefficient a b 1) * X + C (harcosCoefficient a b 2) * X ^ 2 := by
  simp [harcosLPolynomial, Finset.sum_range_succ, harcosCoefficient_zero,
    ← C_mul_X_pow_eq_monomial]

/-- The first reciprocal root, constructed from the actual coefficient sums. -/
def harcosReciprocalRootPlus (a b : ZMod p) : ℂ :=
  (-harcosCoefficient a b 1 +
    Complex.sqrt ((harcosCoefficient a b 1) ^ 2 - 4 * harcosCoefficient a b 2)) / 2

/-- The second reciprocal root; the two choices may coincide. -/
def harcosReciprocalRootMinus (a b : ZMod p) : ℂ :=
  (-harcosCoefficient a b 1 -
    Complex.sqrt ((harcosCoefficient a b 1) ^ 2 - 4 * harcosCoefficient a b 2)) / 2

theorem harcosReciprocalRoots_add (a b : ZMod p) :
    harcosReciprocalRootPlus a b + harcosReciprocalRootMinus a b =
      -harcosCoefficient a b 1 := by
  unfold harcosReciprocalRootPlus harcosReciprocalRootMinus
  ring

theorem harcosReciprocalRoots_mul (a b : ZMod p) :
    harcosReciprocalRootPlus a b * harcosReciprocalRootMinus a b =
      harcosCoefficient a b 2 := by
  have hs : Complex.sqrt ((harcosCoefficient a b 1) ^ 2 -
      4 * harcosCoefficient a b 2) ^ 2 =
        (harcosCoefficient a b 1) ^ 2 - 4 * harcosCoefficient a b 2 := by
    exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
  unfold harcosReciprocalRootPlus harcosReciprocalRootMinus
  linear_combination -hs / 4

/-- Factorization of the polynomial obtained from the monic-degree sums. -/
theorem harcosLPolynomial_factorization (a b : ZMod p) :
    harcosLPolynomial a b =
      (1 - C (harcosReciprocalRootPlus a b) * X) *
        (1 - C (harcosReciprocalRootMinus a b) * X) := by
  rw [harcosLPolynomial_eq_coefficients, ← harcosReciprocalRoots_mul,
    show harcosCoefficient a b 1 =
      -(harcosReciprocalRootPlus a b + harcosReciprocalRootMinus a b) by
        rw [harcosReciprocalRoots_add, neg_neg],
    map_neg, map_add, map_mul]
  ring

/-- The root factorization is an identity of the actual coefficient generating series. -/
theorem harcosLSeries_factorization (a b : ZMod p) (ha : a ≠ 0) :
    harcosLSeries a b =
      (1 - PowerSeries.C (harcosReciprocalRootPlus a b) * PowerSeries.X) *
        (1 - PowerSeries.C (harcosReciprocalRootMinus a b) * PowerSeries.X) := by
  rw [harcosLSeries_eq_polynomial a b ha, harcosLPolynomial_factorization]
  simp


theorem harcosReciprocalRoots_mul_prime (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosReciprocalRootPlus a b * harcosReciprocalRootMinus a b = (p : ℂ) := by
  rw [harcosReciprocalRoots_mul, harcosCoefficient_two a b ha hb]


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEuler -/

/-!
# Finite Euler coefficient identities for actual monic polynomials

This is the algebraic, coefficientwise version of the Euler-product argument
in Harcos, §3, Lemma 7 and Theorem 6 (`pages/harcos-lpolynomial-05.png`–`07.png`).
The multiplicities below are those of the actual polynomial factorization.
-/

noncomputable section

open Finset Polynomial UniqueFactorizationMonoid

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- The coefficient obtained by summing a multiplicative weight over actual monics. -/
def harcosEulerCoefficient (η : (ZMod p)[X] →* ℂ) (n : ℕ) : ℂ :=
  ∑ f ∈ harcosMonicPolynomials p n, η f

/-- A coefficient with one marked occurrence of an irreducible factor. -/
def harcosEulerMarked (η : (ZMod p)[X] →* ℂ) (k : (ZMod p)[X]) (n : ℕ) : ℂ :=
  ∑ f ∈ harcosMonicPolynomials p n, ((normalizedFactors f).count k : ℂ) * η f

/-- Every monic irreducible of degree at most the cutoff, with no duplicates. -/
def harcosEulerPrimes (p n : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] := by
  classical
  exact (range (n + 1)).biUnion fun d ↦
    (harcosMonicPolynomials p d).filter Irreducible

theorem mem_harcosEulerPrimes (n : ℕ) (k : (ZMod p)[X]) :
    k ∈ harcosEulerPrimes p n ↔ k.Monic ∧ Irreducible k ∧ k.natDegree ≤ n := by
  classical
  simp only [harcosEulerPrimes, mem_biUnion, mem_range, mem_filter,
    mem_harcosMonicPolynomials]
  constructor
  · rintro ⟨d, hd, ⟨hm, he⟩, hi⟩
    exact ⟨hm, hi, by omega⟩
  · rintro ⟨hm, hi, hd⟩
    exact ⟨k.natDegree, by omega, ⟨hm, rfl⟩, hi⟩

private theorem euler_count_eq_zero_of_not_dvd (k f : (ZMod p)[X]) (h : ¬ k ∣ f) :
    (normalizedFactors f).count k = 0 := by
  classical
  apply Multiset.count_eq_zero.mpr
  intro hm
  exact h (dvd_of_mem_normalizedFactors hm)

private theorem euler_count_mul (k f : (ZMod p)[X]) (hk : k.Monic)
    (hi : Irreducible k) (hf : f.Monic) :
    (normalizedFactors (k * f)).count k = 1 + (normalizedFactors f).count k := by
  classical
  rw [normalizedFactors_mul hk.ne_zero hf.ne_zero,
    normalizedFactors_irreducible hi, hk.normalize_eq_self, Multiset.count_add]
  simp

theorem harcosEulerMarked_eq_zero (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (n : ℕ) (hn : n < k.natDegree) :
    harcosEulerMarked η k n = 0 := by
  classical
  apply sum_eq_zero
  intro f hf
  obtain ⟨hm, hd⟩ := (mem_harcosMonicPolynomials n f).mp hf
  have hnd : ¬ k ∣ f := by
    intro h
    have := natDegree_le_of_dvd h hm.ne_zero
    omega
  simp [euler_count_eq_zero_of_not_dvd k f hnd]

theorem harcosEulerMarked_add_degree (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (hk : k.Monic) (hi : Irreducible k) (n : ℕ) :
    harcosEulerMarked η k (k.natDegree + n) =
      η k * (harcosEulerCoefficient η n + harcosEulerMarked η k n) := by
  classical
  unfold harcosEulerMarked harcosEulerCoefficient
  rw [← sum_add_distrib, mul_sum]
  have hfilter :
      (∑ f ∈ harcosMonicPolynomials p (k.natDegree + n),
          ((normalizedFactors f).count k : ℂ) * η f) =
        ∑ f ∈ (harcosMonicPolynomials p (k.natDegree + n)).filter (k ∣ ·),
          ((normalizedFactors f).count k : ℂ) * η f := by
    symm
    apply sum_subset (filter_subset _ _)
    intro f hf hnf
    have hnd : ¬ k ∣ f := by simpa [hf] using hnf
    simp [euler_count_eq_zero_of_not_dvd k f hnd]
  rw [hfilter]
  symm
  apply sum_bij (fun f _ ↦ k * f)
  · intro f hf
    obtain ⟨hm, hd⟩ := (mem_harcosMonicPolynomials n f).mp hf
    exact mem_filter.mpr ⟨(mem_harcosMonicPolynomials _ _).mpr
      ⟨hk.mul hm, by rw [hk.natDegree_mul hm, hd]⟩, dvd_mul_right k f⟩
  · intro f _ g _ he
    exact mul_left_cancel₀ hk.ne_zero he
  · intro f hf
    obtain ⟨hfm, hd⟩ := (mem_harcosMonicPolynomials _ _).mp (mem_filter.mp hf).1
    obtain ⟨g, rfl⟩ := (mem_filter.mp hf).2
    have hg := hk.of_mul_monic_left hfm
    refine ⟨g, (mem_harcosMonicPolynomials _ _).mpr ⟨hg, ?_⟩, rfl⟩
    rw [hk.natDegree_mul hg] at hd
    omega
  · intro f hf
    have hm := ((mem_harcosMonicPolynomials n f).mp hf).1
    rw [euler_count_mul k f hk hi hm, map_mul, Nat.cast_add, Nat.cast_one]
    ring

private theorem euler_degree_sum (f : (ZMod p)[X]) (hf : f.Monic) :
    ((normalizedFactors f).map natDegree).sum = f.natDegree := by
  have hprod : (normalizedFactors f).prod = f := by
    simpa [hf.leadingCoeff] using leadingCoeff_mul_prod_normalizedFactors f
  rw [← natDegree_multiset_prod _ (zero_notMem_normalizedFactors f), hprod]

theorem harcosEuler_degree_marked (η : (ZMod p)[X] →* ℂ) (n : ℕ) :
    (n : ℂ) * harcosEulerCoefficient η n =
      ∑ k ∈ harcosEulerPrimes p n, (k.natDegree : ℂ) * harcosEulerMarked η k n := by
  classical
  unfold harcosEulerCoefficient harcosEulerMarked
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro f hf
  obtain ⟨hm, hd⟩ := (mem_harcosMonicPolynomials n f).mp hf
  have hsub : (normalizedFactors f).toFinset ⊆ harcosEulerPrimes p n := by
    intro k hk
    obtain ⟨hi, hkm, hkd⟩ :=
      (Polynomial.mem_normalizedFactors_iff hm.ne_zero).mp (Multiset.mem_toFinset.mp hk)
    exact (mem_harcosEulerPrimes n k).mpr
      ⟨hkm, hi, hd ▸ natDegree_le_of_dvd hkd hm.ne_zero⟩
  have hs : ∑ k ∈ harcosEulerPrimes p n,
      k.natDegree * (normalizedFactors f).count k = n := by
    have hdeg := euler_degree_sum f hm
    rw [sum_multiset_map_count, hd] at hdeg
    calc
      _ = ∑ k ∈ (normalizedFactors f).toFinset,
          (normalizedFactors f).count k • k.natDegree := by
        simp only [nsmul_eq_mul, mul_comm]
        symm
        apply sum_subset hsub
        intro k _ hk
        have hn : k ∉ normalizedFactors f := by rwa [Multiset.mem_toFinset] at hk
        simp [Multiset.count_eq_zero.mpr hn]
      _ = n := hdeg
  have hsc := congrArg (fun x : ℕ ↦ (x : ℂ)) hs
  push_cast at hsc
  rw [← hsc, sum_mul]
  apply sum_congr rfl
  intro k _
  ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEulerSeries -/

/-! # The coefficientwise Euler logarithmic derivative -/

noncomputable section

open Finset
open scoped Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The geometric formal series in `c T^d`; no convergence is involved. -/
def harcosEulerGeometric (d : ℕ) (c : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦ if d ∣ n then c ^ (n / d) else 0

theorem harcosEulerGeometric_step (d : ℕ) (hd : 0 < d) (c : ℂ) :
    harcosEulerGeometric d c =
      1 + PowerSeries.C c * PowerSeries.X ^ d * harcosEulerGeometric d c := by
  apply PowerSeries.ext
  intro n
  rw [map_add, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hn : d ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hne : d + m ≠ 0 := by omega
    simp only [harcosEulerGeometric, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      if_neg hne, zero_add, Nat.le_add_right, if_true, Nat.add_sub_cancel_left,
      Nat.dvd_add_self_left, Nat.add_div_left _ hd]
    split_ifs <;> simp [pow_succ, mul_comm]
  · have hlt : n < d := by omega
    simp only [if_neg hn, mul_zero, add_zero, harcosEulerGeometric,
      PowerSeries.coeff_mk, PowerSeries.coeff_one]
    by_cases hz : n = 0
    · simp [hz]
    · rw [if_neg hz, if_neg]
      exact fun h ↦ (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) h).not_gt hlt

theorem harcosEulerGeometric_mul (d : ℕ) (hd : 0 < d) (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X ^ d) * harcosEulerGeometric d c = 1 := by
  have h := harcosEulerGeometric_step d hd c
  linear_combination h

variable {p : ℕ} [Fact p.Prime]

/-- The formal series of the actual monic coefficient sums. -/
def harcosEulerSeries (η : (ZMod p)[X] →* ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (harcosEulerCoefficient η)

private def eulerMarkedSeries (η : (ZMod p)[X] →* ℂ) (k : (ZMod p)[X]) :
    PowerSeries ℂ :=
  PowerSeries.mk (harcosEulerMarked η k)

private theorem eulerMarkedSeries_step (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (hk : k.Monic) (hi : Irreducible k) :
    eulerMarkedSeries η k = PowerSeries.C (η k) * PowerSeries.X ^ k.natDegree *
      (harcosEulerSeries η + eulerMarkedSeries η k) := by
  apply PowerSeries.ext
  intro n
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  by_cases hn : k.natDegree ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.le_add_right, if_true, Nat.add_sub_cancel_left,
      map_add, eulerMarkedSeries, harcosEulerSeries, PowerSeries.coeff_mk]
    exact harcosEulerMarked_add_degree η k hk hi m
  · simp only [if_neg hn, mul_zero, eulerMarkedSeries, PowerSeries.coeff_mk]
    exact harcosEulerMarked_eq_zero η k n (by omega)

theorem harcosEulerMarked_series (η : (ZMod p)[X] →* ℂ)
    (k : (ZMod p)[X]) (hk : k.Monic) (hi : Irreducible k) :
    PowerSeries.mk (harcosEulerMarked η k) =
      (harcosEulerGeometric k.natDegree (η k) - 1) * harcosEulerSeries η := by
  have hd : 0 < k.natDegree := hi.natDegree_pos
  have hs := eulerMarkedSeries_step η k hk hi
  have hg := harcosEulerGeometric_mul k.natDegree hd (η k)
  change eulerMarkedSeries η k = _
  calc
    eulerMarkedSeries η k =
        ((1 - PowerSeries.C (η k) * PowerSeries.X ^ k.natDegree) *
          harcosEulerGeometric k.natDegree (η k)) * eulerMarkedSeries η k := by rw [hg, one_mul]
    _ = (harcosEulerGeometric k.natDegree (η k) - 1) * harcosEulerSeries η := by
      linear_combination harcosEulerGeometric k.natDegree (η k) * hs -
        harcosEulerSeries η * hg

/-- A finite logarithmic-derivative series, containing all irreducibles up to the cutoff. -/
def harcosEulerLog (η : (ZMod p)[X] →* ℂ) (N : ℕ) : PowerSeries ℂ :=
  ∑ k ∈ harcosEulerPrimes p N, PowerSeries.C (k.natDegree : ℂ) *
    (harcosEulerGeometric k.natDegree (η k) - 1)

theorem harcosEulerLog_mul_coeff (η : (ZMod p)[X] →* ℂ) (N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (harcosEulerLog η N * harcosEulerSeries η) =
      (n : ℂ) * harcosEulerCoefficient η n := by
  classical
  rw [harcosEulerLog, sum_mul, map_sum]
  calc
    _ = ∑ k ∈ harcosEulerPrimes p N,
        (k.natDegree : ℂ) * harcosEulerMarked η k n := by
      apply sum_congr rfl
      intro k hk
      obtain ⟨hkm, hki, _⟩ := (mem_harcosEulerPrimes N k).mp hk
      rw [mul_assoc, ← harcosEulerMarked_series η k hkm hki,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    _ = _ := by
      rw [harcosEuler_degree_marked η n]
      symm
      apply sum_subset
      · intro k hk
        obtain ⟨hkm, hki, hkd⟩ := (mem_harcosEulerPrimes n k).mp hk
        exact (mem_harcosEulerPrimes N k).mpr ⟨hkm, hki, hkd.trans hn⟩
      · intro k hk hkn
        obtain ⟨hkm, hki, _⟩ := (mem_harcosEulerPrimes N k).mp hk
        have hd : n < k.natDegree := by
          by_contra! h
          exact hkn ((mem_harcosEulerPrimes n k).mpr ⟨hkm, hki, h⟩)
        rw [harcosEulerMarked_eq_zero η k n hd, mul_zero]

/-- The actual irreducible divisor sum appearing in Harcos's equation (10). -/
def harcosEulerLogCoefficient (η : (ZMod p)[X] →* ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ d ∈ n.divisors, (d : ℂ) *
    ∑ k ∈ (harcosMonicPolynomials p d).filter Irreducible, η k ^ (n / d)

theorem harcosEulerLog_coeff (η : (ZMod p)[X] →* ℂ) (N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (harcosEulerLog η N) = harcosEulerLogCoefficient η n := by
  classical
  by_cases hz : n = 0
  · subst n
    simp [harcosEulerLog, harcosEulerGeometric, harcosEulerLogCoefficient]
  rw [harcosEulerLog, map_sum]
  simp_rw [PowerSeries.coeff_C_mul, map_sub, harcosEulerGeometric,
    PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg hz, sub_zero]
  rw [harcosEulerPrimes, sum_biUnion]
  · have hfilter : (range (N + 1)).filter (· ∣ n) = n.divisors := by
      ext d
      simp only [mem_filter, mem_range, Nat.mem_divisors]
      constructor
      · exact fun h ↦ ⟨h.2, hz⟩
      · intro h
        exact ⟨by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) h.1; omega, h.1⟩
    calc
      _ = ∑ d ∈ range (N + 1), if d ∣ n then (d : ℂ) *
          ∑ k ∈ (harcosMonicPolynomials p d).filter Irreducible,
            η k ^ (n / d) else 0 := by
        apply sum_congr rfl
        intro d _
        by_cases hd : d ∣ n
        · rw [if_pos hd, mul_sum]
          apply sum_congr rfl
          intro k hk
          have hkdeg := ((mem_harcosMonicPolynomials d k).mp (mem_filter.mp hk).1).2
          rw [hkdeg, if_pos hd]
        · rw [if_neg hd]
          apply sum_eq_zero
          intro k hk
          have hkdeg := ((mem_harcosMonicPolynomials d k).mp (mem_filter.mp hk).1).2
          rw [hkdeg, if_neg hd, mul_zero]
      _ = _ := by rw [← sum_filter, hfilter]; rfl
  · intro d _ e _ hde
    apply disjoint_left.mpr
    intro k hk hk'
    have hd := ((mem_harcosMonicPolynomials d k).mp (mem_filter.mp hk).1).2
    have he := ((mem_harcosMonicPolynomials e k).mp (mem_filter.mp hk').1).2
    exact hde (hd.symm.trans he)


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEulerRoots -/

/-!
# Harcos's irreducible sum equals the negative root power sum

The input character is the actual polynomial character. The Euler logarithmic
identity is produced by finite factorization, not assumed.
-/

noncomputable section

open Finset
open scoped Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem euler_coeff_cancel (A F G : PowerSeries ℂ)
    (hA : PowerSeries.constantCoeff A = 1) (N : ℕ)
    (h : ∀ n ≤ N, PowerSeries.coeff n (F * A) = PowerSeries.coeff n (G * A)) :
    PowerSeries.coeff N F = PowerSeries.coeff N G := by
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr
    (show IsUnit (PowerSeries.constantCoeff A) by rw [hA]; exact isUnit_one)
  have he : PowerSeries.coeff N ((F * A) * (↑u⁻¹ : PowerSeries ℂ)) =
      PowerSeries.coeff N ((G * A) * (↑u⁻¹ : PowerSeries ℂ)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply sum_congr rfl
    intro ij hij
    rw [h ij.1 (by have := mem_antidiagonal.mp hij; omega)]
  simpa [mul_assoc, ← hu] using he

private def eulerRootLog (α β : ℂ) : PowerSeries ℂ :=
  -((harcosEulerGeometric 1 α - 1) + (harcosEulerGeometric 1 β - 1))

private theorem eulerRootLog_mul (α β : ℂ) :
    eulerRootLog α β *
        ((1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)) =
      PowerSeries.X * (PowerSeries.derivative (R := ℂ))
        ((1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)) := by
  have ha := harcosEulerGeometric_mul 1 (by omega) α
  have hb := harcosEulerGeometric_mul 1 (by omega) β
  simp only [pow_one] at ha hb
  simp only [eulerRootLog, Derivation.leibniz, map_sub, PowerSeries.derivative_one,
    PowerSeries.derivative_C, PowerSeries.derivative_X, smul_eq_mul,
    mul_zero, mul_one, zero_sub]
  linear_combination
    -(1 - PowerSeries.C β * PowerSeries.X) * ha -
    (1 - PowerSeries.C α * PowerSeries.X) * hb

private theorem eulerRootLog_coeff (α β : ℂ) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff n (eulerRootLog α β) = -(α ^ n + β ^ n) := by
  simp [eulerRootLog, harcosEulerGeometric, PowerSeries.coeff_one, hn]

variable {p : ℕ} [Fact p.Prime]

theorem harcosEulerCoefficient_zero (η : (ZMod p)[X] →* ℂ) :
    harcosEulerCoefficient η 0 = 1 := by
  classical
  simp [harcosEulerCoefficient, harcosMonicPolynomials, harcosMonic_zero]

/-- A quadratic factorization of the actual monic series determines all prime-power sums. -/
theorem harcosEulerLogCoefficient_eq_powerSum (η : (ZMod p)[X] →* ℂ) (α β : ℂ)
    (hA : harcosEulerSeries η =
      (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X))
    (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient η n = -(α ^ n + β ^ n) := by
  have h0 : PowerSeries.constantCoeff (harcosEulerSeries η) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, harcosEulerSeries,
      PowerSeries.coeff_mk, harcosEulerCoefficient_zero]
  have he := euler_coeff_cancel (harcosEulerSeries η)
    (harcosEulerLog η n) (eulerRootLog α β) h0 n (by
      intro j hj
      rw [harcosEulerLog_mul_coeff η n j hj, hA, eulerRootLog_mul, ← hA]
      cases j with
      | zero => simp
      | succ j =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
            harcosEulerSeries, PowerSeries.coeff_mk]
          push_cast
          ring)
  rw [harcosEulerLog_coeff η n n le_rfl, eulerRootLog_coeff α β n hn] at he
  exact he

theorem harcosEulerSeries_character (a b : ZMod p) :
    harcosEulerSeries (harcosEtaHom a b).toMonoidHom = harcosLSeries a b := by
  apply PowerSeries.ext
  intro n
  rw [harcosEulerSeries, harcosLSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    harcosCoefficient_eq_sum_monic]
  rfl


/-- The actual irreducible coefficients for the explicitly constructed reciprocal roots. -/
theorem harcosEuler_character_reciprocalRoots (a b : ZMod p) (ha : a ≠ 0)
    (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient (harcosEtaHom a b).toMonoidHom n =
      -(harcosReciprocalRootPlus a b ^ n + harcosReciprocalRootMinus a b ^ n) := by
  apply harcosEulerLogCoefficient_eq_powerSum _ _ _ _ n hn
  rw [harcosEulerSeries_character]
  exact harcosLSeries_factorization a b ha

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEulerIndex -/

/-! # The finite Euler index for comparison with minimal-polynomial orbits -/

noncomputable section

open Finset
open scoped Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- Monic irreducibles with nonzero constant coefficient and degree dividing `n`. -/
def harcosEulerNonzeroPrimes (p n : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] := by
  classical
  exact (harcosEulerPrimes p n).filter fun k ↦ k.coeff 0 ≠ 0 ∧ k.natDegree ∣ n

theorem mem_harcosEulerNonzeroPrimes (n : ℕ) (hn : n ≠ 0) (k : (ZMod p)[X]) :
    k ∈ harcosEulerNonzeroPrimes p n ↔
      k.Monic ∧ Irreducible k ∧ k.coeff 0 ≠ 0 ∧ k.natDegree ∣ n := by
  classical
  simp only [harcosEulerNonzeroPrimes, mem_filter, mem_harcosEulerPrimes]
  constructor
  · exact fun ⟨⟨hm, hi, _⟩, hc, hd⟩ ↦ ⟨hm, hi, hc, hd⟩
  · rintro ⟨hm, hi, hc, hd⟩
    exact ⟨⟨hm, hi, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd⟩, hc, hd⟩

theorem harcosEulerLogCoefficient_eq_flat (η : (ZMod p)[X] →* ℂ) (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient η n =
      ∑ k ∈ (harcosEulerPrimes p n).filter (fun k ↦ k.natDegree ∣ n),
        (k.natDegree : ℂ) * η k ^ (n / k.natDegree) := by
  classical
  rw [← harcosEulerLog_coeff η n n le_rfl, harcosEulerLog, map_sum, sum_filter]
  apply sum_congr rfl
  intro k _
  simp only [PowerSeries.coeff_C_mul, map_sub, harcosEulerGeometric,
    PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg hn, sub_zero]
  split_ifs <;> simp

/-- The exact flat, nonzero-root index used by the finite-field orbit sum. -/
theorem harcosEuler_character_eq_nonzeroPrime_sum (a b : ZMod p)
    (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient (harcosEtaHom a b).toMonoidHom n =
      ∑ k ∈ harcosEulerNonzeroPrimes p n,
        (k.natDegree : ℂ) * harcosEta a b k ^ (n / k.natDegree) := by
  classical
  rw [harcosEulerLogCoefficient_eq_flat _ n hn]
  change (∑ k ∈ (harcosEulerPrimes p n).filter (fun k ↦ k.natDegree ∣ n),
    (k.natDegree : ℂ) * harcosEta a b k ^ (n / k.natDegree)) = _
  symm
  apply sum_subset
  · intro k hk
    obtain ⟨hkm, hki, hc, hd⟩ := (mem_harcosEulerNonzeroPrimes n hn k).mp hk
    exact mem_filter.mpr ⟨(mem_harcosEulerPrimes n k).mpr
      ⟨hkm, hki, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd⟩, hd⟩
  · intro k hk hkn
    obtain ⟨hkp, hd⟩ := mem_filter.mp hk
    obtain ⟨hkm, hki, hle⟩ := (mem_harcosEulerPrimes n k).mp hkp
    have hc : k.coeff 0 = 0 := by
      by_contra h
      exact hkn ((mem_harcosEulerNonzeroPrimes n hn k).mpr ⟨hkm, hki, h, hd⟩)
    have he : n / k.natDegree ≠ 0 := by
      have := Nat.div_pos hle hki.natDegree_pos
      omega
    simp [harcosEta, hc, he]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosMinpoly -/

/-!
# Minimal-polynomial linkage in Harcos's Theorem 6

Harcos, §3, pages 7–8 (`pages/harcos-lpolynomial-07.png` and
`pages/harcos-stepanov-08.png`), identifies the character on each orbit
with a power of the polynomial character. The extension multiplicity is
a natural-number quotient, not division in the base field.
-/

noncomputable section

open Polynomial IntermediateField Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

section General

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

omit [FiniteDimensional K L] in
private theorem adjoin_inv_eq (t : L) : K⟮t⁻¹⟯ = K⟮t⟯ := by
  apply le_antisymm
  · exact adjoin_simple_le_iff.mpr ((K⟮t⟯).inv_mem (mem_adjoin_simple_self K t))
  · apply adjoin_simple_le_iff.mpr
    simpa only [inv_inv] using
      (K⟮t⁻¹⟯).inv_mem (mem_adjoin_simple_self K t⁻¹)

theorem harcos_minpoly_inv_natDegree (t : L) :
    (minpoly K t⁻¹).natDegree = (minpoly K t).natDegree := by
  rw [← adjoin.finrank (IsIntegral.of_finite K t⁻¹),
    ← adjoin.finrank (IsIntegral.of_finite K t), adjoin_inv_eq]

/-- The inverse minimal polynomial is the normalized coefficient reversal. -/
theorem harcos_minpoly_inv (t : L) (ht : t ≠ 0) :
    minpoly K t⁻¹ = (minpoly K t).reverse * C ((minpoly K t).coeff 0)⁻¹ := by
  have hc := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite K t) ht
  have hl : (minpoly K t).reverse.leadingCoeff = (minpoly K t).coeff 0 := by
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero hc]
  apply Eq.symm
  apply eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite K t⁻¹))
  · rw [← hl]
    exact monic_mul_leadingCoeff_inv
      (reverse_eq_zero.not.mpr (minpoly.ne_zero (IsIntegral.of_finite K t)))
  · apply minpoly.dvd
    rw [map_mul]
    have hr : aeval t⁻¹ (minpoly K t).reverse = 0 := by
      let : Invertible t := invertibleOfNonzero ht
      simpa only [invOf_eq_inv, ← aeval_def] using
        (eval₂_reverse_eq_zero_iff (algebraMap K L) t (minpoly K t)).mpr
          (minpoly.aeval K t)
    rw [hr, zero_mul]
  · rw [natDegree_mul_C (inv_ne_zero hc), harcos_minpoly_inv_natDegree]
    exact reverse_natDegree_le _

theorem harcos_minpoly_inv_nextCoeff (t : L) (ht : t ≠ 0) :
    (minpoly K t⁻¹).nextCoeff = (minpoly K t).coeff 1 / (minpoly K t).coeff 0 := by
  have hc := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite K t) ht
  have hd : (minpoly K t).reverse.natDegree = (minpoly K t).natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hc), Nat.sub_zero]
  have hp := minpoly.natDegree_pos (IsIntegral.of_finite K t)
  rw [harcos_minpoly_inv K t ht, nextCoeff_mul_C,
    nextCoeff_of_natDegree_pos (hd.symm ▸ hp), hd, coeff_reverse,
    revAt_le (Nat.sub_le _ _)]
  have hi : (minpoly K t).natDegree - ((minpoly K t).natDegree - 1) = 1 := by omega
  rw [hi, div_eq_mul_inv]

/-- The tower index is an integer quotient before casting to the base field. -/
theorem harcos_minpoly_extension_index (t : L) :
    Module.finrank K⟮t⟯ L = Module.finrank K L / (minpoly K t).natDegree := by
  rw [← Module.finrank_mul_finrank K K⟮t⟯ L,
    adjoin.finrank (IsIntegral.of_finite K t),
    Nat.mul_div_right _ (minpoly.natDegree_pos (IsIntegral.of_finite K t))]

theorem harcos_trace_inv_minpoly (t : L) (ht : t ≠ 0) :
    Algebra.trace K L t⁻¹ =
      ((Module.finrank K L / (minpoly K t).natDegree : ℕ) : K) *
        (-(minpoly K t).coeff 1 / (minpoly K t).coeff 0) := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff,
    harcos_minpoly_extension_index, harcos_minpoly_inv_natDegree,
    harcos_minpoly_inv_nextCoeff K t ht, neg_div]

/-- The actual trace of the Kloosterman phase, including inseparable tower indices
and indices divisible by the characteristic. -/
theorem harcos_trace_minpoly_phase (a b : K) (t : L) (ht : t ≠ 0) :
    Algebra.trace K L (algebraMap K L a * t + algebraMap K L b / t) =
      ((Module.finrank K L / (minpoly K t).natDegree : ℕ) : K) *
        (-a * (minpoly K t).nextCoeff -
          b * (minpoly K t).coeff 1 / (minpoly K t).coeff 0) := by
  rw [div_eq_mul_inv, ← Algebra.smul_def, ← Algebra.smul_def, map_add,
    map_smul, map_smul, trace_eq_finrank_mul_minpoly_nextCoeff,
    harcos_minpoly_extension_index, harcos_trace_inv_minpoly K t ht,
    smul_eq_mul, smul_eq_mul]
  ring

end General

section PrimeField

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [Fintype F] [Algebra (ZMod p) F]

/-- The character value is constant on the minimal-polynomial fiber.
The exponent is a natural number even when the characteristic divides the index. -/
theorem harcos_minpoly_eta_power (a b : ZMod p) (m : ℕ) (t : F) (ht : t ≠ 0) :
    ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
      (algebraMap (ZMod p) F a * t + algebraMap (ZMod p) F b / t)) =
      harcosEta a b (minpoly (ZMod p) t) ^
        (m * (Module.finrank (ZMod p) F / (minpoly (ZMod p) t).natDegree)) := by
  have hc := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite (ZMod p) t) ht
  rw [harcos_trace_minpoly_phase (ZMod p) a b t ht]
  simp only [harcosEta, hc, if_false,
    (minpoly.monic (IsIntegral.of_finite (ZMod p) t)).leadingCoeff, div_one]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_mul]
  congr 1
  ring

/-- The finite set of minimal polynomials of nonzero elements of the extension. -/
def harcosMinpolyOrbits : Finset (ZMod p)[X] := by
  classical
  exact univ.image fun t : Fˣ => minpoly (ZMod p) (t : F)

/-- Each orbit is represented by its actual nonzero roots in the given field. -/
def harcosMinpolyFiber (k : (ZMod p)[X]) : Finset Fˣ := by
  classical
  exact univ.filter fun t : Fˣ => minpoly (ZMod p) (t : F) = k

theorem harcos_mem_minpolyOrbits (k : (ZMod p)[X]) :
    k ∈ harcosMinpolyOrbits p F ↔ ∃ t : Fˣ, minpoly (ZMod p) (t : F) = k := by
  classical
  simp [harcosMinpolyOrbits]

theorem harcos_mem_minpolyFiber (k : (ZMod p)[X]) (t : Fˣ) :
    t ∈ harcosMinpolyFiber p F k ↔ minpoly (ZMod p) (t : F) = k := by
  classical
  simp [harcosMinpolyFiber]

private theorem irreducible_splits_of_degree_dvd (k : (ZMod p)[X])
    (hi : Irreducible k) (hd : k.natDegree ∣ Module.finrank (ZMod p) F) :
    (k.map (algebraMap (ZMod p) F)).Splits := by
  have hdiv := hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hd
  have hc : Nat.card (ZMod p) ^ Module.finrank (ZMod p) F = Fintype.card F := by
    simpa only [Nat.card_eq_fintype_card] using
      (Module.card_eq_pow_finrank (K := ZMod p) (V := F)).symm
  rw [hc] at hdiv
  apply (FiniteField.splits_X_pow_card_sub_X p (K := F)).of_dvd
  · simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] using
      Polynomial.X_pow_sub_X_ne_zero (R := F) (Fintype.one_lt_card (α := F))
  · exact Polynomial.map_dvd (algebraMap (ZMod p) F) hdiv

omit [Fintype F] in
private theorem root_ne_zero (k : (ZMod p)[X]) (hc : k.coeff 0 ≠ 0)
    (x : F) (hx : aeval x k = 0) : x ≠ 0 := by
  intro he
  subst x
  apply hc
  apply (algebraMap (ZMod p) F).injective
  simpa only [aeval_def, eval₂_at_zero, map_zero] using hx

/-- Harcos's orbit index set is exactly all monic irreducibles of degree dividing
the extension degree, except `X`, excluded by the nonzero constant coefficient. -/
theorem harcos_mem_minpolyOrbits_iff (k : (ZMod p)[X]) :
    k ∈ harcosMinpolyOrbits p F ↔ k.Monic ∧ Irreducible k ∧ k.coeff 0 ≠ 0 ∧
      k.natDegree ∣ Module.finrank (ZMod p) F := by
  rw [harcos_mem_minpolyOrbits]
  constructor
  · rintro ⟨t, rfl⟩
    have hi := IsIntegral.of_finite (ZMod p) (t : F)
    exact ⟨minpoly.monic hi, minpoly.irreducible hi,
      minpoly.coeff_zero_ne_zero hi t.ne_zero, minpoly.degree_dvd hi⟩
  · rintro ⟨hm, hi, hc, hd⟩
    have hs := irreducible_splits_of_degree_dvd p F k hi hd
    have hdeg : (k.map (algebraMap (ZMod p) F)).degree ≠ 0 := by
      rw [degree_map]
      exact hi.degree_pos.ne'
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero hdeg
    rw [eval_map_algebraMap] at hx
    refine ⟨Units.mk0 x (root_ne_zero p F k hc x hx), ?_⟩
    exact (minpoly.eq_of_irreducible_of_monic hi hx hm).symm

/-- Each minimal-polynomial fiber has cardinality exactly its degree, with no
chosen algebraic closure and no assumption about orbit cardinalities. -/
theorem harcos_minpolyFiber_card (k : (ZMod p)[X])
    (hk : k ∈ harcosMinpolyOrbits p F) :
    (harcosMinpolyFiber p F k).card = k.natDegree := by
  classical
  obtain ⟨hm, hi, hc, hd⟩ := (harcos_mem_minpolyOrbits_iff p F k).mp hk
  let e : ↥(harcosMinpolyFiber p F k) ≃ k.rootSet F :=
    { toFun := fun t =>
        ⟨(t.1 : F), (mem_rootSet_of_ne hi.ne_zero).mpr (by
          have ht := (harcos_mem_minpolyFiber p F k t.1).mp t.2
          exact (congrArg (aeval (t.1 : F)) ht).symm.trans
            (minpoly.aeval (ZMod p) (t.1 : F)))⟩
      invFun := fun x =>
        ⟨Units.mk0 x.1 (root_ne_zero p F k hc x.1
          ((mem_rootSet_of_ne hi.ne_zero).mp x.2)),
          (harcos_mem_minpolyFiber p F k _).mpr
            (minpoly.eq_of_irreducible_of_monic hi
              ((mem_rootSet_of_ne hi.ne_zero).mp x.2) hm).symm⟩
      left_inv := fun t => by apply Subtype.ext; apply Units.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl }
  calc
    (harcosMinpolyFiber p F k).card = Fintype.card ↥(harcosMinpolyFiber p F k) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (k.rootSet F) := Fintype.card_congr e
    _ = k.natDegree := card_rootSet_eq_natDegree (PerfectField.separable_of_irreducible hi)
      (irreducible_splits_of_degree_dvd p F k hi hd)

/-- The contribution of a single orbit is its degree times its eta power. -/
theorem harcos_minpolyFiber_character_sum (a b : ZMod p) (m : ℕ)
    (k : (ZMod p)[X]) (hk : k ∈ harcosMinpolyOrbits p F) :
    ∑ t ∈ harcosMinpolyFiber p F k,
      ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
        (algebraMap (ZMod p) F a * (t : F) + algebraMap (ZMod p) F b / (t : F))) =
      (k.natDegree : ℂ) *
        harcosEta a b k ^ (m * (Module.finrank (ZMod p) F / k.natDegree)) := by
  classical
  calc
    _ = ∑ _t ∈ harcosMinpolyFiber p F k,
        harcosEta a b k ^ (m * (Module.finrank (ZMod p) F / k.natDegree)) := by
      apply sum_congr rfl
      intro t ht
      rw [harcos_minpoly_eta_power p F a b m (t : F) t.ne_zero,
        (harcos_mem_minpolyFiber p F k t).mp ht]
    _ = _ := by rw [sum_const, harcos_minpolyFiber_card p F k hk, nsmul_eq_mul]

/-- The finite orbit-sum identity in the last step of Harcos's Theorem 6.
Together with `harcos_mem_minpolyOrbits_iff`, this is precisely the sum over
monic irreducibles of degrees dividing the extension degree, excluding `X`. -/
theorem harcos_trace_character_minpoly_sum [DecidableEq F] (a b : ZMod p) (m : ℕ) :
    ∑ t : Fˣ, ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
      (algebraMap (ZMod p) F a * (t : F) + algebraMap (ZMod p) F b / (t : F))) =
      ∑ k ∈ harcosMinpolyOrbits p F, (k.natDegree : ℂ) *
        harcosEta a b k ^ (m * (Module.finrank (ZMod p) F / k.natDegree)) := by
  classical
  calc
    _ = ∑ k ∈ harcosMinpolyOrbits p F, ∑ t ∈ harcosMinpolyFiber p F k,
        ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
          (algebraMap (ZMod p) F a * (t : F) +
            algebraMap (ZMod p) F b / (t : F))) := by
      have h := (sum_fiberwise_of_maps_to
        (s := univ) (t := harcosMinpolyOrbits p F)
        (g := fun t : Fˣ => minpoly (ZMod p) (t : F))
        (fun t _ => (harcos_mem_minpolyOrbits p F _).mpr ⟨t, rfl⟩)
        (fun t => ZMod.stdAddChar ((m : ZMod p) * Algebra.trace (ZMod p) F
          (algebraMap (ZMod p) F a * (t : F) +
            algebraMap (ZMod p) F b / (t : F))))).symm
      refine h.trans (sum_congr rfl fun k _ => sum_congr ?_ fun _ _ => rfl)
      ext t
      simp [harcos_mem_minpolyFiber]
    _ = _ := sum_congr rfl fun k hk => harcos_minpolyFiber_character_sum p F a b m k hk

/-- The orbit identity consumes the actual trace-character sum used in the
Artin–Schreier point-count bridge, for every prime-field frequency. -/
theorem harcosTraceKloosterman_minpoly_sum [DecidableEq F] (a b m : ZMod p) :
    harcosTraceKloosterman p F a b m =
      ∑ k ∈ harcosMinpolyOrbits p F, (k.natDegree : ℂ) *
        harcosEta a b k ^ (m.val * (Module.finrank (ZMod p) F / k.natDegree)) := by
  simpa only [harcosTraceKloosterman, ZMod.natCast_zmod_val, div_eq_mul_inv] using
    harcos_trace_character_minpoly_sum p F a b m.val

end PrimeField

section ExtensionSequence

variable (p : ℕ) [Fact p.Prime]

/-- Frequency scaling agrees with an eta power on polynomials not divisible by
`X`. The nonzero-constant condition matters at frequency zero. -/
theorem harcosEta_frequency_of_coeff_zero_ne (a b m : ZMod p)
    (k : (ZMod p)[X]) (hk : k.coeff 0 ≠ 0) :
    harcosEta (m * a) (m * b) k = harcosEta a b k ^ m.val := by
  simp only [harcosEta, hk, if_false]
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
  congr 1
  ring

/-- Orbit indices for the same fixed extension used by `harcosExtensionKloosterman`. -/
def harcosExtensionMinpolyOrbits (n : ℕ) : Finset (ZMod p)[X] := by
  letI := Fintype.ofFinite (GaloisField p n)
  exact harcosMinpolyOrbits p (GaloisField p n)

theorem harcos_mem_extensionMinpolyOrbits_iff (n : ℕ) (hn : 0 < n)
    (k : (ZMod p)[X]) :
    k ∈ harcosExtensionMinpolyOrbits p n ↔
      k.Monic ∧ Irreducible k ∧ k.coeff 0 ≠ 0 ∧ k.natDegree ∣ n := by
  let := Fintype.ofFinite (GaloisField p n)
  simpa only [harcosExtensionMinpolyOrbits, GaloisField.finrank p hn.ne'] using
    harcos_mem_minpolyOrbits_iff p (GaloisField p n) k

/-- The orbit identity for the actual extension sequence, only at positive
degrees: `GaloisField p 0` is not a field with one element. -/
theorem harcosExtensionKloosterman_minpoly_sum (a b m : ZMod p)
    (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      ∑ k ∈ harcosExtensionMinpolyOrbits p n, (k.natDegree : ℂ) *
        harcosEta a b k ^ (m.val * (n / k.natDegree)) := by
  let := Fintype.ofFinite (GaloisField p n)
  let := Classical.decEq (GaloisField p n)
  simpa only [harcosExtensionKloosterman, harcosExtensionMinpolyOrbits,
    GaloisField.finrank p hn.ne'] using
    harcosTraceKloosterman_minpoly_sum p (GaloisField p n) a b m

/-- Frequency-scaled form of the orbit identity, matching the finite Euler
coefficient for the actual polynomial character `harcosEta (m*a) (m*b)`. -/
theorem harcosExtensionKloosterman_minpoly_sum_scaled (a b m : ZMod p)
    (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      ∑ k ∈ harcosExtensionMinpolyOrbits p n, (k.natDegree : ℂ) *
        harcosEta (m * a) (m * b) k ^ (n / k.natDegree) := by
  rw [harcosExtensionKloosterman_minpoly_sum p a b m n hn]
  apply sum_congr rfl
  intro k hk
  have hc := ((harcos_mem_extensionMinpolyOrbits_iff p n hn k).mp hk).2.2.1
  rw [harcosEta_frequency_of_coeff_zero_ne p a b m k hc, pow_mul]

/-- The independently constructed Euler index and actual field-orbit index agree. -/
theorem harcosExtensionMinpolyOrbits_eq_euler (n : ℕ) (hn : 0 < n) :
    harcosExtensionMinpolyOrbits p n = harcosEulerNonzeroPrimes p n := by
  ext k
  rw [harcos_mem_extensionMinpolyOrbits_iff p n hn k,
    mem_harcosEulerNonzeroPrimes n hn.ne' k]

/-- Actual extension-field character sums are the logarithmic coefficients of
the actual polynomial-character Euler series. -/
theorem harcosExtensionKloosterman_eq_eulerLogCoefficient (a b m : ZMod p)
    (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      harcosEulerLogCoefficient (harcosEtaHom (m * a) (m * b)).toMonoidHom n := by
  rw [harcosExtensionKloosterman_minpoly_sum_scaled p a b m n hn,
    harcosExtensionMinpolyOrbits_eq_euler p n hn,
    harcosEuler_character_eq_nonzeroPrime_sum (m * a) (m * b) n hn.ne']

/-- Harcos's Theorem 6 with explicitly constructed reciprocal roots, not an
assumed power-sum or Euler identity. -/
theorem harcosExtensionKloosterman_eq_reciprocalRoots (a b m : ZMod p)
    (ha : a ≠ 0) (hm : m ≠ 0) (n : ℕ) (hn : 0 < n) :
    harcosExtensionKloosterman p a b m n =
      -(harcosReciprocalRootPlus (m * a) (m * b) ^ n +
        harcosReciprocalRootMinus (m * a) (m * b) ^ n) := by
  rw [harcosExtensionKloosterman_eq_eulerLogCoefficient p a b m n hn]
  exact harcosEuler_character_reciprocalRoots (m * a) (m * b) (mul_ne_zero hm ha) n hn.ne'

end ExtensionSequence

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosPowerSum -/

/-!
# Finite power sums detect the modulus of every root

This supplies the growth-to-root-modulus implication used on page 1 of
Harcos, *Weil's bound for Kloosterman sums* (`pages/harcos-weil-01.png`).
Cesàro averages isolate all copies of a maximal-modulus root simultaneously;
their positive multiplicity prevents cancellation. No distinctness is needed.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Filter Finset
open scoped Topology

/-- Away from `1`, the Cesàro averages of powers in the closed unit disk tend to zero. -/
theorem harcos_cesaro_powers_tendsto_zero {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ k ∈ range n, z ^ k)
      atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      ‖((n : ℝ)⁻¹) • ∑ k ∈ range n, z ^ k‖ ≤
        (n : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), geom_sum_eq hz1, norm_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_pow, norm_one]
        have := pow_le_one₀ (n := n) (norm_nonneg z) hz
        linarith
  apply squeeze_zero_norm hbound
  simpa using
    ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
      (2 / ‖z - 1‖))

/-- Cesàro averaging retains precisely the copies of the root `1`. -/
theorem harcos_cesaro_powers_tendsto {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ k ∈ range n, z ^ k)
      atTop (𝓝 (if z = 1 then 1 else 0)) := by
  classical
  by_cases hz1 : z = 1
  · subst z
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (𝓝 1)).cesaro_smul
  · simpa only [if_neg hz1] using harcos_cesaro_powers_tendsto_zero hz hz1

/-- A geometric bound on all sufficiently large power sums bounds every root.
The indexing map may have repetitions: maximal equal roots contribute their
positive integer multiplicity to a Cesàro limit, rather than canceling. -/
theorem harcos_norm_le_of_finset_power_sum_bound {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) {R C : ℝ} (hR : 0 < R)
    (hbound : ∀ᶠ n : ℕ in atTop, ‖∑ i ∈ s, z i ^ n‖ ≤ C * R ^ n) :
    ∀ i ∈ s, ‖z i‖ ≤ R := by
  classical
  intro i hi
  by_contra hbad
  have hiR : R < ‖z i‖ := lt_of_not_ge hbad
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun k ↦ ‖z k‖) ⟨i, hi⟩
  have hjR : R < ‖z j‖ := hiR.trans_le (hmax i hi)
  have hjpos : 0 < ‖z j‖ := hR.trans hjR
  have hj0 : z j ≠ 0 := norm_pos_iff.mp hjpos
  have hratio : 0 ≤ R / ‖z j‖ := div_nonneg hR.le (norm_nonneg _)
  have hratio1 : R / ‖z j‖ < 1 := (div_lt_one hjpos).mpr hjR
  have hdecay : Tendsto (fun n : ℕ ↦ C * (R / ‖z j‖) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratio1).const_mul C
  have hzero : Tendsto (fun n : ℕ ↦ ∑ k ∈ s, (z k / z j) ^ n)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hdecay
    filter_upwards [hbound] with n hn
    calc
      ‖∑ k ∈ s, (z k / z j) ^ n‖ = ‖∑ k ∈ s, z k ^ n‖ / ‖z j‖ ^ n := by
        simp_rw [div_pow, div_eq_mul_inv]
        rw [← Finset.sum_mul, norm_mul, norm_inv, norm_pow]
      _ ≤ C * R ^ n / ‖z j‖ ^ n :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ = C * (R / ‖z j‖) ^ n := by rw [div_pow]; ring
  have hterm (k : ι) (hk : k ∈ s) :
      Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ m ∈ range n, (z k / z j) ^ m)
        atTop (𝓝 (if z k / z j = 1 then 1 else 0)) := by
    apply harcos_cesaro_powers_tendsto
    rw [norm_div]
    exact (div_le_one hjpos).mpr (hmax k hk)
  have hlimit := tendsto_finsetSum s hterm
  have hmeans :
      (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ m ∈ range n, ∑ k ∈ s, (z k / z j) ^ m) =
      (fun n : ℕ ↦ ∑ k ∈ s, ((n : ℝ)⁻¹) • ∑ m ∈ range n, (z k / z j) ^ m) := by
    funext n
    rw [Finset.sum_comm, Finset.smul_sum]
  have heq := tendsto_nhds_unique (hmeans ▸ hzero.cesaro_smul) hlimit
  rw [Finset.sum_boole] at heq
  have hcard : 0 < (s.filter (fun k ↦ z k / z j = 1)).card :=
    Finset.card_pos.mpr ⟨j, by simp [hj, hj0]⟩
  exact (Nat.ne_of_gt hcard) (by exact_mod_cast heq.symm)


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosPrimeWeil -/

/-!
# The odd-prime Kloosterman bound

The polynomial character, its quadratic generating series, the finite Euler
identity, the actual extension trace identity, and the Stepanov point bound
are all proved in the imported modules. Cesaro averaging converts the bound
on the total root power sum into individual bounds without losing multiplicity.
-/

noncomputable section

open Finset Filter

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable (p : ℕ) [Fact p.Prime]

theorem harcosReciprocalRoots_norm_le (hp2 : p ≠ 2) (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) (m : ZMod p) (hm : m ≠ 0) :
    ‖harcosReciprocalRootPlus (m * a) (m * b)‖ ≤ Real.sqrt (p : ℝ) ∧
      ‖harcosReciprocalRootMinus (m * a) (m * b)‖ ≤ Real.sqrt (p : ℝ) := by
  let s := (univ : Finset (ZMod p)).erase 0 ×ˢ (univ : Finset Bool)
  let z : ZMod p × Bool → ℂ := fun i =>
    if i.2 then harcosReciprocalRootPlus (i.1 * a) (i.1 * b)
      else harcosReciprocalRootMinus (i.1 * a) (i.1 * b)
  have hsum (n : ℕ) (hn : 4 ≤ n) :
      (∑ i ∈ s, z i ^ n) =
        -(∑ k ∈ (univ : Finset (ZMod p)).erase 0,
          harcosExtensionKloosterman p a b k n) := by
    simp only [s, z, sum_product, Fintype.sum_bool, Bool.false_eq_true,
      if_false, if_true]
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro k hk
    rw [harcosExtensionKloosterman_eq_reciprocalRoots p a b k ha
      (mem_erase.mp hk).1 n (by omega), neg_neg]
  have hg : ∀ᶠ n : ℕ in atTop,
      ‖∑ i ∈ s, z i ^ n‖ ≤ (16 * (p : ℝ) + 1) * Real.sqrt (p : ℝ) ^ n := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    rw [hsum n hn, norm_neg]
    exact harcosExtensionKloosterman_total_growth p hp2 a b ha hb n hn
  have hz := harcos_norm_le_of_finset_power_sum_bound s z
    (Real.sqrt_pos.mpr (show (0 : ℝ) < p by
      exact_mod_cast (Fact.out : p.Prime).pos)) hg
  exact ⟨hz (m, true) (by simp [s, hm]), hz (m, false) (by simp [s, hm])⟩

theorem harcosReciprocalRoots_norm_eq (hp2 : p ≠ 2) (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖harcosReciprocalRootPlus a b‖ = Real.sqrt (p : ℝ) ∧
      ‖harcosReciprocalRootMinus a b‖ = Real.sqrt (p : ℝ) := by
  have hle := harcosReciprocalRoots_norm_le p hp2 a b ha hb 1 one_ne_zero
  simp only [one_mul] at hle
  have hprod := congrArg norm (harcosReciprocalRoots_mul_prime a b ha hb)
  rw [norm_mul, Complex.norm_natCast] at hprod
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  have hpos : 0 < Real.sqrt (p : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  have hl := mul_le_mul_of_nonneg_left hle.2
    (norm_nonneg (harcosReciprocalRootPlus a b))
  have hr := mul_le_mul_of_nonneg_right hle.1
    (norm_nonneg (harcosReciprocalRootMinus a b))
  constructor <;> nlinarith [hle.1, hle.2]

/-- Harcos's Theorem 1 for the actual complete sum, with an arbitrary integer
second frequency and no unproved Weil or root-power premise. -/
theorem completeKloosterman_odd_prime_weil (hp2 : p ≠ 2)
    (a : ZMod p) (d : ℤ) (ha : a ≠ 0) (hd : (d : ZMod p) ≠ 0) :
    ‖completeKloosterman p a d‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  have hs : harcosReciprocalRootPlus a (d : ZMod p) +
      harcosReciprocalRootMinus a (d : ZMod p) = -completeKloosterman p a d := by
    rw [harcosReciprocalRoots_add, harcosCoefficient_one]
  have hn := harcosReciprocalRoots_norm_eq p hp2 a (d : ZMod p) ha hd
  calc
    ‖completeKloosterman p a d‖ =
        ‖harcosReciprocalRootPlus a (d : ZMod p) +
          harcosReciprocalRootMinus a (d : ZMod p)‖ := by rw [hs, norm_neg]
    _ ≤ ‖harcosReciprocalRootPlus a (d : ZMod p)‖ +
        ‖harcosReciprocalRootMinus a (d : ZMod p)‖ := norm_add_le _ _
    _ = _ := by rw [hn.1, hn.2]; ring

/-- The prime-modulus estimate, including `p = 2` and one zero frequency.
Both frequencies may be arbitrary signed integers; only their simultaneous
vanishing modulo the prime is excluded. -/
theorem completeKloosterman_prime_primitive_weil (a d : ℤ)
    (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman p (a : ZMod p) d‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  have hone : 1 ≤ Real.sqrt (p : ℝ) := Real.one_le_sqrt.mpr (by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  by_cases hp2 : p = 2
  · subst p
    rw [completeKloosterman_eq_sum_units]
    calc
      _ ≤ ∑ u : (ZMod 2)ˣ, ‖ZMod.stdAddChar
        ((a : ZMod 2) * (u : ZMod 2) + (d : ZMod 2) * (↑u⁻¹ : ZMod 2))‖ :=
          norm_sum_le _ _
      _ = 1 := by simp only [stdAddChar_norm, sum_const, card_univ,
        ZMod.card_units, nsmul_eq_mul]; norm_num
      _ ≤ _ := by linarith
  by_cases ha : (a : ZMod p) = 0
  · have hd : ¬ (p : ℤ) ∣ d :=
      hprimitive.resolve_left (not_not.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha))
    rw [ha, completeKloosterman_prime_zero_left p d hd, norm_neg, norm_one]
    linarith
  by_cases hd : (d : ZMod p) = 0
  · have he : completeKloosterman p (a : ZMod p) d =
        completeKloosterman p (a : ZMod p) 0 := by
      simp only [completeKloosterman_eq, hd, Int.cast_zero]
    rw [he, completeKloosterman_prime_zero_frequency p _ ha, norm_neg, norm_one]
    linarith
  exact completeKloosterman_odd_prime_weil p hp2 (a : ZMod p) d ha hd

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryOddPrimePower -/

/-!
# Primitive Weil bounds for every power of an odd prime

The prime endpoint uses the accepted prime Weil theorem. Higher even exponents
use square-zero localization and unit-root rigidity; higher odd exponents use
the proved quadratic Gauss cancellation. Unequal prime valuations vanish.
All frequencies are arbitrary signed integers.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem oddPrimePower_modulus_congr (q r : ℕ) [NeZero q] [NeZero r]
    (h : q = r) (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d = completeKloosterman r (a : ZMod r) d := by
  subst r
  rfl

private theorem oddPrimePower_unit_frequencies_sqrt (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 2 ≤ k) (a d : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (hd : ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      2 * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hrpos : 1 ≤ r := by omega
    subst k
    rw [oddPrimePower_modulus_congr _ _ (pow_add p r r) a d]
    have hs : Real.sqrt (((p ^ r * p ^ r : ℕ) : ℝ)) = (p : ℝ) ^ r := by
      rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul_self (by positivity)]
    rw [pow_add, hs]
    exact completeKloosterman_odd_even_power_norm_le p r hp2 hrpos a d ha hd
  · have hrpos : 1 ≤ r := by omega
    subst k
    have hq : p ^ (2 * r + 1) = p * (p ^ r * p ^ r) := by
      rw [pow_succ, mul_comm 2 r, pow_mul, pow_two]
      ring
    rw [oddPrimePower_modulus_congr _ _ hq a d]
    have hs : Real.sqrt (((p * (p ^ r * p ^ r) : ℕ) : ℝ)) =
        (p : ℝ) ^ r * Real.sqrt (p : ℝ) := by
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p),
        Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul_self (by positivity)]
      ring
    rw [hq, hs]
    simpa only [mul_assoc] using
      completeKloosterman_odd_odd_power_norm_le p r hp2 hrpos a d ha hd

/-- The sharp primitive local estimate at every positive exponent. -/
theorem completeKloosterman_odd_prime_power_primitive_sqrt (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : 1 ≤ k) (a d : ℤ)
    (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      2 * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  by_cases hk1 : k = 1
  · subst k
    rw [oddPrimePower_modulus_congr _ _ (pow_one p) a d]
    simpa only [pow_one] using completeKloosterman_prime_primitive_weil p a d hprimitive
  have hk2 : 2 ≤ k := by omega
  have hq : p ^ k = p * p ^ ((k - 2) + 1) := by
    rw [← pow_succ']
    congr 1
    omega
  by_cases ha : (p : ℤ) ∣ a
  · have hd := hprimitive.resolve_left (not_not.mpr ha)
    rw [oddPrimePower_modulus_congr _ _ hq a d,
      completeKloosterman_prime_power_vanish_left p (k - 2) a d ha hd, norm_zero]
    positivity
  by_cases hd : (p : ℤ) ∣ d
  · rw [oddPrimePower_modulus_congr _ _ hq a d,
      completeKloosterman_prime_power_vanish p (k - 2) a d ha hd, norm_zero]
    positivity
  exact oddPrimePower_unit_frequencies_sqrt p k hp2 hk2 a d ha hd

/-- The divisor-factor envelope, including the modulus-one endpoint `k = 0`.
This is the complete Kloosterman sum, not a conditional local-bound interface. -/
theorem completeKloosterman_odd_prime_power_primitive_weil (p k : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (a d : ℤ)
    (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
  rcases k with _ | k
  · rw [oddPrimePower_modulus_congr _ _ (pow_zero p) a d,
      completeKloosterman_modulus_one, norm_one]
    norm_num
  · refine (completeKloosterman_odd_prime_power_primitive_sqrt p (k + 1) hp2
      (by omega) a d hprimitive).trans ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show 2 ≤ k + 1 + 1 by omega))
      (Real.sqrt_nonneg _)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTwoPowerRoots -/

/-!
# Four-root bound over powers of two

If two unit roots have equal squares modulo `2^(n+1)`, their reductions
modulo `2^n` agree up to sign. Each of these two reduction fibers has size
two. The proof uses only divisibility of the difference of squares.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem two_power_dvd_factor (n : ℕ) (x y : ℤ)
    (hx : ¬ 4 ∣ x) (hxy : (2 : ℤ) ^ (n + 1) ∣ x * y) :
    (2 : ℤ) ^ n ∣ y := by
  by_cases hx2 : (2 : ℤ) ∣ x
  · obtain ⟨z, rfl⟩ := hx2
    have hz : ¬ (2 : ℤ) ∣ z := by
      rintro ⟨w, rfl⟩
      apply hx
      exact ⟨w, by ring⟩
    have hh : (2 : ℤ) ^ n ∣ z * y := by
      apply (mul_dvd_mul_iff_left (show (2 : ℤ) ≠ 0 by norm_num)).mp
      simpa only [pow_succ', mul_assoc] using hxy
    exact Int.prime_two.pow_dvd_of_dvd_mul_left n hz hh
  · exact (pow_dvd_pow 2 (Nat.le_succ n)).trans
      (Int.prime_two.pow_dvd_of_dvd_mul_left (n + 1) hx2 hxy)

private theorem two_power_square_congruence (n : ℕ) (x y : ℤ)
    (hy : ¬ (2 : ℤ) ∣ y) (hxy : (2 : ℤ) ^ (n + 1) ∣ x ^ 2 - y ^ 2) :
    (2 : ℤ) ^ n ∣ x - y ∨ (2 : ℤ) ^ n ∣ x + y := by
  have hp : (2 : ℤ) ^ (n + 1) ∣ (x - y) * (x + y) := by
    convert hxy using 1
    ring
  by_cases hm : (4 : ℤ) ∣ x - y
  · have hn : ¬ (4 : ℤ) ∣ x + y := by
      intro hn
      obtain ⟨u, hu⟩ := hm
      obtain ⟨v, hv⟩ := hn
      exact hy ⟨v - u, by omega⟩
    exact Or.inl (two_power_dvd_factor n (x + y) (x - y) hn
      (by simpa only [mul_comm] using hp))
  · exact Or.inr (two_power_dvd_factor n (x - y) (x + y) hm hp)

/-- A unit quadratic congruence with odd leading coefficient has at most four
roots modulo any positive power of two. -/
theorem two_power_unit_quadratic_root_card_le_four (n : ℕ) (a d : ℤ)
    (ha : ¬ (2 : ℤ) ∣ a) :
    (univ.filter fun v : ZMod (2 ^ n * 2) ↦
      IsUnit v ∧ (a : ZMod (2 ^ n * 2)) * v ^ 2 = (d : ZMod (2 ^ n * 2))).card ≤
      4 := by
  classical
  let s := univ.filter fun v : ZMod (2 ^ n * 2) ↦
    IsUnit v ∧ (a : ZMod (2 ^ n * 2)) * v ^ 2 = (d : ZMod (2 ^ n * 2))
  let f := ZMod.castHom (Nat.dvd_mul_right (2 ^ n) 2) (ZMod (2 ^ n))
  by_cases hs : s.Nonempty
  · obtain ⟨v, hv⟩ := hs
    obtain ⟨y, rfl⟩ := ZMod.intCast_surjective v
    have hv' := (mem_filter.mp hv).2
    have hy : ¬ (2 : ℤ) ∣ y := by
      intro hy
      have hunit := hv'.1.map
        (ZMod.castHom (show 2 ∣ 2 ^ n * 2 from dvd_mul_left 2 _) (ZMod 2))
      have hz : (y : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd y 2).mpr hy
      exact hunit.ne_zero (by simpa only [map_intCast] using hz)
    have hsub : s ⊆ univ.filter fun u ↦ f u ∈ ({f (y : ZMod (2 ^ n * 2)),
        -f (y : ZMod (2 ^ n * 2))} : Finset (ZMod (2 ^ n))) := by
      intro u hu
      obtain ⟨x, rfl⟩ := ZMod.intCast_surjective u
      have hu' := (mem_filter.mp hu).2
      have hz : ((a * (x ^ 2 - y ^ 2) : ℤ) : ZMod (2 ^ n * 2)) = 0 := by
        push_cast
        linear_combination hu'.2 - hv'.2
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
      have hsq : (2 : ℤ) ^ (n + 1) ∣ x ^ 2 - y ^ 2 := by
        apply Int.prime_two.pow_dvd_of_dvd_mul_left (n + 1) ha
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_succ] using hdvd
      have he := two_power_square_congruence n x y hy hsq
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        f, map_intCast]
      rcases he with hm | hp
      · left
        apply sub_eq_zero.mp
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) (2 ^ n)).mpr
          (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hm)
        simpa only [Int.cast_sub] using this
      · right
        apply eq_neg_iff_add_eq_zero.mpr
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x + y) (2 ^ n)).mpr
          (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hp)
        simpa only [Int.cast_add] using this
    have hc := card_le_card hsub
    rw [zmod_reduction_preimage_card] at hc
    have hcard : ({f (y : ZMod (2 ^ n * 2)),
        -f (y : ZMod (2 ^ n * 2))} : Finset (ZMod (2 ^ n))).card ≤ 2 :=
      (card_insert_le _ _).trans (by simp)
    exact hc.trans (Nat.mul_le_mul_right 2 hcard)
  · change s.card ≤ 4
    rw [not_nonempty_iff_eq_empty.mp hs]
    simp

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTwoPower -/

/-!
# Primitive Kloosterman estimates at powers of two

The square-zero layer localizes the sum to unit quadratic roots modulo the
smaller half-power. Four roots and the exact size of the reduction fibers
suffice: the factor `k+1` absorbs the elementary stationary-phase constant.
No odd-characteristic Gauss-sum identity is used.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem two_power_modulus_congr (q r : ℕ) [NeZero q] [NeZero r]
    (h : q = r) (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d =
      completeKloosterman r (a : ZMod r) d := by
  subst r
  rfl

private theorem two_power_layer_norm_le (q r : ℕ) [NeZero q] [NeZero r]
    (hqr : q ∣ r) (a d : ℤ) :
    ‖completeKloosterman (q * r) (a : ZMod (q * r)) d‖ ≤
      (r : ℝ) * ((univ.filter fun v : ZMod q ↦
        IsUnit v ∧ (a : ZMod q) * v ^ 2 = (d : ZMod q)).card : ℝ) := by
  classical
  let f := ZMod.castHom (Nat.dvd_mul_right q r) (ZMod q)
  let s := univ.filter fun v : ZMod q ↦
    IsUnit v ∧ (a : ZMod q) * v ^ 2 = (d : ZMod q)
  have ht : (r : ZMod (q * r)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    obtain ⟨c, hc⟩ := hqr
    exact ⟨c, by rw [hc]; ring⟩
  have hloc := completeKloosterman_square_zero_localization (q * r)
    (a : ZMod (q * r)) (r : ZMod (q * r)) d ht
  simp only [zmod_mul_modulus_eq_zero_iff, map_sub, map_mul, map_pow, map_intCast,
    sub_eq_zero] at hloc
  have hnorm :
      ‖completeKloosterman (q * r) (a : ZMod (q * r)) d‖ ≤
        ((univ.filter fun u : ZMod (q * r) ↦
          IsUnit u ∧ (a : ZMod q) * (f u) ^ 2 = (d : ZMod q)).card : ℝ) := by
    rw [hloc]
    convert norm_sum_le univ (fun u : ZMod (q * r) ↦
      if IsUnit u ∧ (a : ZMod q) * (f u) ^ 2 = (d : ZMod q)
      then ZMod.stdAddChar ((a : ZMod (q * r)) * u + (d : ZMod (q * r)) * u⁻¹)
      else 0) using 1
    simp only [apply_ite norm, stdAddChar_norm, norm_zero, sum_boole]
  have hcard :
      (univ.filter fun u : ZMod (q * r) ↦
        IsUnit u ∧ (a : ZMod q) * (f u) ^ 2 = (d : ZMod q)).card ≤ s.card * r := by
    rw [← zmod_reduction_preimage_card]
    apply card_le_card
    intro u hu
    simp only [mem_filter, mem_univ, true_and, s] at hu ⊢
    exact ⟨hu.1.map f, hu.2⟩
  exact hnorm.trans (by exact_mod_cast hcard.trans_eq (Nat.mul_comm s.card r))

private theorem two_power_stationary_bound (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (a d : ℤ) (ha : ¬ (2 : ℤ) ∣ a) :
    ‖completeKloosterman (2 ^ (n + m)) (a : ZMod (2 ^ (n + m))) d‖ ≤
      4 * (2 : ℝ) ^ m := by
  have hroot :
      (univ.filter fun v : ZMod (2 ^ n) ↦
        IsUnit v ∧ (a : ZMod (2 ^ n)) * v ^ 2 = (d : ZMod (2 ^ n))).card ≤ 4 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    convert! two_power_unit_quadratic_root_card_le_four j a d ha using 1
  have hl := two_power_layer_norm_le (2 ^ n) (2 ^ m) (pow_dvd_pow 2 hnm) a d
  suffices h : ‖completeKloosterman (2 ^ n * 2 ^ m)
      (a : ZMod (2 ^ n * 2 ^ m)) d‖ ≤ 4 * (2 : ℝ) ^ m by
    convert! h using 1
    exact congrArg norm (two_power_modulus_congr _ _ (pow_add 2 n m) a d)
  refine hl.trans ?_
  have hr : ((univ.filter fun v : ZMod (2 ^ n) ↦
      IsUnit v ∧ (a : ZMod (2 ^ n)) * v ^ 2 = (d : ZMod (2 ^ n))).card : ℝ) ≤ 4 :=
    by exact_mod_cast hroot
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using
    mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ (2 ^ m : ℕ) by positivity)

private theorem two_power_trivial_norm_le (q : ℕ) [NeZero q] (a d : ℤ) :
    ‖completeKloosterman q (a : ZMod q) d‖ ≤ (q : ℝ) := by
  classical
  rw [completeKloosterman_eq]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _u : ZMod q, (1 : ℝ) := by
      apply sum_le_sum
      intro u _
      split_ifs <;> simp
    _ = (q : ℝ) := by simp

private theorem two_power_sqrt_even (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (2 * n)) = (2 : ℝ) ^ n := by
  rw [mul_comm 2 n, pow_mul, Real.sqrt_sq (by positivity)]

private theorem two_power_sqrt_odd (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (2 * n + 1)) = (2 : ℝ) ^ n * Real.sqrt 2 := by
  rw [pow_succ, Real.sqrt_mul (by positivity), two_power_sqrt_even]

private theorem two_power_odd_coefficient_bound :
    (8 : ℝ) ≤ 6 * Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

private theorem two_power_primitive_odd_left (k : ℕ) (a d : ℤ)
    (ha : ¬ (2 : ℤ) ∣ a) :
    ‖completeKloosterman (2 ^ k) (a : ZMod (2 ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ k) := by
  by_cases hk : k < 4
  · have ht := two_power_trivial_norm_le (2 ^ k) a d
    have hs : (2 : ℝ) ^ k ≤ ((k + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ k) := by
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hk' with rfl | rfl | rfl | rfl
      · norm_num
      · norm_num only [pow_one, Nat.cast_add, Nat.cast_one]
        have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have hp := Real.sqrt_nonneg (2 : ℝ)
        nlinarith
      · norm_num [show Real.sqrt (4 : ℝ) = 2 from by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      · norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ,
          pow_zero, one_mul]
        have h := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
        have hp := Real.sqrt_nonneg (8 : ℝ)
        nlinarith
    exact ht.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hs)
  · have hk4 : 4 ≤ k := by omega
    obtain ⟨n, he | ho⟩ := Nat.even_or_odd' k
    · subst k
      have hn : 2 ≤ n := by omega
      have ht := two_power_stationary_bound n n (by omega) le_rfl a d ha
      rw [show n + n = 2 * n by omega] at ht
      rw [two_power_sqrt_even]
      refine ht.trans ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show 4 ≤ 2 * n + 1 by omega)
    · subst k
      have hn : 2 ≤ n := by omega
      have ht := two_power_stationary_bound n (n + 1) (by omega) (by omega) a d ha
      rw [show n + (n + 1) = 2 * n + 1 by omega] at ht
      rw [two_power_sqrt_odd]
      refine ht.trans ?_
      have hc : (6 : ℝ) ≤ ((2 * n + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 6 ≤ 2 * n + 1 + 1)
      have hcoef := two_power_odd_coefficient_bound.trans
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg 2))
      calc
        4 * (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 8 := by rw [pow_succ]; ring
        _ ≤ (2 : ℝ) ^ n * (((2 * n + 1 + 1 : ℕ) : ℝ) * Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hcoef (by positivity)
        _ = _ := by ring

/-- Primitive Weil-type bound at every power of two, including modulus one.
The elementary stationary bound is absorbed by the divisor factor `k+1`. -/
theorem completeKloosterman_two_power_primitive_weil (k : ℕ) (a d : ℤ)
    (hprimitive : ¬ (2 : ℤ) ∣ a ∨ ¬ (2 : ℤ) ∣ d) :
    ‖completeKloosterman (2 ^ k) (a : ZMod (2 ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ k) := by
  rcases hprimitive with ha | hd
  · exact two_power_primitive_odd_left k a d ha
  · rw [completeKloosterman_symm]
    exact two_power_primitive_odd_left k d a hd

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLocalGlobalPrimePower -/

/-!
# Removing common prime factors from signed frequencies

The only analytic input is the primitive prime-power estimate. The descent
retains the totient correction at modulus one, so both zero frequencies and
arbitrary signed nonprimitive frequencies are included.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem localGlobal_completeKloosterman_congr_modulus (q r : ℕ) [NeZero q] [NeZero r]
    (h : q = r) (a d : ℤ) :
    completeKloosterman q (a : ZMod q) d = completeKloosterman r (a : ZMod r) d := by
  subst r
  rfl

theorem localGlobal_completeKloosterman_one (a d : ℤ) :
    completeKloosterman 1 (a : ZMod 1) d = 1 := by
  rw [completeKloosterman_eq_sum_units]
  have hz (z : ZMod 1) : z = 0 := Subsingleton.elim _ _
  simp [hz]

theorem localGlobal_prime_power_descent_norm (p k : ℕ) [Fact p.Prime] (a d : ℤ) :
    ‖completeKloosterman (p ^ (k + 1)) ((p * a : ℤ) : ZMod (p ^ (k + 1)))
        (p * d)‖ ≤
      (p : ℝ) * ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ := by
  have hp : p.Prime := Fact.out
  have hφ : (p ^ (k + 1)).totient ≤ p * (p ^ k).totient := by
    cases k with
    | zero => simpa using Nat.totient_le p
    | succ k =>
      rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp, pow_succ]
      exact le_of_eq (by ring)
  have hpos : (0 : ℝ) < (p ^ k).totient := by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hp.pos k)
  have hs : completeKloosterman (p ^ (k + 1)) ((p * a : ℤ) : ZMod (p ^ (k + 1)))
      (p * d) = ((p ^ (k + 1)).totient : ℂ) / ((p ^ k).totient : ℂ) *
        completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d := by
    rw [localGlobal_completeKloosterman_congr_modulus _ _ (pow_succ p k),
      completeKloosterman_common_factor]
    rw [pow_succ]
  rw [hs, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_iff₀ hpos).mpr
  exact_mod_cast hφ

theorem localGlobal_gcd_scale (p n : ℕ) (a d : ℤ) :
    (p * n).gcd ((p * a : ℤ).natAbs.gcd (p * d : ℤ).natAbs) =
      p * n.gcd (a.natAbs.gcd d.natAbs) := by
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Nat.gcd_mul_left]

theorem localGlobal_sqrt_scale (p n g : ℕ) :
    Real.sqrt (p * g : ℕ) * Real.sqrt (p * n : ℕ) =
      (p : ℝ) * Real.sqrt g * Real.sqrt n := by
  simp only [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p)]
  calc
    _ = (Real.sqrt p * Real.sqrt p) * (Real.sqrt g * Real.sqrt n) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg p)]; ring

/-- Exact all-frequency prime-power reduction. The primitive input is explicit,
and is not being asserted as an unconditional analytic theorem here. -/
theorem completeKloosterman_prime_power_weil_of_primitive
    (p : ℕ) [Fact p.Prime]
    (hlocal : ∀ (k : ℕ) (a d : ℤ), (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) →
      ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ))
    (k : ℕ) (a d : ℤ) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt ((p ^ k).gcd (a.natAbs.gcd d.natAbs)) *
        Real.sqrt (p ^ k : ℕ) := by
  induction k generalizing a d with
  | zero =>
    rw [localGlobal_completeKloosterman_congr_modulus _ _ (pow_zero p),
      localGlobal_completeKloosterman_one]
    simp
  | succ k ih =>
    by_cases hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d
    · apply (hlocal (k + 1) a d hprimitive).trans
      have hg : (1 : ℝ) ≤ Real.sqrt ((p ^ (k + 1)).gcd (a.natAbs.gcd d.natAbs)) :=
        Real.one_le_sqrt.mpr (by
          exact_mod_cast Nat.gcd_pos_of_pos_left (a.natAbs.gcd d.natAbs)
            (pow_pos (Fact.out : p.Prime).pos (k + 1)))
      have hs := mul_le_mul_of_nonneg_left hg
        (show (0 : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) by positivity)
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (p ^ (k + 1) : ℕ))
    · obtain ⟨a', rfl⟩ := (not_or.mp hprimitive).1 |> not_not.mp
      obtain ⟨d', rfl⟩ := (not_or.mp hprimitive).2 |> not_not.mp
      calc
        _ ≤ (p : ℝ) * ‖completeKloosterman (p ^ k) (a' : ZMod (p ^ k)) d'‖ :=
          localGlobal_prime_power_descent_norm p k a' d'
        _ ≤ (p : ℝ) * (((k + 1 : ℕ) : ℝ) *
            Real.sqrt ((p ^ k).gcd (a'.natAbs.gcd d'.natAbs)) *
            Real.sqrt (p ^ k : ℕ)) :=
          mul_le_mul_of_nonneg_left (ih a' d') (Nat.cast_nonneg p)
        _ = ((k + 1 : ℕ) : ℝ) *
            (Real.sqrt ((p ^ (k + 1)).gcd
              ((p * a' : ℤ).natAbs.gcd (p * d' : ℤ).natAbs)) *
              Real.sqrt (p ^ (k + 1) : ℕ)) := by
          rw [pow_succ', localGlobal_gcd_scale, localGlobal_sqrt_scale]
          ring
        _ ≤ _ := by
          rw [mul_assoc]
          gcongr
          exact_mod_cast Nat.le_succ k

theorem localGlobal_card_divisors_prime_power (p k : ℕ) [Fact p.Prime] :
    (p ^ k).divisors.card = k + 1 := by
  simp [Nat.divisors_prime_pow (Fact.out : p.Prime)]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryLocalGlobal -/

/-!
# From primitive prime powers to every nonzero modulus

Chinese remaindering twists both frequencies by a Bezout coefficient. Its
coprimality with the corresponding modulus preserves the full three-way gcd.
Together with exact common-factor descent this proves the all-modulus estimate
from a single explicitly quantified primitive prime-power input.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem localGlobal_bezout_coprime (m n : ℕ) (h : m.Coprime n) :
    m.Coprime (m.gcdB n).natAbs ∧ n.Coprime (m.gcdA n).natAbs := by
  have he : (m : ℤ) * m.gcdA n + (n : ℤ) * m.gcdB n = 1 := by
    simpa only [h.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab m n).symm
  have hb : IsCoprime (m : ℤ) (m.gcdB n) :=
    ⟨m.gcdA n, (n : ℤ), by simpa only [mul_comm] using he⟩
  have ha : IsCoprime (n : ℤ) (m.gcdA n) :=
    ⟨m.gcdB n, (m : ℤ), by simpa only [mul_comm, add_comm] using he⟩
  constructor
  · simpa only [Nat.coprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using
      Int.isCoprime_iff_gcd_eq_one.mp hb
  · simpa only [Nat.coprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using
      Int.isCoprime_iff_gcd_eq_one.mp ha

theorem localGlobal_gcd_twist (q : ℕ) (b a d : ℤ) (hb : q.Coprime b.natAbs) :
    q.gcd ((a * b).natAbs.gcd (d * b).natAbs) = q.gcd (a.natAbs.gcd d.natAbs) := by
  rw [Int.natAbs_mul, Int.natAbs_mul, Nat.gcd_mul_right]
  exact hb.symm.gcd_mul_right_cancel_right _

theorem localGlobal_gcd_coprime_mul (m n g : ℕ) (h : m.Coprime n) :
    (m * n).gcd g = m.gcd g * n.gcd g := by
  simpa only [Nat.gcd_comm] using h.gcd_mul g

theorem localGlobal_weil_envelope_mul (m n g : ℕ) (h : m.Coprime n) :
    ((m * n).divisors.card : ℝ) * Real.sqrt ((m * n).gcd g) * Real.sqrt (m * n : ℕ) =
      ((m.divisors.card : ℝ) * Real.sqrt (m.gcd g) * Real.sqrt m) *
        ((n.divisors.card : ℝ) * Real.sqrt (n.gcd g) * Real.sqrt n) := by
  rw [h.card_divisors_mul, localGlobal_gcd_coprime_mul m n g h]
  simp only [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg (m.gcd g)),
    Real.sqrt_mul (Nat.cast_nonneg m)]
  ring

/-- Conditional all-modulus Weil bound, with signed frequencies, modulus one,
and zero or nonprimitive frequencies. Only primitive prime-power bounds are
assumed; coprime assembly and common-factor descent are proved. -/
theorem completeKloosterman_weil_of_primitive_prime_power
    (hlocal : ∀ (p k : ℕ) (_ : Fact p.Prime) (a d : ℤ),
      (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) →
      ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ))
    (q : ℕ) [NeZero q] (a d : ℤ) :
    ‖completeKloosterman q (a : ZMod q) d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (a.natAbs.gcd d.natAbs)) * Real.sqrt q := by
  have hall : ∀ (q : ℕ) (_ : NeZero q) (a d : ℤ),
      ‖completeKloosterman q (a : ZMod q) d‖ ≤
        (q.divisors.card : ℝ) * Real.sqrt (q.gcd (a.natAbs.gcd d.natAbs)) *
          Real.sqrt q := by
    refine Nat.recOnPrimeCoprime ?_ ?_ ?_
    · intro hq
      exact False.elim (hq.out rfl)
    · intro p k hp hq a d
      let : Fact p.Prime := ⟨hp⟩
      rw [localGlobal_card_divisors_prime_power]
      exact completeKloosterman_prime_power_weil_of_primitive p
        (fun k a d ↦ hlocal p k inferInstance a d) k a d
    · intro m n hm hn hmn hmBound hnBound hq a d
      let : NeZero m := ⟨by omega⟩
      let : NeZero n := ⟨by omega⟩
      have htwist := localGlobal_bezout_coprime m n hmn
      rw [completeKloosterman_crt m n hmn, norm_mul]
      have hleft := hmBound inferInstance (a * m.gcdB n) (d * m.gcdB n)
      have hright := hnBound inferInstance (a * m.gcdA n) (d * m.gcdA n)
      rw [localGlobal_gcd_twist m _ a d htwist.1] at hleft
      rw [localGlobal_gcd_twist n _ a d htwist.2] at hright
      rw [localGlobal_weil_envelope_mul m n _ hmn]
      exact mul_le_mul hleft hright (norm_nonneg _) (by positivity)
  exact hall q inferInstance a d

/-- The residue-valued interface used by the existing Weil-to-Fouvry bridge. -/
theorem completeKloosterman_weil_zmod_of_primitive_prime_power
    (hlocal : ∀ (p k : ℕ) (_ : Fact p.Prime) (a d : ℤ),
      (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) →
      ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ))
    (q : ℕ) [NeZero q] (m : ZMod q) (d : ℤ) :
    ‖completeKloosterman q m d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (m.val.gcd d.natAbs)) * Real.sqrt q := by
  simpa only [Int.natAbs_natCast, Int.cast_natCast, ZMod.natCast_zmod_val] using
    completeKloosterman_weil_of_primitive_prime_power hlocal q (m.val : ℤ) d

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean -/

/-!
# Fixed-order divisor means and coefficient square sums

The actual ordered divisor function is the Dirichlet convolution power `ζ ^ k`.
The mean estimate uses only the elementary hyperbola identity and the harmonic
sum bound. The square majorant is unrestricted: no squarefree support is needed.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWeilBridge -/

/-!
# The exact interval and gcd form of the conditional Weil-to-Fouvry bridge

The complete Kloosterman estimate is an explicit hypothesis, not a proved
input. The interval conversion and the divisor/logarithm payment are proved.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {q : ℕ} [NeZero q]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

section
/- SOURCE MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCompleteWeil -/


/-!
# Unconditional complete Weil and Fouvry interval estimates

The odd-prime-power Gauss argument and the separate two-power stationary bound
supply every primitive local estimate. Exact frequency descent and twisted CRT
then give the divisor/gcd envelope for every positive modulus. The existing
Fourier completion yields Fouvry's Lemma 3, uniformly in signed frequencies and
real interval endpoints; no complete-sum estimate remains as a hypothesis.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem completeKloosterman_prime_power_primitive_weil (p k : ℕ) [Fact p.Prime]
    (a d : ℤ) (hprimitive : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ d) :
    ‖completeKloosterman (p ^ k) (a : ZMod (p ^ k)) d‖ ≤
      ((k + 1 : ℕ) : ℝ) * Real.sqrt (p ^ k : ℕ) := by
  by_cases hp : p = 2
  · subst p
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      completeKloosterman_two_power_primitive_weil k a d hprimitive
  · exact completeKloosterman_odd_prime_power_primitive_weil p k hp a d hprimitive


theorem completeKloosterman_weil_zmod (q : ℕ) [NeZero q] (m : ZMod q) (d : ℤ) :
    ‖completeKloosterman q m d‖ ≤
      (q.divisors.card : ℝ) * Real.sqrt (q.gcd (m.val.gcd d.natAbs)) *
        Real.sqrt q := by
  exact completeKloosterman_weil_zmod_of_primitive_prime_power
    (fun p k _ a d ↦ completeKloosterman_prime_power_primitive_weil p k a d) q m d

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
end
end

namespace FareyHD8006
open Finset
open scoped BigOperators

end FareyHD8006

open Finset
open scoped BigOperators

namespace FareyHD8006
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

end FareyHD8006

namespace HD8006
open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators

end HD8006

open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators
namespace HD8006
noncomputable section
variable {q : ℕ} [NeZero q]

end
end HD8006

open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators
namespace HD8006
noncomputable section
variable {q : ℕ} [NeZero q]

end
end HD8006

open Finset

end

/- Source PEqualNP.Outside.L_b13_prime_inverse_moment -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical ComplexConjugate Finset

noncomputable section

theorem sum_mul_stdAddChar {p : ℕ} [NeZero p] (t : ZMod p) :
    ∑ a : ZMod p, ZMod.stdAddChar (a*t) = if t = 0 then (p : ℂ) else 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [ZMod.card]
  · rw [ite_eq_right ht]
    simpa only [AddChar.mulShift_apply, mul_comm] using AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p ht)

theorem conj_stdAddChar {p : ℕ} [NeZero p] (z : ZMod p) :
    conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_goldbach_frontier_type2_b1_b3 -/
section

namespace GoldbachTypeII13

/- Adapted from xuanyou-li, goldbach-proofs PR #2489,
   revision 653f53ba55eea5e3ce3bd067ece0d7e30e37cba2 (Apache-2.0).
   Uses a larger cofactor cutoff for the short part of the third band. -/

/-!
The high band has an expansion in short-step geometric sums.
Away from their rational centres, a weighted square-mean estimate controls the integral.
Near the centres, the Ramanujan-sum expansion reduces the smoothed integral to
primitive Dirichlet characters. The character large sieve on dyadic conductor
intervals gives the needed saving after summing the denominator weights.
-/
section

/- Adapted from goldbach-proofs PR #2468, revision
3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0).
The geometric estimates there adapt openai/math, revision
3344da59991ed94f9ba711217b29c1d760badfa6, module GeometricCharacterBound
(Apache-2.0). These selected estimates use a common grid-neighbourhood radius. -/

namespace DyadicMixedB4Geometric
open Finset MeasureTheory
noncomputable section
def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
/-- The chord distance for a phase of period one. -/
theorem norm_exp_phase_sub_one (x : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * x / 2 = Real.pi * x := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num

@[simp] theorem norm_phase' (x : ℝ) : ‖phase x‖=1 := by simp [phase, Complex.norm_exp]

def sep (u v : ℕ) (z : ℕ×ℕ) : ℝ := |(z.1:ℝ)/u-(z.2:ℝ)/v|

def smoothKernel (a c t : ℝ) := 1/(a+|t-c|)
def pairEnv (a b : ℝ) (u v : ℕ) (z : ℕ×ℕ) (t : ℝ) : ℝ :=
  let x := (z.1:ℝ)/u
  let y := (z.2:ℝ)/v
  if sep u v z=0 then (16/((u:ℝ)*v))*(smoothKernel b x t)^2 else
    (4/((u:ℝ)*v))*(sep u v z)⁻¹*(smoothKernel a x t+smoothKernel a y t)

end
end DyadicMixedB4Geometric

end

section

/- Rational-centre reductions adapted from goldbach-proofs PR #2468,
revision 3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/

namespace DyadicMixedB4ArcGeometry
open Finset MeasureTheory DyadicMixedB4Geometric
noncomputable section

def radius (M : ℕ) : ℝ := 1 / (8 * (M : ℝ) ^ 2)

def wide (n B H : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q ∧
    |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)}

end
end DyadicMixedB4ArcGeometry

end

section

open Finset MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcGeometry

namespace DyadicMixedB4ArcCenters

noncomputable section

end
end DyadicMixedB4ArcCenters

end

section

open Finset MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcCenters

namespace DyadicMixedB4ProgressionApprox

noncomputable section

end
end DyadicMixedB4ProgressionApprox

end

section

open MeasureTheory

namespace DyadicMixedB4SineKernel

noncomputable section

end
end DyadicMixedB4SineKernel

end

section

open MeasureTheory DyadicMixedB4SineKernel DyadicMixedB4Geometric

namespace DyadicMixedB4KernelVariation

noncomputable section

end
end DyadicMixedB4KernelVariation

end

section

open MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcCenters
open DyadicMixedB4ProgressionApprox DyadicMixedB4SineKernel

namespace DyadicMixedB4NearKernelFourier

noncomputable section

end
end DyadicMixedB4NearKernelFourier

end

section

open MeasureTheory DyadicMixedB4ArcGeometry DyadicMixedB4Geometric
open DyadicMixedB4ProgressionApprox DyadicMixedB4SineKernel DyadicMixedB4NearKernelFourier

namespace DyadicMixedB4WindowKernel

noncomputable section

end
end DyadicMixedB4WindowKernel

end

section

open Finset MeasureTheory

namespace DyadicMixedB4Abel

end DyadicMixedB4Abel

end

section

open MeasureTheory Finset DyadicMixedB4ArcGeometry DyadicMixedB4WindowKernel
open DyadicMixedB4SineKernel DyadicMixedB4KernelVariation

namespace DyadicMixedB4KernelControl

noncomputable section

end
end DyadicMixedB4KernelControl

end

section

open Finset MeasureTheory
open scoped ComplexConjugate

namespace DyadicMixedB4Fourier

noncomputable section

end
end DyadicMixedB4Fourier

end

section

open Finset MeasureTheory Set

namespace DyadicMixedB4Sampling

end DyadicMixedB4Sampling

end

section

open Finset Set
open scoped RealInnerProductSpace

namespace DyadicMixedB4Fourier

noncomputable section

end
end DyadicMixedB4Fourier

end

section

/- Adapted from the corresponding Additive, Farey, CharacterSums, and
CharacterOrthogonality modules of kimihiro64/bombieri-vinogradov
at 7a1748306e026825ed6a5555516cc2f28989b2ac (Apache-2.0).
The original notices are retained. The imports have been combined. -/


/-!
# Rational spacing for the additive large sieve

Reduced rational points with denominators at most `Q` are separated by at
least `1 / Q^2`.  This is the arithmetic spacing input in Vaughan's additive
large-sieve theorem.
-/


namespace BombieriVinogradov.LargeSieve

end BombieriVinogradov.LargeSieve

/-!
# Reduced Farey points for the additive large sieve

This module packages the reduced fractions `a / q`, with `1 <= q <= Q` and
`a` a unit modulo `q`, and proves their circular `1 / Q^2` separation.
-/


namespace BombieriVinogradov.LargeSieve

end BombieriVinogradov.LargeSieve

/-!
# Character sums for the large-sieve route

This module fixes the exact source-level objects used in Vaughan's character
large-sieve theorem.  Proofs live under `Proof/LargeSieve` so that changes to
the analytic argument do not destabilize the project-wide statement surface.
-/


noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

end BombieriVinogradov.LargeSieve

/-!
# Character orthogonality and Parseval

This file isolates the exact finite Fourier calculation used in the
multiplicative large-sieve route.  It deliberately sums over the unit group,
where conjugating a character value is the same as evaluating at the inverse.
-/


noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

noncomputable local instance unitFintype (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

end BombieriVinogradov.LargeSieve

end

section

open Complex Finset Real

namespace BombieriVinogradov.LargeSieve

noncomputable section

noncomputable local instance fareyUnitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

end
end BombieriVinogradov.LargeSieve

end

section

/- Adapted from CharacterReduction.lean in kimihiro64/bombieri-vinogradov
at 7a1748306e026825ed6a5555516cc2f28989b2ac (Apache-2.0).
The additive-sieve input uses real interval sampling, with constant 64. -/

/-!
# Reduction from primitive characters to additive Farey samples

This module proves Vaughan's primitive Dirichlet-character large sieve from
the additive large sieve. The reduction uses the composite-modulus primitive
Gauss-sum norm, character Parseval on the unit group, and an exact translation
of arbitrary integer intervals to the coefficient convention used by the
Farey additive theorem.
-/


noncomputable section

open Complex Finset Real
open scoped BigOperators ComplexConjugate

namespace BombieriVinogradov.LargeSieve

noncomputable local instance characterReductionUnitFintype
    (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

end BombieriVinogradov.LargeSieve

end

section

open Finset
open scoped Classical

namespace DyadicMixedB4DualCharacter

noncomputable section

end
end DyadicMixedB4DualCharacter

end

section

open Finset MeasureTheory

namespace DyadicMixedB4MaximalSieve

open DyadicMixedB4Fourier DyadicMixedB4Geometric BombieriVinogradov.LargeSieve

noncomputable section

end
end DyadicMixedB4MaximalSieve

end

section

open Finset MeasureTheory DyadicMixedB4MaximalSieve DyadicMixedB4DualCharacter

namespace DyadicMixedB4MixedCharacter

noncomputable section

end
end DyadicMixedB4MixedCharacter

end

section

open Finset MeasureTheory DyadicMixedB4KernelControl DyadicMixedB4WindowKernel
open DyadicMixedB4ArcGeometry DyadicMixedB4MixedCharacter DyadicMixedB4MaximalSieve

namespace DyadicMixedB4DyadicBlock

noncomputable section

end
end DyadicMixedB4DyadicBlock

end

section

open Finset MeasureTheory ArithmeticFunction DyadicMixedB4DyadicBlock
open DyadicMixedB4ArcGeometry DyadicMixedB4KernelControl DyadicMixedB4MixedCharacter DyadicMixedB4MaximalSieve

namespace DyadicMixedB4FixedBlock

noncomputable section

end
end DyadicMixedB4FixedBlock

end

section

open Finset MeasureTheory DyadicMixedB4MaximalSieve BombieriVinogradov.LargeSieve

namespace DyadicMixedB4PrimitiveEnergy

noncomputable section

end
end DyadicMixedB4PrimitiveEnergy

end

section

open Finset MeasureTheory ArithmeticFunction BombieriVinogradov.LargeSieve
open DyadicMixedB4FixedBlock DyadicMixedB4PrimitiveEnergy DyadicMixedB4DyadicBlock
open DyadicMixedB4MaximalSieve DyadicMixedB4MixedCharacter

namespace DyadicMixedB4BilinearEnergy

noncomputable section

end
end DyadicMixedB4BilinearEnergy

end

section

open Finset BombieriVinogradov.LargeSieve DyadicMixedB4DualCharacter
open scoped Classical

namespace DyadicMixedB4GaussLift

noncomputable section

end
end DyadicMixedB4GaussLift

end

section

open Finset ArithmeticFunction BombieriVinogradov.LargeSieve DyadicMixedB4GaussLift
open scoped ArithmeticFunction.Moebius Classical

namespace DyadicMixedB4MoebiusGauss

noncomputable section

def moebiusComplex (m : ℕ) : ℂ := (μ m : ℂ)

theorem norm_moebiusComplex_le_one (m : ℕ) : ‖moebiusComplex m‖ ≤ 1 := by
  rw [moebiusComplex, Complex.norm_intCast]
  exact_mod_cast (abs_moebius_le_one (n := m))

end
end DyadicMixedB4MoebiusGauss

end

section

open Finset DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss
open scoped Classical

namespace DyadicMixedB4ImprimitiveBound

noncomputable section

end
end DyadicMixedB4ImprimitiveBound

end

section

open Finset DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss BombieriVinogradov.LargeSieve
open scoped Classical ComplexConjugate

namespace DyadicMixedB4Ramanujan

noncomputable section

end
end DyadicMixedB4Ramanujan

end

section

open Finset BombieriVinogradov.LargeSieve

namespace DyadicMixedB4RamanujanCharacters

noncomputable section

noncomputable local instance unitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

end
end DyadicMixedB4RamanujanCharacters

end

section

open Finset DyadicMixedB4GaussLift DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open BombieriVinogradov.LargeSieve DyadicMixedB4Ramanujan DyadicMixedB4RamanujanCharacters

namespace DyadicMixedB4RamanujanUnits

noncomputable section

noncomputable local instance unitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

end
end DyadicMixedB4RamanujanUnits

end

section

open Finset DyadicMixedB4ImprimitiveBound DyadicMixedB4RamanujanCharacters

namespace DyadicMixedB4CharacterFactorBound

noncomputable section

end
end DyadicMixedB4CharacterFactorBound

end

section

open Finset ArithmeticFunction

namespace DyadicMixedB4BadPrimeMass

end DyadicMixedB4BadPrimeMass

end

section

open Finset ArithmeticFunction DyadicMixedB4ArcCenters DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss
open DyadicMixedB4RamanujanUnits DyadicMixedB4RamanujanCharacters DyadicMixedB4CharacterFactorBound
open DyadicMixedB4BadPrimeMass BombieriVinogradov.LargeSieve

namespace DyadicMixedB4RamanujanError

noncomputable section

noncomputable local instance unitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

end
end DyadicMixedB4RamanujanError

end

section

open Finset ArithmeticFunction DyadicMixedB4RamanujanError DyadicMixedB4BadPrimeMass
open DyadicMixedB4ArcCenters

namespace DyadicMixedB4PrimitiveAt

noncomputable section

end
end DyadicMixedB4PrimitiveAt

end

section

open Finset BombieriVinogradov.LargeSieve

namespace DyadicMixedB4ConductorPartition

noncomputable section

end
end DyadicMixedB4ConductorPartition

end

section

open Finset DyadicMixedB4PrimitiveAt DyadicMixedB4RamanujanError DyadicMixedB4RamanujanCharacters
open BombieriVinogradov.LargeSieve DyadicMixedB4ConductorPartition
open DyadicMixedB4CharacterFactorBound

namespace DyadicMixedB4PrimitiveExpansion

noncomputable section

end
end DyadicMixedB4PrimitiveExpansion

end

section

open Finset

namespace DyadicMixedB4GcdHarmonic

theorem sum_inverse_Icc_le (L : ℕ) :
    (∑ t ∈ Icc 1 L, (t : ℝ)⁻¹) ≤ 1 + Real.log L := by
  have bound := harmonic_le_one_add_log L
  rw [harmonic_eq_sum_Icc] at bound
  push_cast at bound
  exact bound

theorem sum_inverse_multiples (D L : ℕ) (DPositive : 0 < D) :
    (∑ u ∈ (Icc 1 L).filter (fun u => D ∣ u), (u : ℝ)⁻¹) =
      (D : ℝ)⁻¹ * ∑ k ∈ Icc 1 (L / D), (k : ℝ)⁻¹ := by
  rw [mul_sum]
  symm
  apply sum_bij (fun k _ => D * k)
  · intro k member
    obtain ⟨lower, upper⟩ := mem_Icc.mp member
    have productUpper : k * D ≤ L := (Nat.le_div_iff_mul_le DPositive).mp upper
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos DPositive lower, by simpa [mul_comm] using productUpper⟩,
      dvd_mul_right D k⟩
  · intro k _ k' _ same
    exact Nat.eq_of_mul_eq_mul_left DPositive same
  · intro u member
    obtain ⟨inIcc, k, identity⟩ := mem_filter.mp member
    obtain ⟨lower, upper⟩ := mem_Icc.mp inIcc
    have productLower : 0 < D * k := identity ▸ lower
    have productUpper : k * D ≤ L := by simpa [identity, Nat.mul_comm] using upper
    refine ⟨k, mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left productLower,
      (Nat.le_div_iff_mul_le DPositive).mpr productUpper⟩, identity.symm⟩
  · intro k member
    have kPositive : 0 < k := (mem_Icc.mp member).1
    have kNonzero : (k : ℝ) ≠ 0 := by exact_mod_cast kPositive.ne'
    have DNonzero : (D : ℝ) ≠ 0 := by exact_mod_cast DPositive.ne'
    rw [Nat.cast_mul]
    field_simp

end DyadicMixedB4GcdHarmonic

end

section

open Finset DyadicMixedB4GcdHarmonic

namespace DyadicMixedB4WeightBudgets

end DyadicMixedB4WeightBudgets

end

section

open Finset MeasureTheory ArithmeticFunction BombieriVinogradov.LargeSieve
open DyadicMixedB4FixedBlock DyadicMixedB4PrimitiveAt DyadicMixedB4PrimitiveExpansion
open DyadicMixedB4PrimitiveEnergy DyadicMixedB4RamanujanCharacters
open DyadicMixedB4MaximalSieve DyadicMixedB4MixedCharacter DyadicMixedB4WeightBudgets
open DyadicMixedB4ArcGeometry DyadicMixedB4KernelControl
open DyadicMixedB4BilinearEnergy

namespace DyadicMixedB4BilinearBlock

noncomputable section

end
end DyadicMixedB4BilinearBlock

end

section

open Finset

namespace DyadicMixedB4ModulusTail

end DyadicMixedB4ModulusTail

end

section

open Finset DyadicMixedB4ModulusTail DyadicMixedB4WeightBudgets

namespace DyadicMixedB4ModulusAggregate

noncomputable section

end
end DyadicMixedB4ModulusAggregate

end

section

open Finset DyadicMixedB4ArcGeometry DyadicMixedB4BilinearBlock DyadicMixedB4BilinearEnergy
open DyadicMixedB4ModulusAggregate

namespace DyadicMixedB4BlockModulus

noncomputable section

end
end DyadicMixedB4BlockModulus

end

section

namespace DyadicMixedB4DyadicCost

end DyadicMixedB4DyadicCost

end

section

open Finset DyadicMixedB4BilinearEnergy DyadicMixedB4DyadicCost
open DyadicMixedB4MaximalSieve DyadicMixedB4PrimitiveEnergy

namespace DyadicMixedB4EnergyTail

noncomputable section

def logBudget (n : ℕ) : ℝ := 1 + Real.log ((n : ℝ) + 2)

theorem one_le_logBudget (n : ℕ) : 1 ≤ logBudget n :=
  le_add_of_nonneg_right (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))

end
end DyadicMixedB4EnergyTail

end

section

open Filter Topology DyadicMixedB4ArcGeometry

namespace DyadicMixedB4Scale

noncomputable section

def cutoffU (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊
def cofactorCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (111 / 256 : ℝ)⌋₊
def maximumStep (n : ℕ) : ℕ := cutoffU n * cofactorCap n
theorem floor_half_le {x : ℝ} (xLower : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  by_cases small : x ≤ 2
  · have floorLower : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.le_floor (n := 1) (by simpa using xLower))
    linarith only [small, floorLower]
  · have floorBound := Nat.lt_floor_add_one x
    linarith only [floorBound, lt_of_not_ge small]

/-- The logarithm comparison adapts the corresponding estimate in
goldbach-proofs PR #2468, revision 3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/
theorem log2_le_four_log (n : ℕ) (hn : 2 ≤ n) : (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log n := by
  have hb := Real.natLog_le_logb (n + 2) 2
  rw [Real.logb] at hb
  push_cast at hb
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hx : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have square : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have logarithm := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) square
  rw [Real.log_pow] at logarithm
  norm_num at logarithm
  have divided := (le_div_iff₀ (by linarith : 0 < Real.log 2)).mp hb
  have multiplied := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.log 2 (n + 2)) : (0 : ℝ) ≤ _)
  linarith only [logarithm, divided, multiplied]

end
end DyadicMixedB4Scale

end

section

open DyadicMixedB4EnergyTail DyadicMixedB4Scale

namespace DyadicMixedB4TailScale

noncomputable section

theorem log_le_logBudget {m n : ℕ} (mPositive : 0 < m) (upper : m ≤ n) :
    Real.log m ≤ logBudget n := by
  have mReal : (0 : ℝ) < m := by exact_mod_cast mPositive
  have mUpper : (m : ℝ) ≤ n := by exact_mod_cast upper
  exact (Real.log_le_log mReal (by linarith)).trans (le_add_of_nonneg_left zero_le_one)

theorem natLog_succ_le {m n : ℕ} (nLower : 2 ≤ n) (mBound : m ≤ n) :
    (Nat.log 2 m : ℝ) + 1 ≤ 5 * logBudget n := by
  have hlog := log2_le_four_log n nLower
  have hmono : (Nat.log 2 m : ℝ) ≤ Nat.log 2 (n + 2) := by
    exact_mod_cast Nat.log_mono_right (mBound.trans (Nat.le_add_right n 2))
  have hle := log_le_logBudget (by omega : 0 < n) (le_refl n)
  linarith only [hlog, hmono, hle, one_le_logBudget n]

end
end DyadicMixedB4TailScale

end

section

open Finset

namespace DyadicMixedB4GcdSeries

noncomputable section

end
end DyadicMixedB4GcdSeries

end

section

open Finset

namespace DyadicMixedB4DyadicPartition

end DyadicMixedB4DyadicPartition

end

section

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open DyadicMixedB4DyadicPartition DyadicMixedB4GcdSeries DyadicMixedB4BilinearEnergy

namespace DyadicMixedB4TailAggregate

noncomputable section

end
end DyadicMixedB4TailAggregate

end

section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace DyadicMixedB4Arithmetic

end DyadicMixedB4Arithmetic

end

section

open Finset MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters

namespace DyadicMixedB4ArcDecomposition

noncomputable section

end
end DyadicMixedB4ArcDecomposition

end

section

open Finset ArithmeticFunction DyadicMixedB4Arithmetic DyadicMixedB4Scale
open DyadicMixedB4ArcDecomposition DyadicMixedB4Geometric DyadicMixedB4MoebiusGauss
open scoped ArithmeticFunction.Moebius

namespace DyadicMixedB4HighAtoms

noncomputable section

end
end DyadicMixedB4HighAtoms

end

section

open Finset ArithmeticFunction DyadicMixedB4Arithmetic
open scoped ArithmeticFunction.Moebius

namespace DyadicMixedB4LowBand

noncomputable section

end
end DyadicMixedB4LowBand

end

section

open Finset MeasureTheory DyadicMixedB4Geometric

namespace DyadicMixedB4OffWaveMoment

noncomputable section

end
end DyadicMixedB4OffWaveMoment

end

section

open MeasureTheory

namespace DyadicMixedB4YoungIntegral

end DyadicMixedB4YoungIntegral

end

section

open Finset MeasureTheory DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4ArcDecomposition

namespace DyadicMixedB4PairIntegral

noncomputable section

def lowCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

end
end DyadicMixedB4PairIntegral

end

section

open Finset MeasureTheory DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4ProgressionApprox DyadicMixedB4WindowKernel DyadicMixedB4KernelControl DyadicMixedB4Ramanujan

namespace DyadicMixedB4NearReplacement

noncomputable section

end
end DyadicMixedB4NearReplacement

end

section

open Finset ArithmeticFunction DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4PairIntegral
open DyadicMixedB4KernelControl DyadicMixedB4NearReplacement

namespace DyadicMixedB4NearPair

noncomputable section

end
end DyadicMixedB4NearPair

end

section

open Finset ArithmeticFunction DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4PairIntegral
open DyadicMixedB4KernelControl DyadicMixedB4NearPair DyadicMixedB4PrimitiveAt

namespace DyadicMixedB4PrimitiveNearPair

noncomputable section

end
end DyadicMixedB4PrimitiveNearPair

end

section

open Finset DyadicMixedB4Scale DyadicMixedB4ArcGeometry
open DyadicMixedB4BilinearEnergy DyadicMixedB4BilinearBlock DyadicMixedB4BlockModulus
open DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4PairIntegral DyadicMixedB4PrimitiveNearPair
open DyadicMixedB4ModulusAggregate DyadicMixedB4DyadicPartition DyadicMixedB4GcdSeries
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4TailAggregate

namespace DyadicMixedB4NearMain

noncomputable section

end
end DyadicMixedB4NearMain

end

section

open DyadicMixedB4Scale DyadicMixedB4ArcGeometry DyadicMixedB4EnergyTail
open DyadicMixedB4PairIntegral DyadicMixedB4TailScale

namespace DyadicMixedB4NumericBudgets

noncomputable section

end
end DyadicMixedB4NumericBudgets

end

section

open Finset Filter

namespace DyadicMixedB4DivisorGrowth

noncomputable section

/-- Adapted from goldbach-proofs PR #2468, revision
3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/
theorem divisorPower (K : ℕ) (hK : 0<K) :
    ∃ C : ℝ,1≤C ∧ ∀ n : ℕ, 0<n → (n.divisors.card:ℝ)^K ≤ C*n := by
  have hl := (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) K (by norm_num : (1:ℝ)<2)).bound (by norm_num : (0:ℝ)<1)
  obtain ⟨E,hE⟩ := eventually_atTop.mp hl
  let c : ℝ := (2:ℝ)^K*((E:ℝ)+1)^K
  have hc : 1≤c := by
    dsimp [c]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E]))
  have small (e : ℕ) : ((e:ℝ)+1)^K ≤ c*(2:ℝ)^e := by
    by_cases he : e<E
    · have hle : ((e:ℝ)+1)^K ≤ ((E:ℝ)+1)^K := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show e+1≤E+1 by omega)) _
      have h2 : (1:ℝ)≤2^K := one_le_pow₀ (by norm_num)
      have h3 : (1:ℝ)≤2^e := one_le_pow₀ (by norm_num)
      exact hle.trans ((le_mul_of_one_le_left (by positivity) h2).trans (le_mul_of_one_le_right (by positivity) h3))
    · have hs := hE (e+1) (by omega)
      simp only [Function.comp_apply,Real.norm_eq_abs,Nat.cast_add,Nat.cast_one,abs_of_nonneg (pow_nonneg (by positivity : 0≤(e:ℝ)+1) K),abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) (e+1)),one_mul,pow_succ] at hs
      rw [abs_of_nonneg (by positivity)] at hs
      have hK1 : (2:ℝ)≤2^K := by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hK)
      have hE1 : (1:ℝ)≤((E:ℝ)+1)^K := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E])
      have hc2 : (2:ℝ)≤c := hK1.trans (le_mul_of_one_le_right (by positivity) hE1)
      exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_right hc2 (by positivity : 0≤(2:ℝ)^e)])
  let P : ℕ := 2^K
  refine ⟨c^P,one_le_pow₀ hc,?_⟩
  intro n hn
  have hprod : (∏ p ∈ n.primeFactors,(p:ℝ)^(n.factorization p))=n := by
    exact_mod_cast (by simpa [Finsupp.prod,Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn.ne' :
      (∏ p ∈ n.primeFactors,p^(n.factorization p))=n)
  have hlocal (p : ℕ) (hp : p∈n.primeFactors) :
      ((n.factorization p:ℝ)+1)^K ≤ (if p<P then c else 1)*(p:ℝ)^(n.factorization p) := by
    have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with h
    · exact (small _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h2 _) (by linarith))
    · rw [one_mul]
      have he : ∀ e : ℕ,(e:ℝ)+1 ≤ (2:ℝ)^e := by
        intro e; induction e with
        | zero => norm_num
        | succ e ih => push_cast; rw [pow_succ]; linarith [show (0:ℝ)≤e by positivity]
      calc
        _ ≤ ((2:ℝ)^n.factorization p)^K := pow_le_pow_left₀ (by positivity) (he _) _
        _ = ((2:ℝ)^K)^n.factorization p := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show 2^K≤p by omega)) _
  have hcount : ((n.primeFactors.filter (·<P)).card)≤P := by
    have : n.primeFactors.filter (·<P)⊆range P := fun _ h => mem_range.mpr (mem_filter.mp h).2
    simpa using card_le_card this
  have hfactor : (∏ p ∈ n.primeFactors, if p<P then c else 1)≤c^P := by
    rw [←prod_filter,prod_const]; exact pow_le_pow_right₀ hc hcount
  rw [Nat.card_divisors hn.ne',Nat.cast_prod,←prod_pow]
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (if p<P then c else 1)*(p:ℝ)^(n.factorization p) :=
      prod_le_prod₀ (fun _ _ => by positivity) hlocal
    _ ≤ _ := by rw [prod_mul_distrib,hprod]; exact mul_le_mul_of_nonneg_right hfactor (by positivity)


end
end DyadicMixedB4DivisorGrowth

end

section

open Filter Topology DyadicMixedB4NumericBudgets DyadicMixedB4DivisorGrowth DyadicMixedB4EnergyTail

namespace DyadicMixedB4FinalGrowth

noncomputable section

end
end DyadicMixedB4FinalGrowth

end

section

open Filter Finset DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand
open DyadicMixedB4PairIntegral DyadicMixedB4NearPair DyadicMixedB4PrimitiveNearPair DyadicMixedB4NearMain
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4GcdSeries
open DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth

namespace DyadicMixedB4Finish

noncomputable section

end
end DyadicMixedB4Finish

end

end
end
end
end GoldbachTypeII13

namespace GoldbachTypeII13

open Finset MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Arithmetic DyadicMixedB4Scale DyadicMixedB4HighAtoms
open DyadicMixedB4PairIntegral DyadicMixedB4Finish

noncomputable section

def saving (f : ℕ → ℂ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖f n‖ ≤ e * (n : ℝ)

end

end GoldbachTypeII13

namespace GoldbachTypeII13

open Finset MeasureTheory ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4LowBand
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open DyadicMixedB4YoungIntegral DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth

noncomputable section

end

end GoldbachTypeII13

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Arithmetic DyadicMixedB4Scale DyadicMixedB4ArcDecomposition DyadicMixedB4Geometric

noncomputable section

end

end GoldbachTypeII13

namespace GoldbachTypeII13

open Finset MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4PairIntegral DyadicMixedB4Finish

noncomputable section

end

end GoldbachTypeII13

namespace GoldbachTypeII13

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Fourier
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4PairIntegral

noncomputable section

end

end GoldbachTypeII13


namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Geometric DyadicMixedB4ArcCenters

noncomputable section

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4HighAtoms
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale

open MeasureTheory Filter
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition DyadicMixedB4LowBand
open DyadicMixedB4YoungIntegral DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth

open Asymptotics Topology DyadicMixedB4DivisorGrowth

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_right_cofactor -/
section

namespace GoldbachTypeII13

open Finset Filter
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4ArcDecomposition DyadicMixedB4TailScale
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def rightLargeCofactorCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (33 / 64 : ℝ)⌋₊

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_left_type_one -/
section

namespace GoldbachTypeII13

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4EnergyTail
open DyadicMixedB4ArcGeometry DyadicMixedB4OffWaveMoment DyadicMixedB4YoungIntegral
open DyadicMixedB4ArcDecomposition DyadicMixedB4PairIntegral
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

noncomputable section

def truncateArithmetic (f : ArithmeticFunction ℝ) (H : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m ≤ H then f m else 0, by simp⟩

theorem vaughan_identity_real (P Q : ℕ) :
    let M := (μ : ArithmeticFunction ℝ)
    let u := truncateArithmetic M P
    let v := truncateArithmetic vonMangoldt Q
    u * ArithmeticFunction.log - (u * v) * ζ + v +
      ((M - u) * (vonMangoldt - v)) * ζ = vonMangoldt := by
  let M := (μ : ArithmeticFunction ℝ)
  let u := truncateArithmetic M P
  let v := truncateArithmetic vonMangoldt Q
  let Z := (ζ : ArithmeticFunction ℝ)
  change u * ArithmeticFunction.log - (u * v) * Z + v +
    ((M - u) * (vonMangoldt - v)) * Z = vonMangoldt
  rw [← ArithmeticFunction.vonMangoldt_mul_zeta]
  change u * (vonMangoldt * Z) - (u * v) * Z + v +
    ((M - u) * (vonMangoldt - v)) * Z = vonMangoldt
  have inv : M * Z = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  calc
    _ = (M * Z) * vonMangoldt + (1 - M * Z) * v := by ring
    _ = _ := by rw [inv]; simp

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_left_zeta -/
section

namespace GoldbachTypeII13

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcDecomposition DyadicMixedB4Scale DyadicMixedB4ArcGeometry
open DyadicMixedB4Arithmetic DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4MoebiusGauss
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def leftBandMoebius (n a : ℕ) : ℝ :=
  ∑ d ∈ a.divisors.filter (fun d => cutoffU n < d), (μ d : ℝ)

theorem norm_leftBandMoebius_le (n a : ℕ) :
    ‖(leftBandMoebius n a : ℂ)‖ ≤ a.divisors.card := by
  unfold leftBandMoebius
  rw [Complex.ofReal_sum]
  calc
    _ ≤ ∑ d ∈ a.divisors.filter (fun d => cutoffU n < d), ‖((μ d : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ a.divisors.filter (fun d => cutoffU n < d), (1 : ℝ) := by
      refine sum_le_sum fun d _ => ?_
      simpa [moebiusComplex] using norm_moebiusComplex_le_one d
    _ = ((a.divisors.filter (fun d => cutoffU n < d)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast card_le_card (filter_subset _ _)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_abel_log_wave -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4Geometric
open scoped Classical

noncomputable section

def clippedLog (r j : ℕ) : ℝ := if j ≤ r then Real.log j else 0

def logWaveStep (r j : ℕ) : ℝ := clippedLog r j - clippedLog r (j + 1)

private theorem telescoping_Ico {G : Type*} [AddCommGroup G] {a b : ℕ}
    (ord : a ≤ b) (f : ℕ → G) :
    (∑ j ∈ Ico a b, (f (j + 1) - f j)) = f b - f a := by
  rw [sum_Ico_eq_sum_range]
  have addBack : a + (b - a) = b := Nat.add_sub_of_le ord
  simpa only [Nat.add_assoc, addBack, Nat.add_zero] using sum_range_sub (fun j => f (a + j)) (b - a)

theorem log_wave_prefix_weights_le (l r : ℕ) :
    (∑ j ∈ Ioc l r, ‖(logWaveStep r j : ℂ)‖) ≤ 2 * Real.log r := by
  by_cases h : l < r
  · have I : Ioc l r = Ico (l+1) (r+1) := by
      ext j
      simp only [mem_Ioc, mem_Ico]
      omega
    have out : ¬ r+1 ≤ r := by omega
    have last : ‖(logWaveStep r r : ℂ)‖ = Real.log r := by
      unfold logWaveStep
      rw [Complex.norm_real, Real.norm_eq_abs]
      have rr : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
      simp [clippedLog, out, abs_of_nonneg (Real.log_nonneg rr)]
    rw [I, sum_Ico_succ_top (show l+1 ≤ r by omega), last]
    have older : (∑ j ∈ Ico (l+1) r, ‖(logWaveStep r j : ℂ)‖) =
        ∑ j ∈ Ico (l+1) r, (Real.log (j+1 : ℕ) - Real.log j) := by
      refine sum_congr rfl fun j hj => ?_
      obtain ⟨lo,up⟩ := mem_Ico.mp hj
      have jPos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      have jSucc : j+1 ≤ r := up
      have monotone : Real.log j ≤ Real.log (j+1 : ℕ) :=
        Real.log_le_log jPos (by exact_mod_cast Nat.le_succ j)
      unfold logWaveStep
      rw [Complex.norm_real, Real.norm_eq_abs]
      simp only [clippedLog, up.le, jSucc, ite_true]
      exact (abs_of_nonpos (sub_nonpos.mpr monotone)).trans (by ring)
    rw [older, telescoping_Ico (show l+1 ≤ r by omega) (fun j => Real.log (j : ℝ))]
    have nonneg : 0 ≤ Real.log (l+1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ l+1 by omega))
    linarith only [nonneg]
  · have empty : Ioc l r = ∅ := by
      ext j
      simp [mem_Ioc]
      omega
    rw [empty, sum_empty]
    cases r with
    | zero => simp
    | succ r =>
      exact mul_nonneg (by norm_num)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ r.succ by omega)))


end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_vaughan_zeta -/
section

namespace GoldbachTypeII13

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail
open DyadicMixedB4MoebiusGauss DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def vaughanShortCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 96 : ℝ)⌋₊

theorem truncate_moebius_mangoldt_support {P S : ℕ} (pBound : P * P ≤ S) :
    ∀ s, S < s →
      ((truncateArithmetic (μ : ArithmeticFunction ℝ) P * truncateArithmetic vonMangoldt P :
        ArithmeticFunction ℝ) s) = 0 := by
  intro s hs
  rw [ArithmeticFunction.mul_apply]
  refine sum_eq_zero fun i hi => ?_
  have eq := (Nat.mem_divisorsAntidiagonal.mp hi).1
  by_cases left : i.1 ≤ P
  · have right : ¬ i.2 ≤ P := by
      intro upper
      have prod := Nat.mul_le_mul left upper
      rw [eq] at prod
      exact (not_lt_of_ge (prod.trans pBound)) hs
    change truncateArithmetic (μ : ArithmeticFunction ℝ) P i.1 * truncateArithmetic vonMangoldt P i.2 = 0
    simp [truncateArithmetic, right]
  · change truncateArithmetic (μ : ArithmeticFunction ℝ) P i.1 * truncateArithmetic vonMangoldt P i.2 = 0
    simp [truncateArithmetic,left]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_bilateral_short -/
section

namespace GoldbachTypeII13

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4PairIntegral
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4MoebiusGauss
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

theorem norm_convolution_apply_le {n m : ℕ} (hm : m ≤ n) (f g : ArithmeticFunction ℝ)
    {T F G : ℝ} (F0 : 0 ≤ F) (G0 : 0 ≤ G) (hT : (m.divisors.card : ℝ) ≤ T)
    (fBound : ∀ x ≤ n, ‖(f x : ℂ)‖ ≤ F) (gBound : ∀ x ≤ n, ‖(g x : ℂ)‖ ≤ G) :
    ‖((f*g) m : ℂ)‖ ≤ T * (F * G) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => f x * g y), Complex.ofReal_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ m.divisors, F * G := by
      refine sum_le_sum fun x hx => ?_
      have xBound := (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hx).2)
        (Nat.dvd_of_mem_divisors hx)).trans hm
      rw [Complex.ofReal_mul, norm_mul]
      exact mul_le_mul (fBound x xBound) (gBound _ ((Nat.div_le_self m x).trans hm)) (norm_nonneg _) F0
    _ = (m.divisors.card : ℝ) * (F * G) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hT (mul_nonneg F0 G0)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_left_medium_waves -/
section

namespace GoldbachTypeII13

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4EnergyTail
open DyadicMixedB4ArcGeometry DyadicMixedB4OffWaveMoment DyadicMixedB4YoungIntegral
open DyadicMixedB4ArcDecomposition DyadicMixedB4PairIntegral
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

noncomputable section

def leftMediumCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (3 / 10 : ℝ)⌋₊

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_left_bilinear_short -/
section

namespace GoldbachTypeII13

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4PairIntegral
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4MoebiusGauss
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def leftBilinearItems (n : ℕ) : Finset (ℕ × ℕ) := Ioc (cutoffU n) (lowCut n) ×ˢ Icc 1 n

def leftBilinearStep (i : ℕ × ℕ) : ℕ := i.1 * i.2

def leftLargeBilinearItems (n : ℕ) : Finset (ℕ × ℕ) :=
  (leftBilinearItems n).filter (fun i => leftMediumCap n < leftBilinearStep i)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_right_bilinear_waves -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Arithmetic DyadicMixedB4Scale DyadicMixedB4ArcDecomposition DyadicMixedB4Geometric
open DyadicMixedB4HighAtoms DyadicMixedB4MoebiusGauss DyadicMixedB4TailScale DyadicMixedB4EnergyTail
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

abbrev RightLowWaveIndex := Σ _ : ℕ, ℕ

def rightLowWaveItems (n : ℕ) : Finset RightLowWaveIndex :=
  (Ioc (cutoffU n) (min n (rightLargeCofactorCut n))).sigma fun b =>
    Icc 1 (min (cutoffU n) (n/b))

def rightLowWaveStep (i : RightLowWaveIndex) : ℕ := i.2 * i.1

def rightLowWaveWeight (i : RightLowWaveIndex) : ℂ := -(μ i.2 : ℂ) * (vonMangoldt i.1 : ℂ)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_joint_actual_waves -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4ArcDecomposition
open DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4MoebiusGauss
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def bilateralLeftWaveItems (n : ℕ) : Finset (ℕ × ℕ) :=
  (leftLargeBilinearItems n).filter (fun i => leftBilinearStep i ≤ n)

theorem bilateral_left_step_range {n : ℕ} {i : ℕ × ℕ} (hi : i ∈ bilateralLeftWaveItems n) :
    leftBilinearStep i ∈ Icc 1 n :=
  mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (mem_filter.mp (mem_filter.mp hi).1).2, (mem_filter.mp hi).2⟩

theorem bilateral_right_low_step_range {n : ℕ} {i : RightLowWaveIndex} (hi : i ∈ rightLowWaveItems n) :
    rightLowWaveStep i ∈ Icc 1 n := by
  obtain ⟨hb,hd⟩ := mem_sigma.mp hi
  have bp : 0 < i.1 := (Nat.zero_le _).trans_lt (mem_Ioc.mp hb).1
  obtain ⟨dp,du⟩ := mem_Icc.mp hd
  exact mem_Icc.mpr ⟨Nat.mul_pos dp bp,
    (Nat.le_div_iff_mul_le bp).mp (du.trans (min_le_right ..))⟩

private theorem norm_mass_le_of_card_le {α : Type*} (S : Finset α) (c : α → ℂ)
    {A B : ℝ} (cardBound : (S.card : ℝ) ≤ A) (B0 : 0 ≤ B) (wt : ∀ i ∈ S, ‖c i‖ ≤ B) :
    (∑ i ∈ S, ‖c i‖) ≤ A*B := by
  calc
    _ ≤ ∑ _ ∈ S, B := sum_le_sum wt
    _ = (S.card : ℝ)*B := by rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right cardBound B0

theorem norm_bilateral_left_step_mass_from_pointwise {n : ℕ} {T : ℝ} (T0 : 0 ≤ T)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (w : ℕ × ℕ → ℂ)
    (pointwise : ∀ i ∈ bilateralLeftWaveItems n, ‖w i‖ ≤ T * (T * logBudget n))
    (u : ℕ) (hu : u ∈ Icc 1 n) :
    (∑ i ∈ (bilateralLeftWaveItems n).filter (fun i => leftBilinearStep i = u),
      ‖w i‖) ≤ T^3 * logBudget n := by
  let selected := (bilateralLeftWaveItems n).filter (fun i => leftBilinearStep i = u)
  have up : 0 < u := (mem_Icc.mp hu).1
  have count : selected.card ≤ u.divisors.card := by
    apply card_le_card_of_injOn (Prod.fst : ℕ × ℕ → ℕ)
    · intro i hi
      have hi' : i ∈ selected := hi
      exact Nat.mem_divisors.mpr ⟨⟨i.2, (mem_filter.mp hi').2.symm⟩, up.ne'⟩
    · intro i hi j hj first
      have iSel : i ∈ selected := hi
      have jSel : j ∈ selected := hj
      have stepEq : i.1*i.2 = j.1*j.2 := (mem_filter.mp iSel).2.trans (mem_filter.mp jSel).2.symm
      have pair := (mem_filter.mp iSel).1
      have left := (mem_product.mp (mem_filter.mp (mem_filter.mp pair).1).1).1
      apply Prod.ext first
      change i.1 = j.1 at first
      rw [← first] at stepEq
      exact Nat.eq_of_mul_eq_mul_left ((Nat.zero_le _).trans_lt (mem_Ioc.mp left).1) stepEq
  have cn : (selected.card : ℝ) ≤ T :=
    (show (selected.card : ℝ) ≤ u.divisors.card by exact_mod_cast count).trans (divisorBound u (mem_Icc.mp hu).2)
  refine (norm_mass_le_of_card_le selected w cn
    (mul_nonneg T0 (mul_nonneg T0 (zero_le_one.trans (one_le_logBudget n)))) ?_).trans_eq (by ring)
  exact fun i hi => pointwise i (mem_filter.mp hi).1

theorem norm_bilateral_right_low_step_mass {n : ℕ} {T : ℝ} (T1 : 1 ≤ T)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (u : ℕ) (hu : u ∈ Icc 1 n) :
    (∑ i ∈ (rightLowWaveItems n).filter (fun i => rightLowWaveStep i = u), ‖rightLowWaveWeight i‖) ≤
      T^3 * logBudget n := by
  let selected := (rightLowWaveItems n).filter (fun i => rightLowWaveStep i = u)
  have up : 0 < u := (mem_Icc.mp hu).1
  have count : selected.card ≤ u.divisors.card := by
    apply card_le_card_of_injOn Sigma.fst
    · intro i hi
      have hi' : i ∈ selected := hi
      have eq : i.2*i.1 = u := (mem_filter.mp hi').2
      exact Nat.mem_divisors.mpr ⟨⟨i.2, eq.symm.trans (Nat.mul_comm _ _)⟩, up.ne'⟩
    · intro i hi j hj first
      have ii : i ∈ selected := hi
      have jj : j ∈ selected := hj
      have eq := (mem_filter.mp ii).2.trans (mem_filter.mp jj).2.symm
      have hp : 0 < i.1 := (Nat.zero_le _).trans_lt (mem_Ioc.mp (mem_sigma.mp (mem_filter.mp ii).1).1).1
      rcases i with ⟨b,d⟩
      rcases j with ⟨c,e⟩
      change b = c at first
      subst c
      change d*b = e*b at eq
      have same := Nat.eq_of_mul_eq_mul_right hp eq
      simp [same]
  have cn : (selected.card : ℝ) ≤ T :=
    (show (selected.card : ℝ) ≤ u.divisors.card by exact_mod_cast count).trans (divisorBound u (mem_Icc.mp hu).2)
  have L0 := zero_le_one.trans (one_le_logBudget n)
  refine (norm_mass_le_of_card_le selected rightLowWaveWeight cn L0 ?_).trans
    (mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ T1 (by decide : 1 ≤ 3)) L0)
  intro i hi
  have hb := (mem_Ioc.mp (mem_sigma.mp (mem_filter.mp hi).1).1)
  have bpos : 0 < i.1 := (Nat.zero_le _).trans_lt hb.1
  have nBound := hb.2.trans (min_le_left _ _)
  have lambdaBound : ‖(vonMangoldt i.1 : ℂ)‖ ≤ logBudget n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact vonMangoldt_le_log.trans (log_le_logBudget bpos nBound)
  rw [rightLowWaveWeight, norm_mul, norm_neg]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (by simpa [moebiusComplex] using norm_moebiusComplex_le_one i.2)).trans lambdaBound

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_joint_product_limit -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4DivisorGrowth
open scoped Classical

noncomputable section

private theorem divisor_envelope_for_product (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
    (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / (k : ℝ) : ℝ) := by
  obtain ⟨C, CLower, estimate⟩ := divisorPower k hk
  let p : ℝ := 1 / (k : ℝ)
  have CNonnegative : 0 ≤ C := zero_le_one.trans CLower
  refine ⟨C ^ p, Real.one_le_rpow CLower (by unfold p; positivity), fun n m upper => ?_⟩
  by_cases mPositive : 0 < m
  · have mReal : (m : ℝ) ≤ n := by exact_mod_cast upper
    have standard := (estimate m mPositive).trans (mul_le_mul_of_nonneg_left mReal CNonnegative)
    have powered := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg m.divisors.card) k) standard
      (show 0 ≤ p by dsimp [p]; positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m.divisors.card),
      Real.mul_rpow CNonnegative (Nat.cast_nonneg n)] at powered
    have kReal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have kp : (k : ℝ) * p = 1 := by unfold p; field_simp
    rw [kp, Real.rpow_one] at powered
    exact powered
  · have mZero : m = 0 := by omega
    subst m
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    positivity

private theorem eventually_log_budget_le_for_product (p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, logBudget n ≤ (n : ℝ) ^ p := by
  have limit : Tendsto (fun n : ℕ => Real.log n / (n : ℝ) ^ p) atTop (𝓝 0) := by
    have realLimit := (isLittleO_log_rpow_rpow_atTop (1 : ℕ)
      hp).tendsto_div_nhds_zero
    simpa only [Real.rpow_one, Nat.cast_one, Function.comp_def] using
      realLimit.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2, limit.eventually_lt_const (show (0 : ℝ) < 1 / 4 by norm_num)] with n hn small
  have nLower : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have nPositive : (0 : ℝ) < n := by linarith only [nLower]
  have logTwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) nLower
  have big : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith only [nLower])
      (show 0 ≤ (n : ℝ) + 1 by positivity)]
  have logSquare := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) big
  rw [Real.log_pow] at logSquare
  norm_num at logSquare
  have logBound : logBudget n ≤ 4 * Real.log n := by
    unfold logBudget
    linarith only [logSquare, logTwo, Real.log_two_gt_d9]
  have divided := (div_lt_iff₀ (Real.rpow_pos_of_pos nPositive _)).mp small
  exact logBound.trans (by linarith only [divided])

end

theorem divisor_envelope_at_power (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
    (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / (k : ℝ) : ℝ) :=
  divisor_envelope_for_product k hk

theorem eventually_log_budget_le_power (p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, logBudget n ≤ (n : ℝ) ^ p :=
  eventually_log_budget_le_for_product p hp

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_long_lattice -/
section

namespace GoldbachTypeII13

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open DyadicMixedB4Fourier DyadicMixedB4ArcDecomposition DyadicMixedB4OffWaveMoment
open DyadicMixedB4Scale
open scoped Classical

noncomputable section

def progressionPairSolutions (n u v l r p s : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc l r ×ˢ Ioc p s).filter (fun i => u*i.1 + v*i.2 = n)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_residue_count -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

private theorem card_residue_Ioc (a b z m : ℤ) (hm : 0 < m) :
    ((Ioc a b).filter (fun x => x ≡ z [ZMOD m])).card =
      ((b-z)/m - (a-z)/m).toNat := by
  let R := (Ioc a b).filter (fun x => x ≡ z [ZMOD m])
  let I := Ioc ((a-z)/m) ((b-z)/m)
  have member (j : ℤ) : z + m*j ∈ R ↔ j ∈ I := by
    have cong : z + m*j ≡ z [ZMOD m] := Int.modEq_iff_dvd.mpr ⟨-j, by ring⟩
    simp only [R,I,mem_filter,mem_Ioc,cong,and_true]
    rw [Int.ediv_lt_iff_lt_mul hm, Int.le_ediv_iff_mul_le hm, mul_comm j m]
    omega
  have eq : I.card = R.card := by
    apply card_bij (fun j _ => z + m*j)
    · intro j hj
      exact (member j).mpr hj
    · intro i _ j _ same
      apply mul_left_cancel₀ hm.ne'
      exact add_left_cancel same
    · intro x hx
      obtain ⟨j, eq⟩ := Int.modEq_iff_dvd.mp (mem_filter.mp hx).2
      have repr : z + m*(-j) = x := by rw [mul_neg]; omega
      exact ⟨-j, (member (-j)).mp (repr.symm ▸ hx), repr⟩
  exact eq.symm.trans (Int.card_Ioc ..)

theorem card_residue_in_integer_interval (a b z m : ℤ) (hm : 0 < m) :
    ((Ioc a b).filter (fun x => x ≡ z [ZMOD m])).card =
      ((b-z)/m - (a-z)/m).toNat :=
  card_residue_Ioc a b z m hm

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_residue_fourier -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Geometric
open scoped ZMod Classical

noncomputable section

def residueRamp (m : ℕ) [NeZero m] (x : ZMod m) : ℂ := (x.val : ℂ)/(m : ℂ)

theorem residue_ramp_difference_fourier (m : ℕ) [NeZero m] (a b z : ℤ) :
    (((((a-z) % (m : ℤ) : ℤ)) : ℂ) - ((((b-z) % (m : ℤ) : ℤ)) : ℂ))/(m : ℂ) =
      ∑ k ∈ (univ : Finset (ZMod m)).filter (fun k => k ≠ 0),
        ZMod.stdAddChar (-(k*(z : ZMod m))) *
          ((ZMod.stdAddChar (k*(a : ZMod m)) - ZMod.stdAddChar (k*(b : ZMod m))) *
            ((m : ℂ)⁻¹ * (ZMod.dft (residueRamp m) k))) := by
  let F := residueRamp m
  let H := ZMod.dft F
  have invert (x : ZMod m) : F x = (m : ℂ)⁻¹ * ∑ k : ZMod m, ZMod.stdAddChar (k*x)*H k := by
    calc
      _ = (ZMod.dft.symm H) x := congrFun (ZMod.dft.symm_apply_apply F).symm x
      _ = _ := by rw [ZMod.invDFT_apply]; rfl
  have cast (r : ℤ) : ((r : ZMod m).val : ℂ) = ((r % (m : ℤ) : ℤ) : ℂ) := by
    exact_mod_cast ZMod.val_intCast (n := m) r
  have val (r : ℤ) : ((r % (m : ℤ) : ℤ) : ℂ)/(m : ℂ) = F (r : ZMod m) := by
    unfold F residueRamp
    rw [cast r]
  rw [sub_div, val (a-z), val (b-z), invert, invert, ← mul_sub, ← sum_sub_distrib, mul_sum, sum_filter]
  apply sum_congr rfl
  intro k _
  by_cases zero : k = 0
  · subst k
    simp
  · have step (q : ℤ) : ZMod.stdAddChar (k*((q-z : ℤ) : ZMod m)) =
        ZMod.stdAddChar (k*(q : ZMod m))*ZMod.stdAddChar (-(k*(z : ZMod m))) := by
      rw [Int.cast_sub, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    rw [ite_eq_left zero, step a, step b]
    change _ = ZMod.stdAddChar (-(k*(z : ZMod m))) *
      ((ZMod.stdAddChar (k*(a : ZMod m)) - ZMod.stdAddChar (k*(b : ZMod m))) * ((m : ℂ)⁻¹ * H k))
    ring

theorem dft_residue_ramp_of_ne_zero (m : ℕ) [NeZero m] (hm : 1 < m)
    (k : ZMod m) (hk : k ≠ 0) :
    ZMod.dft (residueRamp m) k = ZMod.stdAddChar k / (1-ZMod.stdAddChar k) := by
  let F := residueRamp m
  let e := (ZMod.stdAddChar : AddChar (ZMod m) ℂ)
  let H := ZMod.dft F k
  have oneVal : (1 : ZMod m).val = 1 := ZMod.val_one'' (by omega)
  have castM : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have diff (x : ZMod m) : F (x+1)-F x =
      (m : ℂ)⁻¹ - if x = -1 then 1 else 0 := by
    have lt := ZMod.val_lt x
    rw [show F (x+1)-F x = (((x+1).val : ℂ)-(x.val : ℂ))/(m : ℂ) by unfold F residueRamp; ring]
    by_cases b : x.val+1 < m
    · have val : (x+1).val = x.val+1 := by rw [ZMod.val_add,oneVal,Nat.mod_eq_of_lt b]
      have ne : x ≠ -1 := by
        intro eq
        have zero : x+1 = 0 := by simp [eq]
        rw [zero,ZMod.val_zero] at val
        omega
      rw [ite_eq_right ne,val]
      push_cast
      ring
    · have eq : x.val+1=m := by omega
      have val : (x+1).val = 0 := by rw [ZMod.val_add,oneVal,eq,Nat.mod_self]
      have neg : x = -1 := by
        have zero := (ZMod.val_eq_zero (x+1)).mp val
        exact eq_neg_of_add_eq_zero_left zero
      have lift : (x.val : ℂ)+1=(m : ℂ) := by
        simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun j : ℕ => (j : ℂ)) eq
      rw [ite_eq_left neg,val,Nat.cast_zero]
      apply (div_eq_iff castM).mpr
      rw [sub_mul,inv_mul_cancel₀ castM,one_mul]
      linear_combination -lift
  have translate : ZMod.dft (fun x : ZMod m => F (x+1)) k = e k*H := by
    simp only [H, ZMod.dft_apply, smul_eq_mul, e, mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod m))
      (fun x => ZMod.stdAddChar (-(x*k))*F (x+1))
      (fun x => ZMod.stdAddChar k*(ZMod.stdAddChar (-(x*k))*F x)) (fun x => ?_)
    have rotate : (Equiv.addRight (1 : ZMod m)) x = x+1 := rfl
    rw [rotate]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    have index : -(x*k) = k + -((x+1)*k) := by
      rw [add_mul,one_mul,neg_add,← add_assoc,add_comm k (-(x*k)),add_assoc,add_neg_cancel,add_zero]
    rw [index]
  have charSum : ∑ x : ZMod m, e (-(x*k)) = 0 := by
    have zero := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar m (a := -k) (neg_ne_zero.mpr hk))
    simpa only [e,AddChar.mulShift_apply,neg_mul,mul_comm k] using zero
  have spectrum : e k*H-H = -e k := by
    calc
      _ = ZMod.dft (fun x : ZMod m => F (x+1)-F x) k := by
        rw [← translate]
        simp only [ZMod.dft_apply,smul_eq_mul,mul_sub,sum_sub_distrib,H]
      _ = ∑ x : ZMod m, e (-(x*k))*((m : ℂ)⁻¹ - if x = -1 then 1 else 0) := by
        simp only [ZMod.dft_apply,smul_eq_mul,diff,e]
      _ = _ := by
        simp only [mul_sub,sum_sub_distrib,← sum_mul,charSum,zero_mul,zero_sub,mul_ite,mul_zero,mul_one]
        rw [sum_ite_eq', ite_eq_left (mem_univ _)]
        simp
  have ne : (1 : ℂ)-e k ≠ 0 := by
    intro zero
    have h : e k = e 0 := by rw [AddChar.map_zero_eq_one]; exact (sub_eq_zero.mp zero).symm
    exact hk (ZMod.injective_stdAddChar h)
  apply (eq_div_iff ne).mpr
  change H*(1-e k) = e k
  linear_combination -spectrum

theorem norm_residue_fourier_coefficient_le (m : ℕ) [NeZero m] (k : ZMod m) (hk : k ≠ 0) :
    ‖(m : ℂ)⁻¹ * ZMod.dft (residueRamp m) k‖ ≤
      1/(4*(min k.val (m-k.val) : ℕ)) := by
  have kp := ZMod.val_pos.mpr hk
  have km := ZMod.val_lt k
  have hm : 1 < m := by omega
  have mp : (0 : ℝ) < m := by exact_mod_cast (zero_lt_one.trans hm)
  let x := (k.val : ℝ)/m
  let y := min x (1-x)
  have xmin : 0 ≤ x := by unfold x; positivity
  have xmax : x ≤ 1 := (div_le_one mp).mpr (by exact_mod_cast km.le)
  have ymin : 0 ≤ y := le_min xmin (sub_nonneg.mpr xmax)
  have ymax : y ≤ 1/2 := by
    have a : y ≤ x := min_le_left _ _
    have b : y ≤ 1-x := min_le_right _ _
    linarith only [a,b]
  have choice : y = (min k.val (m-k.val) : ℕ)/(m : ℝ) := by
    have sub : (1 : ℝ)-x = ((m : ℝ)-(k.val : ℝ))/(m : ℝ) := by
      unfold x
      rw [sub_div,div_self mp.ne']
    unfold y
    rw [sub,Nat.cast_min,Nat.cast_sub km.le,← min_div_div_right mp.le]
  have sines : Real.sin (Real.pi*x) = Real.sin (Real.pi*y) := by
    by_cases side : x ≤ 1-x
    · rw [show y = x from min_eq_left side]
    · rw [show y = 1-x from min_eq_right (le_of_not_ge side),mul_sub,mul_one,Real.sin_pi_sub]
  have lB : 2*y ≤ Real.sin (Real.pi*y) := by
    have pi := Real.pi_pos
    calc
      _ = 2/Real.pi*(Real.pi*y) := by field_simp
      _ ≤ _ := Real.mul_le_sin (mul_nonneg pi.le ymin) (by nlinarith only [ymax,pi])
  have phaseEq : ZMod.stdAddChar k = phase x := by
    rw [ZMod.stdAddChar_apply,ZMod.toCircle_apply]
    unfold phase x
    push_cast
    congr 1
    ring
  have chord : ‖(1 : ℂ)-ZMod.stdAddChar k‖ = 2*|Real.sin (Real.pi*x)| := by
    rw [norm_sub_rev,phaseEq,phase,mul_comm]
    exact norm_exp_phase_sub_one x
  have lower : 4*(min k.val (m-k.val) : ℕ) ≤ (m : ℝ)*‖(1 : ℂ)-ZMod.stdAddChar k‖ := by
    have four : 4*y ≤ ‖(1 : ℂ)-ZMod.stdAddChar k‖ := by
      rw [chord, sines]
      linarith only [lB,le_abs_self (Real.sin (Real.pi*y))]
    have scaled := mul_le_mul_of_nonneg_left four mp.le
    rw [choice] at scaled
    have eq : (m : ℝ)*(4*((min k.val (m-k.val) : ℕ)/(m : ℝ))) = 4*(min k.val (m-k.val) : ℕ) := by
      field_simp
    rwa [eq] at scaled
  have minPos : 0 < min k.val (m-k.val) := lt_min kp (Nat.sub_pos_of_lt km)
  rw [dft_residue_ramp_of_ne_zero m hm k hk,norm_mul,norm_inv,norm_div,Complex.norm_natCast,
    show ‖ZMod.stdAddChar k‖=1 by rw [phaseEq,norm_phase']]
  calc
    _ = 1/((m : ℝ)*‖(1 : ℂ)-ZMod.stdAddChar k‖) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left zero_le_one
      (mul_pos (by norm_num) (by exact_mod_cast minPos)) lower

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_interval_residue_fourier -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical ZMod

noncomputable section

def intIntervalResidueCount (p : ℕ) (a b : ℤ) (x : ZMod p) : ℕ :=
  #((Ioc a b).filter fun (j : ℤ) => (j : ZMod p) = x)

def intIntervalFourierCoefficient (p : ℕ) [NeZero p] (a b : ℤ) (h : ZMod p) : ℂ :=
  (ZMod.stdAddChar (h*(a : ZMod p))-ZMod.stdAddChar (h*(b : ZMod p))) *
    ((p : ℂ)⁻¹ * ZMod.dft (residueRamp p) h)

theorem int_interval_residue_count_fourier (p : ℕ) [NeZero p] {a b : ℤ}
    (hab : a ≤ b) (z : ZMod p) :
    (intIntervalResidueCount p a b z : ℂ) =
      ((b-a : ℤ) : ℂ)/(p : ℂ) +
        ∑ h ∈ (univ : Finset (ZMod p)).filter (fun h => h ≠ 0),
          ZMod.stdAddChar (-(h*z))*intIntervalFourierCoefficient p a b h := by
  have pNat : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have pInt : (0 : ℤ) < p := by exact_mod_cast pNat
  have pC : (p : ℂ) ≠ 0 := by exact_mod_cast pNat.ne'
  let t : ℤ := z.val
  have tCast : (t : ZMod p) = z := by
    dsimp [t]
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have eq : intIntervalResidueCount p a b z =
      ((Ioc a b).filter fun j => j ≡ t [ZMOD (p : ℤ)]).card := by
    unfold intIntervalResidueCount
    apply congrArg Finset.card
    ext j
    simp only [mem_filter]
    rw [← tCast, ZMod.intCast_eq_intCast_iff]
  rw [eq, card_residue_in_integer_interval a b t p pInt]
  have hdiff : 0 ≤ (b-t)/(p : ℤ)-(a-t)/(p : ℤ) := by
    exact sub_nonneg.mpr (Int.ediv_le_ediv (by omega) (by omega))
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hdiff]
  have recast (s : ℤ) :
      (((s / (p : ℤ) : ℤ)) : ℂ) = ((s : ℂ)-(((s % (p : ℤ) : ℤ)) : ℂ))/(p : ℂ) := by
    apply (eq_div_iff pC).mpr
    have eq := congrArg (fun y : ℤ => (y : ℂ)) (Int.emod_add_mul_ediv s p)
    push_cast at eq
    linear_combination eq
  calc
    _ = ((b-a : ℤ) : ℂ)/(p : ℂ) +
        ((((a-t) % (p : ℤ) : ℤ) : ℂ)-(((b-t) % (p : ℤ) : ℤ) : ℂ))/(p : ℂ) := by
      rw [Int.cast_sub, recast (b-t), recast (a-t)]
      push_cast
      ring
    _ = _ := by rw [residue_ramp_difference_fourier, tCast]; rfl

theorem norm_stdAddChar_eq_one (p : ℕ) [NeZero p] (z : ZMod p) :
    ‖ZMod.stdAddChar z‖ = 1 := by rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

private theorem inv_min_val_le (p : ℕ) [NeZero p] {h : ZMod p} (hh : h ≠ 0) :
    1/(2*(min h.val (p-h.val) : ℕ) : ℝ) ≤
      (1/2 : ℝ)*(1/(h.val : ℝ) + 1/((-h).val : ℝ)) := by
  let : NeZero h := ⟨hh⟩
  rw [ZMod.val_neg_of_ne_zero]
  by_cases hd : h.val ≤ p-h.val
  · rw [min_eq_left hd]
    calc
      _ = (1/2 : ℝ)*(1/(h.val : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by norm_num)
  · rw [min_eq_right (by omega)]
    calc
      _ = (1/2 : ℝ)*(1/((p-h.val : ℕ) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by norm_num)

theorem norm_int_interval_fourier_coefficient_le (p : ℕ) [NeZero p] (a b : ℤ)
    {h : ZMod p} (hh : h ≠ 0) :
    ‖intIntervalFourierCoefficient p a b h‖ ≤ 1/(2*(min h.val (p-h.val) : ℕ) : ℝ) := by
  unfold intIntervalFourierCoefficient
  rw [norm_mul]
  have w := norm_sub_le (ZMod.stdAddChar (h*(a : ZMod p))) (ZMod.stdAddChar (h*(b : ZMod p)))
  rw [norm_stdAddChar_eq_one, norm_stdAddChar_eq_one] at w
  calc
    _ ≤ 2*(1/(4*(min h.val (p-h.val) : ℕ) : ℝ)) :=
      mul_le_mul (w.trans_eq (by norm_num)) (norm_residue_fourier_coefficient_le p h hh)
        (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem sum_inv_min_val_le (p : ℕ) [NeZero p] :
    ∑ h ∈ (univ : Finset (ZMod p)).filter (fun h => h ≠ 0),
      (1/(2*(min h.val (p-h.val) : ℕ) : ℝ)) ≤ 1+Real.log p := by
  let H := (univ : Finset (ZMod p)).filter fun h => h ≠ 0
  have valPos {x : ZMod p} (hx : x ∈ H) := ZMod.val_pos.mpr (mem_filter.mp hx).2
  have negPerm : ∑ h ∈ H, 1/((-h).val : ℝ) = ∑ h ∈ H, 1/(h.val : ℝ) := by
    refine sum_bij (fun h _ => -h) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro h hh
      exact mem_filter.mpr ⟨mem_univ _, neg_ne_zero.mpr (mem_filter.mp hh).2⟩
    · intro i _ j _ heq
      exact neg_injective heq
    · intro h hh
      exact ⟨-h, mem_filter.mpr ⟨mem_univ _, neg_ne_zero.mpr (mem_filter.mp hh).2⟩, neg_neg _⟩
  have divs : ∑ h ∈ H, 1/(h.val : ℝ) ≤ (harmonic p : ℝ) := by
    have injective : Set.InjOn (fun (h : ZMod p) => h.val-1) H := by
      intro x hx y hy eq
      apply ZMod.val_injective p
      have xp := valPos hx
      have yp := valPos hy
      change x.val-1 = y.val-1 at eq
      omega
    have incl : (H.image fun h => h.val-1) ⊆ range p := by
      intro i hi
      obtain ⟨h,_,rfl⟩ := mem_image.mp hi
      exact mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _) (ZMod.val_lt h))
    have eq (h : ZMod p) (hh : h ∈ H) :
        1/(h.val : ℝ) = (((h.val-1+1 : ℕ) : ℝ))⁻¹ := by
      rw [Nat.sub_add_cancel (valPos hh), one_div]
    calc
      _ = ∑ h ∈ H, (((h.val-1+1 : ℕ) : ℝ))⁻¹ := sum_congr rfl eq
      _ = ∑ i ∈ H.image (fun h => h.val-1), (((i+1 : ℕ) : ℝ))⁻¹ := by
        rw [sum_image (fun x hx y hy h => injective hx hy h)]
      _ ≤ ∑ i ∈ range p, (((i+1 : ℕ) : ℝ))⁻¹ :=
        sum_le_sum_of_subset_of_nonneg incl (fun _ _ _ => by positivity)
      _ = _ := by unfold harmonic; push_cast; rfl
  change ∑ h ∈ H, (1/(2*(min h.val (p-h.val) : ℕ) : ℝ)) ≤ _
  calc
    _ ≤ ∑ h ∈ H, (1/2 : ℝ)*(1/(h.val : ℝ) + 1/((-h).val : ℝ)) :=
      sum_le_sum fun h hh =>
        inv_min_val_le p (mem_filter.mp hh).2
    _ = ∑ h ∈ H, 1/(h.val : ℝ) := by rw [← mul_sum, sum_add_distrib, negPerm]; ring
    _ ≤ _ := divs.trans (by exact_mod_cast harmonic_le_one_add_log p)

theorem sum_norm_int_interval_fourier_coefficient_le (p : ℕ) [NeZero p] (a b : ℤ) :
    ∑ h ∈ (univ : Finset (ZMod p)).filter (fun h => h ≠ 0),
      ‖intIntervalFourierCoefficient p a b h‖ ≤ 1+Real.log p := by
  exact (sum_le_sum fun h hh => norm_int_interval_fourier_coefficient_le p a b (mem_filter.mp hh).2).trans
    (sum_inv_min_val_le p)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_bilinear_inverse_prime_factor -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical ComplexConjugate

noncomputable section

def intIntervalModUnits (m : ℕ) (a b : ℤ) : Finset ℤ :=
  (Ioc a b).filter (fun (j : ℤ) => IsUnit (j : ZMod m))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_reciprocal_interval -/
section

namespace GoldbachTypeII13

open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped Classical

noncomputable section

def weilReciprocalBudget (m : ℕ) : ℝ :=
  (3+2*Real.log m)*(m.divisors.card : ℝ)*Real.sqrt m

theorem weil_reciprocal_budget_nonneg {m : ℕ} (m0 : 0 < m) : 0 ≤ weilReciprocalBudget m := by
  have log0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m from m0))
  unfold weilReciprocalBudget
  positivity

theorem norm_modular_unit_inverse_interval_le_weil {m : ℕ} [NeZero m]
    (z : ZMod m) {a b : ℤ} (span : b-a ≤ m) :
    ‖∑ j ∈ intIntervalModUnits m a b, ZMod.stdAddChar (z*(j : ZMod m)⁻¹)‖ ≤
      weilReciprocalBudget m*Real.sqrt (m.gcd z.val) := by
  have m0 : 0 < m := NeZero.pos m
  have mi : (0 : ℤ) < m := by exact_mod_cast m0
  by_cases ordered : a ≤ b
  · let L := (b-a).toNat
    have Lcast : (L : ℤ) = b-a := Int.toNat_of_nonneg (sub_nonneg.mpr ordered)
    have Lm : L ≤ m := by
      have h : (L : ℤ) ≤ (m : ℤ) := by rw [Lcast]; exact span
      exact_mod_cast h
    let φ : ℕ ↪ ℤ := ⟨fun k => a+1+(k : ℤ),fun x y e => by dsimp at e; omega⟩
    have indices : (range L).map φ = Ioc a b := by
      ext j
      constructor
      · intro mem
        obtain ⟨k,hk,eq⟩ := mem_map.mp mem
        have up : (k : ℤ) < (L : ℤ) := by exact_mod_cast mem_range.mp hk
        change a+1+(k : ℤ)=j at eq
        rw [Lcast] at up
        exact mem_Ioc.mpr ⟨by omega,by omega⟩
      · intro mem
        obtain ⟨left,right⟩ := mem_Ioc.mp mem
        let k := (j-a-1).toNat
        have eq : (k : ℤ)=j-a-1 := Int.toNat_of_nonneg (by omega)
        have lt : (k : ℤ) < (L : ℤ) := by rw [eq,Lcast]; omega
        refine mem_map.mpr ⟨k,mem_range.mpr (by exact_mod_cast lt),?_⟩
        change a+1+(k : ℤ)=j
        omega
    have same : (∑ j ∈ intIntervalModUnits m a b, ZMod.stdAddChar (z*(j : ZMod m)⁻¹)) =
        incompleteReciprocal m (z.val : ℤ) (a+1) L := by
      unfold intIntervalModUnits incompleteReciprocal
      rw [sum_filter,← indices,sum_map]
      refine sum_congr rfl fun k _ => ?_
      have cast : ((φ k : ℤ) : ZMod m) = ((a+1 : ℤ) : ZMod m)+(k : ZMod m) := by
        change ((a+1+(k : ℤ) : ℤ) : ZMod m) = _
        rw [Int.cast_add,Int.cast_natCast]
      by_cases h : IsUnit ((φ k : ℤ) : ZMod m)
      · rw [if_pos h,reciprocalPhase,if_pos (cast ▸ h),Int.cast_natCast,ZMod.natCast_zmod_val,cast]
      · rw [if_neg h,reciprocalPhase,if_neg (fun hz => h (cast.symm ▸ hz))]
    rw [same]
    let B := (m.divisors.card : ℝ)*Real.sqrt (m.gcd z.val)*Real.sqrt m
    have allFreq (k : ZMod m) : ‖completeKloosterman m k (z.val : ℤ)‖ ≤ B := by
      refine (completeKloosterman_weil_zmod m k (z.val : ℤ)).trans ?_
      have div : m.gcd (k.val.gcd ((z.val : ℤ)).natAbs) ∣ m.gcd z.val := by
        rw [Int.natAbs_natCast]
        exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
      have hle : m.gcd (k.val.gcd ((z.val : ℤ)).natAbs) ≤ m.gcd z.val :=
        Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ m0) div
      unfold B
      gcongr
    exact (incompleteReciprocal_norm_le_log (z.val : ℤ) (a+1) L Lm B allFreq).trans_eq
      (by unfold B weilReciprocalBudget; ring)
  · have empty : intIntervalModUnits m a b = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      have h : j ∈ Ioc a b ∧ IsUnit (j : ZMod m) := by
        simpa only [intIntervalModUnits,mem_filter] using hj
      exact ordered ((mem_Ioc.mp h.1).1.le.trans (mem_Ioc.mp h.1).2)
    simp only [empty,sum_empty,norm_zero]
    exact mul_nonneg (weil_reciprocal_budget_nonneg m0) (Real.sqrt_nonneg _)

theorem gcd_unit_inverse_difference_le {m : ℕ} [NeZero m] (c : ZMod m)
    {a b : ℕ} (ac : a.Coprime m) (bc : b.Coprime m) :
    m.gcd (c*((a : ZMod m)⁻¹-(b : ZMod m)⁻¹)).val ≤
      m.gcd c.val * m.gcd (((b : ℤ)-(a : ℤ)).natAbs) := by
  let z := c*((a : ZMod m)⁻¹-(b : ZMod m)⁻¹)
  let d := m.gcd z.val
  let f := ZMod.castHom (Nat.gcd_dvd_left m z.val) (ZMod d)
  have zero : f z=0 := by
    rw [← ZMod.natCast_zmod_val z,map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.gcd_dvd_right _ _)
  have multiply : ((a : ZMod m)*(b : ZMod m))*z = c*((b : ZMod m)-(a : ZMod m)) := by
    calc
      _ = c*((b : ZMod m)*((a : ZMod m)*(a : ZMod m)⁻¹)-
             (a : ZMod m)*((b : ZMod m)*(b : ZMod m)⁻¹)) := by unfold z; ring
      _ = _ := by rw [ZMod.coe_mul_inv_eq_one _ ac,ZMod.coe_mul_inv_eq_one _ bc,mul_one,mul_one]
  have mapped : f (c*((b : ZMod m)-(a : ZMod m)))=0 := by
    rw [← multiply,map_mul,zero,mul_zero]
  have fv : f c = (c.val : ZMod d) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c, map_natCast]
  have castZero : ((((c.val : ℤ)*((b : ℤ)-(a : ℤ))) : ℤ) : ZMod d) = 0 := by
    rw [map_mul,map_sub,fv,map_natCast,map_natCast] at mapped
    push_cast
    exact mapped
  have divInt : (d : ℤ) ∣ (c.val : ℤ)*((b : ℤ)-(a : ℤ)) := by
    have h : ((((c.val : ℤ)*((b : ℤ)-(a : ℤ))) : ℤ) : ZMod d) = ((0 : ℤ) : ZMod d) := by
      simpa only [Int.cast_zero] using castZero
    have div := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ d).mp h
    simpa only [zero_sub,Int.dvd_neg] using div
  have divAbs := Int.dvd_natAbs.mpr divInt
  rw [Int.natAbs_mul,Int.natAbs_natCast] at divAbs
  have div : d ∣ c.val * (((b : ℤ)-(a : ℤ)).natAbs) := by exact_mod_cast divAbs
  let r := ((b : ℤ)-(a : ℤ)).natAbs
  have split : d ∣ d.gcd c.val*d.gcd r := by
    simpa only [Nat.gcd_comm] using (Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr div)
  have cmp (k : ℕ) : d.gcd k ∣ m.gcd k :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left d k).trans (Nat.gcd_dvd_left m z.val)) (Nat.gcd_dvd_right d k)
  have m0 := NeZero.pos m
  exact Nat.le_of_dvd (mul_pos (Nat.gcd_pos_of_pos_left _ m0) (Nat.gcd_pos_of_pos_left _ m0))
    (split.trans (Nat.mul_dvd_mul (cmp c.val) (cmp r)))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_difference_divisors -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

private theorem compare_abs_sub_right {a b : ℕ} (order : a ≤ b) :
    (((b : ℤ)-(a : ℤ)).natAbs) = b-a := by
  rw [← Int.ofNat_sub order,Int.natAbs_natCast]

private theorem compare_abs_sub_left {a b : ℕ} (order : b ≤ a) :
    (((b : ℤ)-(a : ℤ)).natAbs) = a-b := by
  rw [← Int.natAbs_neg,neg_sub]
  exact compare_abs_sub_right order

private theorem card_other_divisible_le {A d i : ℕ} (d0 : 0 < d) {I : Finset ℕ}
    (base : I ⊆ Icc 1 A) (hi : i ∈ I) :
    #((I.erase i).filter (fun (t : ℕ) => d ∣ (((t : ℤ)-(i : ℤ)).natAbs))) ≤ 2*(A/d) := by
  let S := (I.erase i).filter (fun (t : ℕ) => d ∣ (((t : ℤ)-(i : ℤ)).natAbs))
  let L := S.filter (fun t => i < t)
  let R := S.filter (fun t => ¬i < t)
  have iA : i ≤ A := (mem_Icc.mp (base hi)).2
  have rightInfo (t : ℕ) (ht : t ∈ L) : i < t ∧ t ≤ A ∧ d ∣ t-i := by
    obtain ⟨s,gt⟩ := mem_filter.mp ht
    obtain ⟨tmem,div⟩ := mem_filter.mp s
    exact ⟨gt,(mem_Icc.mp (base (mem_erase.mp tmem).2)).2,(compare_abs_sub_right gt.le) ▸ div⟩
  have leftInfo (t : ℕ) (ht : t ∈ R) : t < i ∧ d ∣ i-t := by
    obtain ⟨s,le⟩ := mem_filter.mp ht
    obtain ⟨mem,div⟩ := mem_filter.mp s
    have tlt : t < i := lt_of_le_of_ne (le_of_not_gt le) (mem_erase.mp mem).1
    exact ⟨tlt,(compare_abs_sub_left tlt.le) ▸ div⟩
  have rightCount : #L ≤ A/d := by
    rw [← show #(Icc 1 (A/d)) = A/d by simp [Nat.card_Icc]]
    apply card_le_card_of_injOn (fun t => (t-i)/d)
    · intro t ht
      obtain ⟨gt,up,dvd⟩ := rightInfo t ht
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt gt) dvd) d0,
        Nat.div_le_div_right ((Nat.sub_le _ _).trans up)⟩
    · intro a ha b hb eq
      obtain ⟨gtA,_,divA⟩ := rightInfo a ha
      obtain ⟨gtB,_,divB⟩ := rightInfo b hb
      have same : a-i=b-i := by simpa only [Nat.div_mul_cancel divA,Nat.div_mul_cancel divB] using congrArg (fun k => k*d) eq
      omega
  have leftCount : #R ≤ A/d := by
    rw [← show #(Icc 1 (A/d)) = A/d by simp [Nat.card_Icc]]
    apply card_le_card_of_injOn (fun t => (i-t)/d)
    · intro t ht
      obtain ⟨lt,dvd⟩ := leftInfo t ht
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt lt) dvd) d0,
        Nat.div_le_div_right ((Nat.sub_le _ _).trans iA)⟩
    · intro a ha b hb eq
      obtain ⟨ltA,divA⟩ := leftInfo a ha
      obtain ⟨ltB,divB⟩ := leftInfo b hb
      have same : i-a=i-b := by simpa only [Nat.div_mul_cancel divA,Nat.div_mul_cancel divB] using congrArg (fun k => k*d) eq
      omega
  change #S ≤ _
  have split : #L + #R = #S := card_filter_add_card_filter_not (fun t => i < t)
  omega

theorem sum_gcd_of_distinct_differences_le {m A i : ℕ} (m0 : 0 < m) {I : Finset ℕ}
    (base : I ⊆ Icc 1 A) (hi : i ∈ I) :
    (∑ t ∈ I.erase i, (m.gcd (((t : ℤ)-(i : ℤ)).natAbs) : ℝ)) ≤
      2*(A : ℝ)*(m.divisors.card : ℝ) := by
  let D (t : ℕ) := (((t : ℤ)-(i : ℤ)).natAbs)
  have term (t : ℕ) : (m.gcd (D t) : ℝ) ≤ ∑ d ∈ m.divisors,
      if d ∣ D t then (d : ℝ) else 0 := by
    let g := m.gcd (D t)
    have mem : g ∈ m.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,m0.ne'⟩
    have one := single_le_sum (f := fun d => if d ∣ D t then (d : ℝ) else 0)
      (fun d _ => by split_ifs <;> positivity) mem
    simpa only [if_pos (Nat.gcd_dvd_right m (D t)),g] using one
  have each (d : ℕ) (hd : d ∈ m.divisors) :
      (∑ t ∈ I.erase i, if d ∣ D t then (d : ℝ) else 0) ≤ 2*(A : ℝ) := by
    have d0 := Nat.pos_of_mem_divisors hd
    have dr : (0 : ℝ) < d := by exact_mod_cast d0
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    have count := card_other_divisible_le d0 base hi
    calc
      _ ≤ (2*((A/d : ℕ) : ℝ))*(d : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ dr.le
        dsimp only [D]
        exact_mod_cast count
      _ ≤ (2*((A : ℝ)/(d : ℝ)))*(d : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)) dr.le
      _ = _ := by field_simp
  calc
    _ ≤ ∑ t ∈ I.erase i, ∑ d ∈ m.divisors, if d ∣ D t then (d : ℝ) else 0 :=
      sum_le_sum fun t _ => term t
    _ = ∑ d ∈ m.divisors, ∑ t ∈ I.erase i, if d ∣ D t then (d : ℝ) else 0 := sum_comm
    _ ≤ ∑ _ ∈ m.divisors,2*(A : ℝ) := sum_le_sum each
    _ = _ := by rw [sum_const,nsmul_eq_mul]; ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weighted_bilinear_correlation -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical ComplexConjugate

noncomputable section

theorem norm_weighted_bilinear_correlation_sq_le_with_cost {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (α : ι → ℂ) (β : κ → ℂ) (f : ι → κ → ℂ)
    (K : ι → ι → ℝ) (K0 : ∀ i t, 0 ≤ K i t)
    (diag : ∀ i ∈ I, ‖∑ j ∈ J, f i j*conj (f i j)‖ ≤ #J)
    (off : ∀ i ∈ I, ∀ t ∈ I, i ≠ t → ‖∑ j ∈ J, f i j*conj (f t j)‖ ≤ K i t) :
    ‖∑ j ∈ J, β j * ∑ i ∈ I, α i*f i j‖^2 ≤
      (∑ j ∈ J, ‖β j‖^2) *
        ((#J : ℝ)*(∑ i ∈ I, ‖α i‖^2)+(∑ i ∈ I, ∑ t ∈ I, K i t*(‖α i‖*‖α t‖))) := by
  let Z (i t : ι) := ∑ j ∈ J, f i j*conj (f t j)
  have single (j : κ) :
      ((‖∑ i ∈ I, α i*f i j‖^2 : ℝ) : ℂ) =
        ∑ i ∈ I, ∑ t ∈ I, (α i*conj (α t))*(f i j*conj (f t j)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun t _ => ?_
    rw [map_mul]
    ring
  have expansion :
      (↑(∑ j ∈ J, ‖∑ i ∈ I, α i*f i j‖^2 : ℝ) : ℂ) =
        ∑ i ∈ I, ∑ t ∈ I, α i*conj (α t)*Z i t := by
    change Complex.ofRealHom (∑ j ∈ J, ‖∑ i ∈ I, α i*f i j‖^2) = _
    rw [map_sum]
    change (∑ j ∈ J, ((‖∑ i ∈ I, α i*f i j‖^2 : ℝ) : ℂ)) = _
    simp only [single]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    unfold Z
    rw [mul_sum]
  have point (i t : ι) (hi : i ∈ I) (ht : t ∈ I) :
      ‖α i*conj (α t)*Z i t‖ ≤
        (if i = t then (#J : ℝ)*‖α i‖^2 else 0)+K i t*(‖α i‖*‖α t‖) := by
    simp only [norm_mul,Complex.norm_conj]
    by_cases h : i = t
    · subst t
      rw [ite_eq_left rfl]
      calc
        _ ≤ (‖α i‖*‖α i‖)*(#J : ℝ) := mul_le_mul_of_nonneg_left (diag i hi) (by positivity)
        _ = (#J : ℝ)*‖α i‖^2 := by ring
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (K0 i i) (by positivity))
    · rw [ite_eq_right h,zero_add,mul_comm (K i t)]
      exact mul_le_mul_of_nonneg_left (off i hi t ht h) (by positivity)
  have energy :
      ∑ j ∈ J, ‖∑ i ∈ I, α i*f i j‖^2 ≤
        (#J : ℝ)*(∑ i ∈ I, ‖α i‖^2)+(∑ i ∈ I, ∑ t ∈ I, K i t*(‖α i‖*‖α t‖)) := by
    have sum0 : 0 ≤ ∑ j ∈ J, ‖∑ i ∈ I, α i*f i j‖^2 := by positivity
    calc
      _ = ‖(↑(∑ j ∈ J, ‖∑ i ∈ I, α i*f i j‖^2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg sum0]
      _ = ‖∑ i ∈ I, ∑ t ∈ I, α i*conj (α t)*Z i t‖ := by rw [expansion]
      _ ≤ ∑ i ∈ I, ∑ t ∈ I, ‖α i*conj (α t)*Z i t‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
      _ ≤ ∑ i ∈ I, ∑ t ∈ I,
          ((if i = t then (#J : ℝ)*‖α i‖^2 else 0)+K i t*(‖α i‖*‖α t‖)) :=
        sum_le_sum fun i hi => sum_le_sum fun t ht => point i t hi ht
      _ = _ := by
        simp only [sum_add_distrib]
        apply congrArg₂ (·+·) _ rfl
        rw [mul_sum]
        exact sum_congr rfl fun i hi => by rw [sum_ite_eq,ite_eq_left hi]
  have N : ‖∑ j ∈ J, β j*(∑ i ∈ I, α i*f i j)‖ ≤ ∑ j ∈ J, ‖β j‖*‖∑ i ∈ I, α i*f i j‖ := by
    simpa only [norm_mul] using norm_sum_le J (fun j => β j*(∑ i ∈ I, α i*f i j))
  calc
    _ ≤ (∑ j ∈ J, ‖β j‖*‖∑ i ∈ I, α i*f i j‖)^2 := pow_le_pow_left₀ (norm_nonneg _) N 2
    _ ≤ (∑ j ∈ J, ‖β j‖^2)*(∑ j ∈ J, ‖∑ i ∈ I, α i*f i j‖^2) :=
      sum_mul_sq_le_sq_mul_sq J _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left energy (by positivity)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_symmetric_lattice_count -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

def positiveInverseResidue (n : ℤ) (u v : ℕ) : ℤ :=
  (n*Nat.gcdA u v-1)%(v : ℤ)+1

theorem positive_inverse_residue_bounds (n : ℤ) {u v : ℕ} (hv : 0 < v) :
    1 ≤ positiveInverseResidue n u v ∧ positiveInverseResidue n u v ≤ (v : ℤ) := by
  have vr : (0 : ℤ) < v := by exact_mod_cast hv
  have lo := Int.emod_nonneg (n*Nat.gcdA u v-1) vr.ne'
  have hi := Int.emod_lt_of_pos (n*Nat.gcdA u v-1) vr
  unfold positiveInverseResidue
  omega

private theorem positive_inverse_residue_modEq (n : ℤ) (u v : ℕ) :
    positiveInverseResidue n u v ≡ n*Nat.gcdA u v [ZMOD (v : ℤ)] := by
  have h := (Int.mod_modEq (n*Nat.gcdA u v-1) (v : ℤ)).add_right 1
  simpa only [positiveInverseResidue,sub_add_cancel] using h

private theorem mul_positive_inverse_residue_modEq (n : ℤ) {u v : ℕ} (cop : u.Coprime v) :
    (u : ℤ)*positiveInverseResidue n u v ≡ n [ZMOD (v : ℤ)] := by
  have bez : (u : ℤ)*Nat.gcdA u v ≡ 1 [ZMOD (v : ℤ)] := by
    simpa only [cop.gcd_eq_one,Nat.cast_one] using Int.gcd_a_modEq u v
  calc
    _ ≡ (u : ℤ)*(n*Nat.gcdA u v) [ZMOD (v : ℤ)] := (positive_inverse_residue_modEq n u v).mul_left _
    _ = ((u : ℤ)*Nat.gcdA u v)*n := by ring
    _ ≡ n [ZMOD (v : ℤ)] := by simpa only [one_mul] using bez.mul_right n

private theorem positive_coordinate_representation {n x : ℤ} {u v : ℕ} (hv : 0 < v)
    (cop : u.Coprime v) (hx : 0 < x) (eq : (u : ℤ)*x ≡ n [ZMOD (v : ℤ)]) :
    ∃ i : ℤ, 0 ≤ i ∧ x = positiveInverseResidue n u v+(v : ℤ)*i := by
  have vr : (0 : ℤ) < v := by exact_mod_cast hv
  have bez : (u : ℤ)*Nat.gcdA u v ≡ 1 [ZMOD (v : ℤ)] := by
    simpa only [cop.gcd_eq_one,Nat.cast_one] using Int.gcd_a_modEq u v
  have recovered : x ≡ n*Nat.gcdA u v [ZMOD (v : ℤ)] := by
    calc
      _ ≡ ((u : ℤ)*Nat.gcdA u v)*x [ZMOD (v : ℤ)] := by simpa only [one_mul] using (bez.mul_right x).symm
      _ = ((u : ℤ)*x)*Nat.gcdA u v := by ring
      _ ≡ _ [ZMOD (v : ℤ)] := eq.mul_right _
  have residues := recovered.sub (Int.ModEq.refl (n := (v : ℤ)) 1)
  change (x-1)%(v : ℤ) = (n*Nat.gcdA u v-1)%(v : ℤ) at residues
  refine ⟨(x-1)/(v : ℤ),Int.ediv_nonneg (by omega) vr.le,?_⟩
  rw [positiveInverseResidue,← residues]
  have h := Int.emod_add_mul_ediv (x-1) (v : ℤ)
  linarith only [h]

/-- Popoviciu's formula with both coordinates positive. -/
theorem positive_coprime_pair_count {n u v : ℕ} (hn : 0 < n)
    (hu : 0 < u) (hv : 0 < v) (cop : u.Coprime v) :
    ((progressionPairSolutions n u v 0 (n/u) 0 (n/v)).card : ℝ) =
      1+(n : ℝ)/((u : ℝ)*(v : ℝ))-
        (positiveInverseResidue n u v : ℝ)/(v : ℝ)-
        (positiveInverseResidue n v u : ℝ)/(u : ℝ) := by
  let U : ℤ := u
  let V : ℤ := v
  let X := positiveInverseResidue n u v
  let Y := positiveInverseResidue n v u
  let P := U*V
  let D := U*X+V*Y
  have u0 : 0 < U := by change (0 : ℤ) < (u : ℤ); exact_mod_cast hu
  have v0 : 0 < V := by change (0 : ℤ) < (v : ℤ); exact_mod_cast hv
  have p0 : 0 < P := mul_pos u0 v0
  have n0 : (0 : ℤ) < n := by exact_mod_cast hn
  obtain ⟨x1,xv⟩ : 1 ≤ X ∧ X ≤ V := positive_inverse_residue_bounds n hv
  obtain ⟨y1,yu⟩ : 1 ≤ Y ∧ Y ≤ U := positive_inverse_residue_bounds n hu
  have dx : U*X ≡ n [ZMOD V] := mul_positive_inverse_residue_modEq n cop
  have dy : V*Y ≡ n [ZMOD U] := mul_positive_inverse_residue_modEq n cop.symm
  have dzV : D ≡ n [ZMOD V] := by
    have h : V*Y ≡ 0 [ZMOD V] := Int.modEq_zero_iff_dvd.mpr (dvd_mul_right V Y)
    simpa only [D,add_zero] using dx.add h
  have dzU : D ≡ n [ZMOD U] := by
    have h : U*X ≡ 0 [ZMOD U] := Int.modEq_zero_iff_dvd.mpr (dvd_mul_right U X)
    simpa only [D,zero_add] using h.add dy
  have dos : P ∣ (n : ℤ)-D := cop.isCoprime.mul_dvd dzU.dvd dzV.dvd
  obtain ⟨K,hK⟩ := dos
  have eqN : (n : ℤ) = D+P*K := by linarith only [hK]
  have dTop : D ≤ 2*P := by
    calc
      _ ≤ U*V+V*U := add_le_add (mul_le_mul_of_nonneg_left xv u0.le) (mul_le_mul_of_nonneg_left yu v0.le)
      _ = _ := by unfold P; ring
  have K1 : 0 ≤ K+1 := by
    by_contra! neg
    have k : K ≤ -2 := by omega
    have mul := mul_le_mul_of_nonneg_left k p0.le
    linarith only [eqN,dTop,mul,n0]
  let indices := Icc (0 : ℤ) K
  let points := progressionPairSolutions n u v 0 (n/u) 0 (n/v)
  let f (i : ℤ) : ℕ × ℕ := ((X+V*i).toNat,(Y+U*(K-i)).toNat)
  have fVal (i : ℤ) (hi : i ∈ indices) :
      ((f i).1 : ℤ) = X+V*i ∧ ((f i).2 : ℤ) = Y+U*(K-i) := by
    obtain ⟨lo,up⟩ := mem_Icc.mp hi
    exact ⟨Int.toNat_of_nonneg (add_nonneg (by omega) (mul_nonneg v0.le lo)),
      Int.toNat_of_nonneg (add_nonneg (by omega) (mul_nonneg u0.le (sub_nonneg.mpr up)))⟩
  have card : indices.card = points.card := by
    apply card_bij (fun i _ => f i)
    · intro i hi
      obtain ⟨lo,up⟩ := mem_Icc.mp hi
      obtain ⟨fx,fy⟩ := fVal i hi
      have equation : U*((f i).1 : ℤ)+V*((f i).2 : ℤ) = n := by
        rw [fx,fy,eqN]
        unfold D P
        ring
      have eq : u*(f i).1+v*(f i).2=n := by
        change (u : ℤ)*((f i).1 : ℤ)+(v : ℤ)*((f i).2 : ℤ) = (n : ℤ) at equation
        exact_mod_cast equation
      have xp : (0 : ℤ) < ((f i).1 : ℤ) := by
        rw [fx]
        exact add_pos_of_pos_of_nonneg (by omega) (mul_nonneg v0.le lo)
      have yp : (0 : ℤ) < ((f i).2 : ℤ) := by
        rw [fy]
        exact add_pos_of_pos_of_nonneg (by omega) (mul_nonneg u0.le (sub_nonneg.mpr up))
      have xEnd : (f i).1 ≤ n/u := (Nat.le_div_iff_mul_le hu).mpr (by rw [mul_comm]; omega)
      have yEnd : (f i).2 ≤ n/v := (Nat.le_div_iff_mul_le hv).mpr (by rw [mul_comm]; omega)
      apply mem_filter.mpr
      exact ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨by exact_mod_cast xp,xEnd⟩,
        mem_Ioc.mpr ⟨by exact_mod_cast yp,yEnd⟩⟩,eq⟩
    · intro i hi j hj same
      have cast : ((f i).1 : ℤ) = ((f j).1 : ℤ) := by rw [same]
      rw [(fVal i hi).1,(fVal j hj).1] at cast
      exact mul_left_cancel₀ v0.ne' (add_left_cancel cast)
    · intro q hq
      obtain ⟨boxes,eq⟩ := mem_filter.mp hq
      obtain ⟨hqx,hqy⟩ := mem_product.mp boxes
      have qx : (0 : ℤ) < q.1 := by exact_mod_cast (mem_Ioc.mp hqx).1
      have qy : (0 : ℤ) < q.2 := by exact_mod_cast (mem_Ioc.mp hqy).1
      have equation : U*(q.1 : ℤ)+V*(q.2 : ℤ) = n := by
        change (u : ℤ)*(q.1 : ℤ)+(v : ℤ)*(q.2 : ℤ) = (n : ℤ)
        exact_mod_cast eq
      have mx : U*(q.1 : ℤ) ≡ n [ZMOD V] :=
        Int.modEq_iff_dvd.mpr ⟨(q.2 : ℤ),by linarith only [equation]⟩
      have my : V*(q.2 : ℤ) ≡ n [ZMOD U] :=
        Int.modEq_iff_dvd.mpr ⟨(q.1 : ℤ),by linarith only [equation]⟩
      obtain ⟨i,i0,ex⟩ := positive_coordinate_representation hv cop qx mx
      obtain ⟨j,j0,ey⟩ := positive_coordinate_representation hu cop.symm qy my
      change (q.1 : ℤ) = X+V*i at ex
      change (q.2 : ℤ) = Y+U*j at ey
      have total : i+j = K := by
        apply mul_left_cancel₀ p0.ne'
        have eq2 : D+P*(i+j) = n := by
          rw [← equation,ex,ey]
          unfold D P
          ring
        linarith only [eqN,eq2]
      have hi : i ∈ indices := mem_Icc.mpr ⟨i0,by omega⟩
      refine ⟨i,hi,Prod.ext ?_ ?_⟩
      · exact_mod_cast ((fVal i hi).1.trans ex.symm)
      · have rest : K-i=j := by omega
        have cast : ((f i).2 : ℤ) = (q.2 : ℤ) :=
          (fVal i hi).2.trans (by rw [rest,← ey])
        exact_mod_cast cast
  have count : points.card = (K+1).toNat := by
    rw [← card,Int.card_Icc,sub_zero]
  have countR : (points.card : ℝ) = ((K+1 : ℤ) : ℝ) := by
    rw [count]
    exact_mod_cast Int.toNat_of_nonneg K1
  have eqCast : (n : ℝ) = (u : ℝ)*(X : ℝ)+(v : ℝ)*(Y : ℝ)+(u : ℝ)*(v : ℝ)*(K : ℝ) := by
    unfold D P U V at eqN
    exact_mod_cast eqN
  change (points.card : ℝ) = 1+(n : ℝ)/((u : ℝ)*(v : ℝ))-(X : ℝ)/(v : ℝ)-(Y : ℝ)/(u : ℝ)
  rw [countR,Int.cast_add,Int.cast_one]
  have uR : (0 : ℝ) < u := by exact_mod_cast hu
  have vR : (0 : ℝ) < v := by exact_mod_cast hv
  field_simp
  nlinarith only [eqCast]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_shifted_lattice_count -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem mem_full_progression_pair_iff {n u v p : ℕ} {z : ℕ × ℕ}
    (hu : 0 < u) (hv : 0 < v) :
    z ∈ progressionPairSolutions n u v 0 (n/u) p (n/v) ↔
      0 < z.1 ∧ p < z.2 ∧ u*z.1+v*z.2=n := by
  unfold progressionPairSolutions
  rw [mem_filter,mem_product,mem_Ioc,mem_Ioc]
  constructor
  · exact fun h => ⟨h.1.1.1,h.1.2.1,h.2⟩
  · rintro ⟨x,y,eq⟩
    exact ⟨⟨⟨x,(Nat.le_div_iff_mul_le hu).mpr (by rw [mul_comm]; omega)⟩,
      ⟨y,(Nat.le_div_iff_mul_le hv).mpr (by rw [mul_comm]; omega)⟩⟩,eq⟩

theorem full_progression_pair_count_eq_shifted {n u v p : ℕ}
    (hu : 0 < u) (hv : 0 < v) (compatible : u.gcd v ∣ n) (threshold : v*p < n) :
    let d := u.gcd v
    let U := u/d
    let V := v/d
    let T := n/d-V*p
    (progressionPairSolutions n u v 0 (n/u) p (n/v)).card =
      (progressionPairSolutions T U V 0 (T/U) 0 (T/V)).card := by
  dsimp only
  let d := u.gcd v
  let U := u/d
  let V := v/d
  let T := n/d-V*p
  have d0 : 0 < d := Nat.gcd_pos_of_pos_left _ hu
  have Ud : U*d=u := Nat.div_mul_cancel (Nat.gcd_dvd_left u v)
  have Vd : V*d=v := Nat.div_mul_cancel (Nat.gcd_dvd_right u v)
  have nd : (n/d)*d=n := Nat.div_mul_cancel compatible
  have u0 : 0 < U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) d0
  have v0 : 0 < V := Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right u v)) d0
  have shift : V*p < n/d := by
    apply (Nat.mul_lt_mul_right d0).mp
    calc
      _ = (V*d)*p := by ring
      _ < n := by rw [Vd]; exact threshold
      _ = _ := nd.symm
  have tSum : T+V*p=n/d := Nat.sub_add_cancel shift.le
  have normalize (x y : ℕ) : u*x+v*y=n ↔ U*x+V*y=n/d := by
    constructor <;> intro h
    · apply Nat.eq_of_mul_eq_mul_right d0
      calc
        _ = (U*d)*x+(V*d)*y := by ring
        _ = n := by rw [Ud,Vd]; exact h
        _ = _ := nd.symm
    · calc
        _ = (U*x+V*y)*d := by rw [← Ud,← Vd]; ring
        _ = n := by rw [h,nd]
  apply card_bij (fun z _ => (z.1,z.2-p))
  · intro z hz
    obtain ⟨x,y,eq⟩ := (mem_full_progression_pair_iff hu hv).mp hz
    obtain hh := (normalize _ _).mp eq
    have eq' : U*z.1+V*(z.2-p)+V*p=n/d := by
      rw [add_assoc,← mul_add,Nat.sub_add_cancel y.le,hh]
    exact (mem_full_progression_pair_iff u0 v0).mpr
      ⟨x,Nat.sub_pos_of_lt y,Nat.add_right_cancel (eq'.trans tSum.symm)⟩
  · intro a ha b hb same
    have pA := ((mem_full_progression_pair_iff hu hv).mp ha).2.1
    have pB := ((mem_full_progression_pair_iff hu hv).mp hb).2.1
    have x := congrArg Prod.fst same
    have y := congrArg Prod.snd same
    change a.2-p=b.2-p at y
    exact Prod.ext x (by omega)
  · intro z hz
    obtain ⟨x,y,eq⟩ := (mem_full_progression_pair_iff u0 v0).mp hz
    have original : U*z.1+V*(z.2+p)=n/d := by
      rw [mul_add,← add_assoc,eq,tSum]
    refine ⟨(z.1,z.2+p),(mem_full_progression_pair_iff hu hv).mpr
      ⟨x,by omega,(normalize _ _).mpr original⟩,?_⟩
    exact Prod.ext rfl (Nat.add_sub_cancel _ _)

theorem positive_inverse_residue_sub_modulus (n : ℤ) (u v : ℕ) (p : ℤ) :
    positiveInverseResidue (n-(v : ℤ)*p) u v = positiveInverseResidue n u v := by
  have hm : n-(v : ℤ)*p ≡ n [ZMOD (v : ℤ)] := Int.modEq_iff_dvd.mpr ⟨p,by ring⟩
  have hx := (hm.mul_right (Nat.gcdA u v)).sub (Int.ModEq.refl (n := (v : ℤ)) 1)
  unfold positiveInverseResidue
  exact congrArg (fun x : ℤ => x+1) hx

theorem positive_inverse_residue_sub_step (n : ℤ) {u v : ℕ} (cop : u.Coprime v) (p : ℤ) :
    positiveInverseResidue (n-(u : ℤ)*p) u v = (n*Nat.gcdA u v-p-1)%(v : ℤ)+1 := by
  have bez : (u : ℤ)*Nat.gcdA u v ≡ 1 [ZMOD (v : ℤ)] := by
    simpa only [cop.gcd_eq_one,Nat.cast_one] using Int.gcd_a_modEq u v
  have fact : (u : ℤ)*p*Nat.gcdA u v ≡ p [ZMOD (v : ℤ)] := by
    rw [show (u : ℤ)*p*Nat.gcdA u v = ((u : ℤ)*Nat.gcdA u v)*p by ring]
    simpa only [one_mul] using bez.mul_right p
  have hc : (n-(u : ℤ)*p)*Nat.gcdA u v-1 ≡ n*Nat.gcdA u v-p-1 [ZMOD (v : ℤ)] := by
    rw [sub_mul]
    exact ((Int.ModEq.refl (n*Nat.gcdA u v)).sub fact).sub (Int.ModEq.refl 1)
  unfold positiveInverseResidue
  exact congrArg (fun x : ℤ => x+1) hc

theorem full_progression_pair_count_eq_symmetric {n u v p : ℕ}
    (hu : 0 < u) (hv : 0 < v) (compatible : u.gcd v ∣ n) (threshold : v*p < n) :
    let d := u.gcd v
    let U := u/d
    let V := v/d
    let T := (n/d : ℕ)
    ((progressionPairSolutions n u v 0 (n/u) p (n/v)).card : ℝ) =
      1+((T : ℝ)-(V : ℝ)*p)/((U : ℝ)*(V : ℝ))-
        (positiveInverseResidue T U V : ℝ)/(V : ℝ)-
        (((((T : ℤ)*Nat.gcdA V U-(p : ℤ)-1)%(U : ℤ)+1) : ℤ) : ℝ)/(U : ℝ) := by
  dsimp only
  let d := u.gcd v
  let U := u/d
  let V := v/d
  let T := n/d
  have d0 : 0 < d := Nat.gcd_pos_of_pos_left _ hu
  have Ud : U*d=u := Nat.div_mul_cancel (Nat.gcd_dvd_left u v)
  have Vd : V*d=v := Nat.div_mul_cancel (Nat.gcd_dvd_right u v)
  have nd : T*d=n := Nat.div_mul_cancel compatible
  have u0 : 0 < U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) d0
  have v0 : 0 < V := Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right u v)) d0
  have cop : U.Coprime V := Nat.coprime_div_gcd_div_gcd d0
  have shift : V*p < T := by
    apply (Nat.mul_lt_mul_right d0).mp
    calc
      _ = (V*d)*p := by ring
      _ < n := by rw [Vd]; exact threshold
      _ = _ := nd.symm
  rw [full_progression_pair_count_eq_shifted hu hv compatible threshold]
  change ((progressionPairSolutions (T-V*p) U V 0 ((T-V*p)/U) 0 ((T-V*p)/V)).card : ℝ) =
      1+((T : ℝ)-(V : ℝ)*p)/((U : ℝ)*(V : ℝ))-
        (positiveInverseResidue T U V : ℝ)/(V : ℝ)-
        (((((T : ℤ)*Nat.gcdA V U-(p : ℤ)-1)%(U : ℤ)+1) : ℤ) : ℝ)/(U : ℝ)
  rw [positive_coprime_pair_count (Nat.sub_pos_of_lt shift) u0 v0 cop]
  rw [Nat.cast_sub shift.le,Nat.cast_mul,Int.ofNat_sub shift.le,Int.natCast_mul,
    positive_inverse_residue_sub_modulus,positive_inverse_residue_sub_step (T : ℤ) cop.symm]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_symmetric_residue_error -/
section

namespace GoldbachTypeII13

open scoped Classical

noncomputable section

def centeredInverseRamp (m : ℕ) (x : ℤ) : ℝ :=
  ((m : ℝ)-1)/(2*(m : ℝ))-((x%(m : ℤ) : ℤ) : ℝ)/(m : ℝ)

def symmetricResidueError (n u v p : ℕ) : ℝ :=
  let d := u.gcd v
  let U := u/d
  let V := v/d
  let T : ℤ := (n/d : ℕ)
  if d ∣ n ∧ v*p<n then
    centeredInverseRamp V (T*Nat.gcdA U V-1)+centeredInverseRamp U (T*Nat.gcdA V U-p-1)
  else 0

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_prime_right_low_residue -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale
open scoped Classical

noncomputable section

def centeredIntIntervalResidue (p : ℕ) (a b : ℤ) (x : ZMod p) : ℂ :=
  (intIntervalResidueCount p a b x : ℂ) - ((b-a : ℤ) : ℂ)/(p : ℂ)

theorem centered_int_interval_residue_fourier (p : ℕ) [NeZero p] {a b : ℤ}
    (hab : a ≤ b) (z : ZMod p) :
    centeredIntIntervalResidue p a b z =
      ∑ h ∈ (univ : Finset (ZMod p)).filter (fun h => h ≠ 0),
        ZMod.stdAddChar (-(h*z))*intIntervalFourierCoefficient p a b h := by
  unfold centeredIntIntervalResidue
  rw [int_interval_residue_count_fourier p hab z, add_sub_cancel_left]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_prime_weighted_intervals -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

def gatedBilinearSum {ι : Type*} (I : Finset ι) (J : Finset ℤ) (α : ι → ℂ) (β : ℤ → ℂ)
    (lo hi : ι → ℤ) (val : ι → ℤ → ℂ) : ℂ :=
  ∑ j ∈ J, β j * ∑ i ∈ I, if lo i < j ∧ j ≤ hi i then α i*val i j else 0

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_ramp_intervals -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

private theorem short_negative_ediv {a b : ℤ} (b0 : 0 < b) (low : -b ≤ a) (high : a < 0) :
    a/b = -1 := by
  have h₁ := (Int.le_ediv_iff_mul_le b0).mpr (show (-1 : ℤ)*b ≤ a by simpa only [neg_mul,one_mul] using low)
  have h₂ := (Int.ediv_lt_iff_lt_mul b0).mpr (show a < (0 : ℤ)*b by simpa only [zero_mul] using high)
  omega

private theorem int_interval_residue_count_short_prefix {m : ℕ} (m0 : 0 < m) (z : ℤ)
    {k : ℕ} (hk : k < m) :
    intIntervalResidueCount m 0 ((k : ℤ)+1) (z : ZMod m) =
      if (z-1)%(m : ℤ) ≤ (k : ℤ) then 1 else 0 := by
  let a := (z-1)%(m : ℤ)
  let r := a+1
  have mi : (0 : ℤ) < m := by exact_mod_cast m0
  have ki : (k : ℤ) < m := by exact_mod_cast hk
  have a0 : 0 ≤ a := Int.emod_nonneg _ mi.ne'
  have am : a < (m : ℤ) := Int.emod_lt_of_pos _ mi
  have r0 : 0 < r := by unfold r; omega
  have rm : r ≤ (m : ℤ) := by unfold r; omega
  have eqCast : (r : ZMod m) = (z : ZMod m) := by
    apply (ZMod.intCast_eq_intCast_iff r z m).mpr
    simpa only [r,a,sub_add_cancel] using (Int.mod_modEq (z-1) (m : ℤ)).add_right 1
  have identify : intIntervalResidueCount m 0 ((k : ℤ)+1) (z : ZMod m) =
      ((Ioc (0 : ℤ) ((k : ℤ)+1)).filter (fun x => x ≡ r [ZMOD (m : ℤ)])).card := by
    unfold intIntervalResidueCount
    apply congrArg Finset.card
    ext y
    rw [mem_filter,mem_filter,← eqCast,ZMod.intCast_eq_intCast_iff]
  rw [identify,card_residue_in_integer_interval _ _ _ _ mi]
  have negOne : ((0 : ℤ)-r)/(m : ℤ) = -1 := short_negative_ediv mi (by omega) (by omega)
  rw [negOne]
  change ((((k : ℤ)+1-r)/(m : ℤ)-(-1)).toNat) = if a ≤ (k : ℤ) then 1 else 0
  by_cases h : a ≤ (k : ℤ)
  · have eq : ((k : ℤ)+1-r)/(m : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by unfold r; omega) (by unfold r; omega)
    simp [h,eq]
  · have eq : ((k : ℤ)+1-r)/(m : ℤ) = -1 := short_negative_ediv mi (by unfold r; omega) (by unfold r; omega)
    simp [h,eq]

theorem centered_inverse_ramp_eq_prefix_average {m : ℕ} (m0 : 0 < m) (z : ℤ) :
    (centeredInverseRamp m (z-1) : ℂ) = (m : ℂ)⁻¹ *
      ∑ k ∈ range m, centeredIntIntervalResidue m 0 ((k : ℤ)+1) (z : ZMod m) := by
  let a := (z-1)%(m : ℤ)
  let r := a.toNat
  have mi : (0 : ℤ) < m := by exact_mod_cast m0
  have mc : (m : ℂ) ≠ 0 := by exact_mod_cast m0.ne'
  have a0 : 0 ≤ a := Int.emod_nonneg _ mi.ne'
  have am : a < (m : ℤ) := Int.emod_lt_of_pos _ mi
  have rep : (r : ℤ) = a := Int.toNat_of_nonneg a0
  have rm : r ≤ m := by
    have le : (r : ℤ) ≤ (m : ℤ) := rep ▸ am.le
    exact_mod_cast le
  have choices : ((range m).filter (fun k => r≤k)) = Ico r m := by
    ext k
    simp only [mem_filter,mem_range,mem_Ico,and_comm]
  have sumCounts : (∑ k ∈ range m, (intIntervalResidueCount m 0 ((k : ℤ)+1) (z : ZMod m) : ℂ)) =
      (m : ℂ)-(r : ℂ) := by
    calc
      _ = ∑ k ∈ range m, if r≤k then (1 : ℂ) else 0 := by
        refine sum_congr rfl fun k hk => ?_
        rw [int_interval_residue_count_short_prefix m0 z (mem_range.mp hk)]
        have equiv : a ≤ (k : ℤ) ↔ r≤k := by
          rw [← rep]
          constructor <;> intro h <;> exact_mod_cast h
        change ((if a≤(k : ℤ) then 1 else 0 : ℕ) : ℂ) = _
        simp only [equiv,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      _ = _ := by
        rw [← sum_filter,choices,sum_const,Nat.card_Ico,nsmul_eq_mul,mul_one,Nat.cast_sub rm]
  have sumEndpoints : (∑ k ∈ range m, ((k : ℂ)+1)) = (m : ℂ)*((m : ℂ)+1)/2 := by
    have one : 1 ≤ m := m0
    have eq := congrArg (fun t : ℕ => (t : ℂ)) (Finset.sum_range_id_mul_two m)
    simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,Nat.cast_sub one,Nat.cast_one] at eq
    rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one]
    linear_combination eq / 2
  unfold centeredInverseRamp centeredIntIntervalResidue
  change (((((m : ℝ)-1)/(2*(m : ℝ))-(a : ℝ)/(m : ℝ)) : ℝ) : ℂ) = _
  push_cast
  simp only [sub_zero,sum_sub_distrib,← sum_div,Int.cast_add,Int.cast_one,Int.cast_natCast]
  rw [sumCounts,sumEndpoints,← rep,Int.cast_natCast]
  field_simp
  <;> ring

theorem norm_gated_inverse_ramp_le_of_prefix_bounds {m : ℕ} (m0 : 0 < m) {ι : Type*}
    (I : Finset ι) (J : Finset ℤ) (a : ι → ℂ) (b : ℤ → ℂ) (lo hi : ι → ℤ) (z : ι → ℤ → ℤ)
    {B : ℝ} (B0 : 0 ≤ B)
    (bounds : ∀ k < m, ‖gatedBilinearSum I J a b lo hi (fun i j =>
      centeredIntIntervalResidue m 0 ((k : ℤ)+1) (z i j : ZMod m))‖ ≤ B) :
    ‖gatedBilinearSum I J a b lo hi (fun i j => (centeredInverseRamp m (z i j-1) : ℂ))‖ ≤ B := by
  let F (k : ℕ) (i : ι) (j : ℤ) : ℂ :=
    if lo i<j ∧ j≤hi i then a i*centeredIntIntervalResidue m 0 ((k : ℤ)+1) (z i j : ZMod m) else 0
  have point (i : ι) (j : ℤ) :
      (if lo i<j ∧ j≤hi i then a i*(centeredInverseRamp m (z i j-1) : ℂ) else 0) =
        (m : ℂ)⁻¹ * ∑ k ∈ range m, F k i j := by
    by_cases h : lo i<j ∧ j≤hi i
    · rw [if_pos h,centered_inverse_ramp_eq_prefix_average m0]
      unfold F
      simp only [if_pos h,←mul_sum]
      ring
    · simp [F,h]
  have rearrange : gatedBilinearSum I J a b lo hi (fun i j => (centeredInverseRamp m (z i j-1) : ℂ)) =
      (m : ℂ)⁻¹ * ∑ k ∈ range m, gatedBilinearSum I J a b lo hi (fun i j =>
        centeredIntIntervalResidue m 0 ((k : ℤ)+1) (z i j : ZMod m)) := by
    unfold gatedBilinearSum
    simp_rw [point]
    calc
      _ = ∑ j ∈ J, (m : ℂ)⁻¹ * ∑ k ∈ range m, b j * ∑ i ∈ I, F k i j := by
        refine sum_congr rfl fun j _ => ?_
        rw [←mul_sum, sum_comm, ←mul_sum]
        ring
      _ = _ := by
        rw [←mul_sum,sum_comm]
  rw [rearrange,norm_mul,norm_inv,Complex.norm_natCast]
  have mr : (0 : ℝ) < m := by exact_mod_cast m0
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ k ∈ range m, ‖gatedBilinearSum I J a b lo hi (fun i j =>
        centeredIntIntervalResidue m 0 ((k : ℤ)+1) (z i j : ZMod m))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (m : ℝ)⁻¹ * ∑ _ ∈ range m, B :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun k hk => bounds k (mem_range.mp hk)) (by positivity)
    _ = B := by rw [sum_const,card_range,nsmul_eq_mul,← mul_assoc,inv_mul_cancel₀ mr.ne',one_mul]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_bilinear_bound -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical ComplexConjugate

noncomputable section

theorem norm_gated_weil_inverse_sq_le {m A : ℕ} [NeZero m] (c : ZMod m)
    (I : Finset ℕ) (base : I ⊆ Icc 1 A) (cop : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ) {L R : ℤ} (span : R-L ≤ m)
    {T : ℝ} (T0 : 0 ≤ T) (weights : ∀ i ∈ I, ‖α i‖ ≤ T) :
    let J := intIntervalModUnits m L R
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹))‖^2 ≤
      (∑ j ∈ J, ‖β j‖^2)*
        ((#J : ℝ)*(∑ i ∈ I, ‖α i‖^2) +
          2*(A : ℝ)^2*T^2*(m.divisors.card : ℝ)*weilReciprocalBudget m*Real.sqrt (m.gcd c.val)) := by
  dsimp only
  let J := intIntervalModUnits m L R
  let f (i : ℕ) (j : ℤ) : ℂ :=
    if lo i < j ∧ j ≤ hi i then ZMod.stdAddChar (c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹) else 0
  let W := weilReciprocalBudget m*Real.sqrt (m.gcd c.val)
  let K (i t : ℕ) := if i=t then 0 else W*(m.gcd (((t : ℤ)-(i : ℤ)).natAbs) : ℝ)
  let C (i t : ℕ) := c*((i : ZMod m)⁻¹-(t : ZMod m)⁻¹)
  have m0 : 0 < m := NeZero.pos m
  have B0 : 0 ≤ weilReciprocalBudget m := weil_reciprocal_budget_nonneg m0
  have W0 : 0 ≤ W := mul_nonneg B0 (Real.sqrt_nonneg _)
  have K0 (i t : ℕ) : 0 ≤ K i t := by unfold K; split_ifs <;> positivity
  have fBound (i : ℕ) (j : ℤ) : ‖f i j‖ ≤ 1 := by
    unfold f
    split_ifs
    · rw [norm_stdAddChar_eq_one]
    · simp
  have diag (i : ℕ) (_ : i ∈ I) : ‖∑ j ∈ J, f i j*conj (f i j)‖ ≤ (#J : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ J, (1 : ℝ) := sum_le_sum fun j _ => by
        rw [norm_mul,Complex.norm_conj]
        exact (mul_le_mul (fBound i j) (fBound i j) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by simp
  have off (i : ℕ) (hiI : i ∈ I) (t : ℕ) (ht : t ∈ I) (hne : i ≠ t) :
      ‖∑ j ∈ J, f i j*conj (f t j)‖ ≤ K i t := by
    let a := max L (max (lo i) (lo t))
    let b := min R (min (hi i) (hi t))
    let F := intIntervalModUnits m a b
    have filterEq : F = J.filter (fun j => (lo i < j ∧ j ≤ hi i) ∧ (lo t < j ∧ j ≤ hi t)) := by
      ext j
      simp only [F,J,intIntervalModUnits,a,b,mem_filter,mem_Ioc,max_lt_iff,le_min_iff]
      tauto
    have pairSum : ∑ j ∈ J, f i j*conj (f t j) =
        ∑ j ∈ F, ZMod.stdAddChar (C i t*(j : ZMod m)⁻¹) := by
      rw [filterEq,sum_filter]
      refine sum_congr rfl fun j _ => ?_
      by_cases h₁ : lo i < j ∧ j ≤ hi i <;>
        by_cases h₂ : lo t < j ∧ j ≤ hi t <;> simp [f,h₁,h₂,conj_stdAddChar]
      rw [← AddChar.map_add_eq_mul]
      congr 1
      unfold C
      ring
    have width : b-a ≤ (m : ℤ) :=
      (sub_le_sub (min_le_left R (min (hi i) (hi t)))
        (le_max_left L (max (lo i) (lo t)))).trans span
    have d := gcd_unit_inverse_difference_le c (cop i hiI) (cop t ht)
    let g := m.gcd (((t : ℤ)-(i : ℤ)).natAbs)
    have g1 : (1 : ℝ) ≤ g := by
      exact_mod_cast (show 1 ≤ g from Nat.gcd_pos_of_pos_left _ m0)
    have bound : Real.sqrt (m.gcd (C i t).val) ≤ Real.sqrt (m.gcd c.val)*(g : ℝ) := by
      calc
        _ ≤ Real.sqrt ((m.gcd c.val : ℝ)*(g : ℝ)) := Real.sqrt_le_sqrt (by dsimp only [C,g]; exact_mod_cast d)
        _ = Real.sqrt (m.gcd c.val)*Real.sqrt (g : ℝ) := by rw [Real.sqrt_mul (by positivity)]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr g1)) (Real.sqrt_nonneg _)
    rw [pairSum]
    calc
      _ ≤ weilReciprocalBudget m*Real.sqrt (m.gcd (C i t).val) :=
        norm_modular_unit_inverse_interval_le_weil (C i t) width
      _ ≤ weilReciprocalBudget m*(Real.sqrt (m.gcd c.val)*(g : ℝ)) := mul_le_mul_of_nonneg_left bound B0
      _ = K i t := by unfold K W g; rw [if_neg hne]; ring
  have oneRow (i : ℕ) (hiI : i ∈ I) :
      (∑ t ∈ I, K i t*(‖α i‖*‖α t‖)) ≤ W*(2*(A : ℝ)*(m.divisors.card : ℝ)*T^2) := by
    calc
      _ = ∑ t ∈ I.erase i, K i t*(‖α i‖*‖α t‖) := by
        rw [← sum_erase_add _ _ hiI]
        simp [K]
      _ ≤ ∑ t ∈ I.erase i, W*((m.gcd (((t : ℤ)-(i : ℤ)).natAbs) : ℝ)*T^2) := by
        refine sum_le_sum fun t ht => ?_
        have notEqual : i ≠ t := (mem_erase.mp ht).1.symm
        unfold K
        rw [if_neg notEqual,pow_two]
        calc
          _ = W*((m.gcd (((t : ℤ)-(i : ℤ)).natAbs) : ℝ)*(‖α i‖*‖α t‖)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul (weights i hiI) (weights t (mem_erase.mp ht).2)
              (norm_nonneg _) T0) (by positivity)) W0
      _ = W*((∑ t ∈ I.erase i, (m.gcd (((t : ℤ)-(i : ℤ)).natAbs) : ℝ))*T^2) := by rw [sum_mul,mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (sum_gcd_of_distinct_differences_le m0 base hiI) (sq_nonneg T)) W0
  have cardA : (#I : ℝ) ≤ (A : ℝ) := by
    have h : #I ≤ A := (card_le_card base).trans_eq (by simp [Nat.card_Icc])
    exact_mod_cast h
  have total : (∑ i ∈ I, ∑ t ∈ I, K i t*(‖α i‖*‖α t‖)) ≤
      2*(A : ℝ)^2*T^2*(m.divisors.card : ℝ)*weilReciprocalBudget m*Real.sqrt (m.gcd c.val) := by
    calc
      _ ≤ ∑ _ ∈ I, W*(2*(A : ℝ)*(m.divisors.card : ℝ)*T^2) := sum_le_sum oneRow
      _ = (#I : ℝ)*(W*(2*(A : ℝ)*(m.divisors.card : ℝ)*T^2)) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ (A : ℝ)*(W*(2*(A : ℝ)*(m.divisors.card : ℝ)*T^2)) := mul_le_mul_of_nonneg_right cardA (by positivity)
      _ = _ := by unfold W; ring
  have eq (j : ℤ) :
      (∑ i ∈ I, if lo i<j ∧ j≤hi i then α i*ZMod.stdAddChar (c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹) else 0) =
      ∑ i ∈ I, α i*f i j := by
    refine sum_congr rfl fun i _ => ?_
    unfold f
    split_ifs <;> simp
  unfold gatedBilinearSum
  change ‖∑ j ∈ J, β j*(∑ i ∈ I, if lo i<j ∧ j≤hi i then
    α i*ZMod.stdAddChar (c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹) else 0)‖^2 ≤ _
  simp_rw [eq]
  exact (norm_weighted_bilinear_correlation_sq_le_with_cost I J α β f K K0 diag off).trans
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) total) (by positivity))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_fourier_large_divisor_bound -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical Finset

noncomputable section

theorem sum_norm_interval_coefficients_at_divisor_multiples_le {m d : ℕ} [NeZero m]
    (d0 : 0 < d) (dm : d ∣ m) (a b : ℤ) :
    (∑ h ∈ ((univ : Finset (ZMod m)).filter (fun h => h ≠ 0)).filter (fun h => d ∣ h.val),
      ‖intIntervalFourierCoefficient m a b h‖) ≤ (1+Real.log m)/(d : ℝ) := by
  let q := m/d
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have q0 : 0 < q := Nat.div_pos (Nat.le_of_dvd m0 dm) d0
  let _ : NeZero q := ⟨q0.ne'⟩
  let X := ((univ : Finset (ZMod m)).filter (fun h => h ≠ 0)).filter (fun h => d ∣ h.val)
  let Y := (univ : Finset (ZMod q)).filter (fun h => h ≠ 0)
  let f (h : ZMod m) : ZMod q := (h.val/d : ℕ)
  let C (h : ZMod q) : ℝ := 1/(2*(min h.val (q-h.val) : ℕ) : ℝ)
  have dp : (0 : ℝ) < d := by exact_mod_cast d0
  have mQ : d*q=m := Nat.mul_div_cancel' dm
  have pos (h : ZMod m) (hh : h ∈ X) : 0 < h.val :=
    ZMod.val_pos.mpr (mem_filter.mp (mem_filter.mp hh).1).2
  have dH (h : ZMod m) (hh : h ∈ X) : d ∣ h.val := (mem_filter.mp hh).2
  have upper (h : ZMod m) : h.val/d < q := (Nat.div_lt_iff_lt_mul d0).mpr
    (by rw [mul_comm, mQ]; exact ZMod.val_lt h)
  have valF (h : ZMod m) : (f h).val = h.val/d := ZMod.val_natCast_of_lt (upper h)
  have eq (h : ZMod m) (hh : h ∈ X) : d*(f h).val=h.val := by
    rw [valF,Nat.mul_div_cancel' (dH h hh)]
  have f0 (h : ZMod m) (hh : h ∈ X) : f h ≠ 0 := by
    intro hz
    have v := (pos h hh).ne'
    rw [← eq h hh,hz,ZMod.val_zero,mul_zero] at v
    exact v rfl
  have inj : Set.InjOn f X := by
    intro h hh k hk he
    apply ZMod.val_injective m
    rw [← eq h hh,← eq k hk,he]
  have incl : X.image f ⊆ Y := by
    intro j hj
    obtain ⟨h,hh,rfl⟩ := mem_image.mp hj
    exact mem_filter.mpr ⟨mem_univ _,f0 h hh⟩
  have each (h : ZMod m) (hh : h ∈ X) :
      ‖intIntervalFourierCoefficient m a b h‖ ≤ ((1 : ℝ)/d)*C (f h) := by
    refine (norm_int_interval_fourier_coefficient_le m a b (mem_filter.mp (mem_filter.mp hh).1).2).trans_eq ?_
    have min_eq : min h.val (m-h.val) = d*min (f h).val (q-(f h).val) := by
      rw [← eq h hh,← mQ,← Nat.mul_sub_left_distrib]
      exact (mul_min_of_nonneg _ _ (Nat.zero_le d)).symm
    have min0 : 0 < min (f h).val (q-(f h).val) :=
      lt_min (ZMod.val_pos.mpr (f0 h hh)) (Nat.sub_pos_of_lt (ZMod.val_lt _))
    have mp : (0 : ℝ) < (min (f h).val (q-(f h).val) : ℕ) := by exact_mod_cast min0
    unfold C
    rw [min_eq,Nat.cast_mul]
    field_simp
  calc
    _ ≤ ∑ h ∈ X, ((1 : ℝ)/d)*C (f h) := sum_le_sum each
    _ = ((1 : ℝ)/d)*∑ j ∈ X.image f, C j := by
      rw [mul_sum,sum_image (fun a ha b hb h => inj ha hb h)]
    _ ≤ ((1 : ℝ)/d)*∑ j ∈ Y, C j := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg incl (fun _ _ _ => by unfold C; positivity)) (by positivity)
    _ ≤ ((1 : ℝ)/d)*(1+Real.log q) := by
      exact mul_le_mul_of_nonneg_left (sum_inv_min_val_le q) (by positivity)
    _ ≤ _ := by
      have cmp : 1+Real.log (q : ℝ) ≤ 1+Real.log (m : ℝ) :=
        add_le_add_right (Real.log_le_log (by exact_mod_cast q0 : (0 : ℝ) < q)
          (by exact_mod_cast Nat.div_le_self m d : (q : ℝ) ≤ m)) 1
      calc
        _ ≤ ((1 : ℝ)/d)*(1+Real.log m) := mul_le_mul_of_nonneg_left cmp (by positivity)
        _ = _ := by ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_fourier_gcd_weighted_sum -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem sum_norm_interval_coefficients_mul_gcd_le {m : ℕ} [NeZero m] (a b : ℤ) :
    (∑ h ∈ (univ : Finset (ZMod m)).filter (fun h => h ≠ 0),
      ‖intIntervalFourierCoefficient m a b h‖*(m.gcd h.val : ℝ)) ≤
        (m.divisors.card : ℝ)*(1+Real.log m) := by
  let H := (univ : Finset (ZMod m)).filter fun h => h ≠ 0
  let F (h : ZMod m) := ‖intIntervalFourierCoefficient m a b h‖
  have m0 := NeZero.pos m
  have row (h : ZMod m) : F h*(m.gcd h.val : ℝ) ≤
      ∑ d ∈ m.divisors, if d ∣ h.val then F h*(d : ℝ) else 0 := by
    let d := m.gcd h.val
    have dm : d ∈ m.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,m0.ne'⟩
    have dh : d ∣ h.val := Nat.gcd_dvd_right _ _
    refine (show F h*(d : ℝ) = (if d ∣ h.val then F h*(d : ℝ) else 0) by rw [if_pos dh]).le.trans ?_
    exact single_le_sum (f := fun k => if k ∣ h.val then F h*(k : ℝ) else 0)
      (fun _ _ => by split_ifs <;> positivity) dm
  have each (d : ℕ) (hd : d ∈ m.divisors) :
      (∑ h ∈ H, if d ∣ h.val then F h*(d : ℝ) else 0) ≤ 1+Real.log m := by
    have d0 := Nat.pos_of_mem_divisors hd
    have dr : (0 : ℝ) < d := by exact_mod_cast d0
    rw [← sum_filter,← sum_mul]
    calc
      _ ≤ ((1+Real.log m)/(d : ℝ))*(d : ℝ) :=
        mul_le_mul_of_nonneg_right
          (sum_norm_interval_coefficients_at_divisor_multiples_le d0 (Nat.dvd_of_mem_divisors hd) a b) dr.le
      _ = _ := by field_simp
  calc
    _ ≤ ∑ h ∈ H, ∑ d ∈ m.divisors, if d ∣ h.val then F h*(d : ℝ) else 0 := sum_le_sum fun h _ => row h
    _ = ∑ d ∈ m.divisors, ∑ h ∈ H, if d ∣ h.val then F h*(d : ℝ) else 0 := sum_comm
    _ ≤ ∑ _ ∈ m.divisors, (1+Real.log m) := sum_le_sum each
    _ = _ := by rw [sum_const,nsmul_eq_mul]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_gated_residue_frequency_bounds -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem norm_gated_interval_residue_le_of_frequency_bounds {m : ℕ} [NeZero m] {ι : Type*}
    (I : Finset ι) (J : Finset ℤ) (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ)
    (z : ι → ℤ → ZMod m) {a b : ℤ} (ab : a ≤ b) {D E : ℝ} (D0 : 0 ≤ D) (E0 : 0 ≤ E)
    (bound : ∀ h : ZMod m, h ≠ 0 →
      ‖gatedBilinearSum I J α β lo hi (fun i j => ZMod.stdAddChar (-(h*z i j)))‖ ≤ D+E*(m.gcd h.val : ℝ)) :
    ‖gatedBilinearSum I J α β lo hi (fun i j => centeredIntIntervalResidue m a b (z i j))‖ ≤
      (1+Real.log m)*D+((m.divisors.card : ℝ)*(1+Real.log m))*E := by
  let H := (univ : Finset (ZMod m)).filter fun h => h ≠ 0
  let C (h : ZMod m) := intIntervalFourierCoefficient m a b h
  let f (h : ZMod m) (i : ι) (j : ℤ) := ZMod.stdAddChar (-(h*z i j))
  let F (h : ZMod m) := gatedBilinearSum I J α β lo hi (f h)
  have point (i : ι) (j : ℤ) :
      (if lo i < j ∧ j ≤ hi i then α i*centeredIntIntervalResidue m a b (z i j) else 0) =
      ∑ h ∈ H, C h*(if lo i < j ∧ j ≤ hi i then α i*f h i j else 0) := by
    by_cases gate : lo i < j ∧ j ≤ hi i
    · rw [if_pos gate,centered_int_interval_residue_fourier m ab,mul_sum]
      refine sum_congr rfl fun h _ => ?_
      rw [if_pos gate]
      unfold C f
      ring
    · simp [gate]
  have expansion : gatedBilinearSum I J α β lo hi
        (fun i j => centeredIntIntervalResidue m a b (z i j)) = ∑ h ∈ H, C h*F h := by
    calc
      _ = ∑ j ∈ J, β j*(∑ i ∈ I,∑ h ∈ H, C h*(if lo i < j ∧ j ≤ hi i then α i*f h i j else 0)) := by
        unfold gatedBilinearSum
        refine sum_congr rfl fun j _ => congrArg (fun x : ℂ => β j*x) (sum_congr rfl fun i _ => point i j)
      _ = _ := by
        have per (j : ℤ) :
            β j*(∑ i ∈ I,∑ h ∈ H, C h*(if lo i < j ∧ j ≤ hi i then α i*f h i j else 0)) =
              ∑ h ∈ H, C h*(β j*(∑ i ∈ I, if lo i < j ∧ j ≤ hi i then α i*f h i j else 0)) := by
          rw [sum_comm,mul_sum]
          refine sum_congr rfl fun h _ => ?_
          rw [← mul_sum]
          ring
        simp only [per]
        rw [sum_comm]
        refine sum_congr rfl fun h _ => ?_
        rw [← mul_sum] <;> rfl
  rw [expansion]
  calc
    _ ≤ ∑ h ∈ H, ‖C h*F h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ H, ‖C h‖*(D+E*(m.gcd h.val : ℝ)) := by
      refine sum_le_sum fun h hh => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (bound h (mem_filter.mp hh).2) (norm_nonneg _)
    _ = (∑ h ∈ H, ‖C h‖)*D+(∑ h ∈ H, ‖C h‖*(m.gcd h.val : ℝ))*E := by
      rw [sum_mul,sum_mul,←sum_add_distrib]
      exact sum_congr rfl (fun _ _ => by ring)
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (sum_norm_int_interval_fourier_coefficient_le m a b) D0)
      (mul_le_mul_of_nonneg_right (sum_norm_interval_coefficients_mul_gcd_le a b) E0)

theorem gated_phase_shift_eq_twisted_weights {m : ℕ} [NeZero m] {ι : Type*}
    (I : Finset ι) (J : Finset ℤ) (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ)
    (z : ι → ℤ → ZMod m) (s : ι → ZMod m) (t : ℤ → ZMod m) (h : ZMod m) :
    gatedBilinearSum I J α β lo hi
      (fun i j => ZMod.stdAddChar (-(h*(z i j-s i-t j)))) =
    gatedBilinearSum I J (fun i => α i*ZMod.stdAddChar (h*s i))
      (fun j => β j*ZMod.stdAddChar (h*t j)) lo hi
      (fun i j => ZMod.stdAddChar (-(h*z i j))) := by
  unfold gatedBilinearSum
  refine sum_congr rfl fun j _ => ?_
  rw [mul_assoc]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  by_cases gate : lo i < j ∧ j ≤ hi i
  · rw [if_pos gate,if_pos gate]
    dsimp only
    rw [show -(h*(z i j-s i-t j)) = (h*t j+h*s i)+ -(h*z i j) by ring]
    rw [AddChar.map_add_eq_mul,AddChar.map_add_eq_mul]
    ring
  · rw [if_neg gate,if_neg gate,mul_zero]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_fibre_factorization -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical Finset

noncomputable section

def inverseCollisionFiber (p A : ℕ) (target : ZMod p) : Finset (ℕ × ℕ) :=
  (Icc 1 A ×ˢ Icc 1 A).filter (fun i =>
    (i.1 : ZMod p)⁻¹ + (i.2 : ZMod p)⁻¹ = target)

theorem reciprocal_dirichlet_candidate {p R : ℕ} [NeZero p] (c : ZMod p) (Rpos : 0 < R) :
    ∃ s t : ℤ, 0 < s ∧ s ≤ R ∧ (t : ZMod p) = (s : ZMod p)*c ∧
      (↑|t| : ℝ) ≤ (p : ℝ)/((R : ℝ)+1) := by
  have pp : (0 : ℝ) < p := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne p))
  obtain ⟨j,s,s0,sR,h⟩ := Real.exists_int_int_abs_mul_sub_le ((c.val : ℝ)/p) Rpos
  let t : ℤ := s*(c.val : ℤ) - j*p
  have castT : (t : ZMod p) = (s : ZMod p)*c := by
    simp only [t, Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_self, mul_zero, sub_zero]
  have frac : (s : ℝ)*((c.val : ℝ)/p) - (j : ℝ) = (t : ℝ)/(p : ℝ) := by
    unfold t
    push_cast
    field_simp
  rw [frac,abs_div,abs_of_pos pp,div_le_iff₀ pp] at h
  refine ⟨s,t,s0,sR,castT,?_⟩
  push_cast
  have reorder : (1/((R : ℝ)+1))*(p : ℝ) = (p : ℝ)/((R : ℝ)+1) := by ring
  exact h.trans_eq reorder

theorem reciprocal_fibre_pair_factorization_of_units {p A : ℕ} [NeZero p]
    {c : ZMod p} {s t : ℤ} (castT : (t : ZMod p) = (s : ZMod p)*c)
    {i : ℕ × ℕ} (hi : i ∈ inverseCollisionFiber p A c)
    (xU : IsUnit (i.1 : ZMod p)) (yU : IsUnit (i.2 : ZMod p)) :
    ∃ k : ℤ, |k| ≤ (|t| * (A : ℤ)^2+2*|s| * (A : ℤ))/(p : ℤ) ∧
      (t*(i.1 : ℤ)-s)*(t*(i.2 : ℤ)-s) = s^2+t*k*(p : ℤ) := by
  have p0 : (0 : ℤ) < p := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne p))
  obtain ⟨range,recip⟩ := mem_filter.mp hi
  obtain ⟨hx,hy⟩ := mem_product.mp range
  have xA := (mem_Icc.mp hx).2
  have yA := (mem_Icc.mp hy).2
  have cEq : c*(i.1 : ZMod p)*(i.2 : ZMod p) = (i.1 : ZMod p)+(i.2 : ZMod p) := by
    rw [← recip, add_mul, ZMod.inv_mul_of_unit _ xU, add_mul, one_mul,
      mul_right_comm ((i.2 : ZMod p)⁻¹), ZMod.inv_mul_of_unit _ yU, one_mul, add_comm]
  let g : ℤ := t*(i.1 : ℤ)*(i.2 : ℤ)-s*((i.1 : ℤ)+(i.2 : ℤ))
  have zero : (g : ZMod p) = 0 := by
    unfold g
    push_cast
    rw [castT, mul_assoc (s : ZMod p), mul_assoc (s : ZMod p), cEq]
    exact sub_self _
  have div : (p : ℤ) ∣ g := by
    have eq : (g : ZMod p) = ((0 : ℤ) : ZMod p) := by simpa only [Int.cast_zero] using zero
    exact Int.modEq_zero_iff_dvd.mp ((ZMod.intCast_eq_intCast_iff g 0 p).mp eq)
  obtain ⟨k,hk⟩ := div
  have x : (i.1 : ℤ) ≤ A := by exact_mod_cast xA
  have y : (i.2 : ℤ) ≤ A := by exact_mod_cast yA
  have gabs : |g| ≤ |t| * (A : ℤ)^2+2*|s| * (A : ℤ) := by
    unfold g
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (i.1 : ℤ)),
      abs_of_nonneg (by positivity : 0 ≤ (i.2 : ℤ)), abs_of_nonneg (by positivity : 0 ≤ (i.1 : ℤ)+(i.2 : ℤ))]
    have xy : (i.1 : ℤ)*(i.2 : ℤ) ≤ (A : ℤ)^2 := by
      rw [pow_two]
      exact mul_le_mul x y (by positivity) (by positivity)
    have summed : (i.1 : ℤ)+(i.2 : ℤ) ≤ 2*(A : ℤ) := by linarith only [x,y]
    calc
      _ = |t| * ((i.1 : ℤ)*(i.2 : ℤ)) + |s| * ((i.1 : ℤ)+(i.2 : ℤ)) := by ring
      _ ≤ |t| * (A : ℤ)^2+|s| * (2*(A : ℤ)) :=
        add_le_add (mul_le_mul_of_nonneg_left xy (abs_nonneg _))
          (mul_le_mul_of_nonneg_left summed (abs_nonneg _))
      _ = _ := by ring
  have kbound : |k| ≤ (|t| * (A : ℤ)^2+2*|s| * (A : ℤ))/(p : ℤ) := by
    apply (Int.le_ediv_iff_mul_le p0).mpr
    rw [hk,abs_mul,abs_of_pos p0,mul_comm] at gabs
    exact gabs
  refine ⟨k,kbound,?_⟩
  unfold g at hk
  linear_combination t*hk

private theorem card_shifted_product_le (A : ℕ) (s t M : ℤ) (t0 : t ≠ 0) (M0 : M ≠ 0) :
    #((Icc 1 A ×ˢ Icc 1 A).filter (fun i =>
      (t*(i.1 : ℤ)-s)*(t*(i.2 : ℤ)-s) = M)) ≤ 2*M.natAbs.divisors.card := by
  let X := (Icc 1 A ×ˢ Icc 1 A).filter (fun i => (t*(i.1 : ℤ)-s)*(t*(i.2 : ℤ)-s) = M)
  let Y := (univ : Finset Bool) ×ˢ M.natAbs.divisors
  let z (i : ℕ × ℕ) := t*(i.1 : ℤ)-s
  let w (i : ℕ × ℕ) := t*(i.2 : ℤ)-s
  let f (i : ℕ × ℕ) := (decide (0 ≤ z i), (z i).natAbs)
  have product {i : ℕ × ℕ} (hi : i ∈ X) : z i*w i = M := (mem_filter.mp hi).2
  have maps : #X ≤ #Y := by
    refine card_le_card_of_injOn f ?_ ?_
    · intro i hi
      apply mem_product.mpr
      refine ⟨mem_univ _,Nat.mem_divisors.mpr ⟨?_,by simpa using M0⟩⟩
      exact ⟨(w i).natAbs, by rw [← Int.natAbs_mul, product hi]⟩
    · intro a ha b hb eq
      have sign : decide (0 ≤ z a) = decide (0 ≤ z b) := congrArg Prod.fst eq
      have mag : (z a).natAbs = (z b).natAbs := congrArg Prod.snd eq
      have ez : z a = z b := by
        rcases (Int.natAbs_eq_natAbs_iff.mp mag) with h | h
        · exact h
        · rw [h] at sign ⊢
          by_cases neg : z b < 0
          · simp [not_le.mpr neg] at sign
            omega
          · have nonneg : 0 ≤ z b := le_of_not_gt neg
            have neg' : 0 ≤ -z b := of_decide_eq_true (sign.trans (decide_eq_true nonneg))
            omega
      have ew : w a = w b := by
        have both := (product ha).trans (product hb).symm
        rw [←ez] at both
        have za0 : z a ≠ 0 := fun e => M0 (by simpa [e] using (product ha).symm)
        exact mul_left_cancel₀ za0 both
      have x : (a.1 : ℤ) = b.1 := by
        apply mul_left_cancel₀ t0
        change t*(a.1 : ℤ)-s = t*(b.1 : ℤ)-s at ez
        omega
      have y : (a.2 : ℤ) = b.2 := by
        apply mul_left_cancel₀ t0
        change t*(a.2 : ℤ)-s = t*(b.2 : ℤ)-s at ew
        omega
      exact Prod.ext (by exact_mod_cast x) (by exact_mod_cast y)
  apply maps.trans_eq
  simp [Y,card_product]

theorem reciprocal_card_le_of_nonzero_determinant_cover (p A : ℕ) {X : Finset (ℕ × ℕ)} {s t : ℤ}
    (t0 : t ≠ 0) (range : X ⊆ Icc 1 A ×ˢ Icc 1 A)
    (factor : ∀ i ∈ X, ∃ k : ℤ, |k| ≤ (|t| * (A : ℤ)^2+2*|s| * (A : ℤ))/(p : ℤ) ∧ s^2+t*k*(p : ℤ) ≠ 0 ∧
      (t*(i.1 : ℤ)-s)*(t*(i.2 : ℤ)-s) = s^2+t*k*(p : ℤ)) :
    let K : ℤ := (|t| * (A : ℤ)^2+2*|s| * (A : ℤ))/(p : ℤ)
    X.card ≤ 2*(∑ k ∈ Icc (-K) K, (s^2+t*k*(p : ℤ)).natAbs.divisors.card) := by
  dsimp only
  let K := (|t| * (A : ℤ)^2+2*|s| * (A : ℤ))/(p : ℤ)
  let m (k : ℤ) := s^2+t*k*(p : ℤ)
  let G (k : ℤ) := (Icc 1 A ×ˢ Icc 1 A).filter (fun i => (t*(i.1 : ℤ)-s)*(t*(i.2 : ℤ)-s) = m k)
  let active := (Icc (-K) K).filter fun k => m k ≠ 0
  have inc : X ⊆ active.biUnion G := by
    intro i hi
    obtain ⟨k,bound,nonzero,eq⟩ := factor i hi
    exact mem_biUnion.mpr ⟨k,mem_filter.mpr ⟨mem_Icc.mpr (abs_le.mp bound),nonzero⟩,mem_filter.mpr ⟨range hi,eq⟩⟩
  calc
    _ ≤ #(active.biUnion G) := card_le_card inc
    _ ≤ ∑ k ∈ active, #(G k) := card_biUnion_le
    _ ≤ ∑ k ∈ active, 2*(m k).natAbs.divisors.card :=
      sum_le_sum fun k hk => card_shifted_product_le A s t (m k) t0 (mem_filter.mp hk).2
    _ ≤ ∑ k ∈ Icc (-K) K, 2*(m k).natAbs.divisors.card :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    _ = _ := (mul_sum ..).symm

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_fibre_budget -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

def inverseFibreBudget (p A : ℕ) (T : ℝ) : ℝ :=
  2*T*(1+6*(A : ℝ)*Real.sqrt ((p : ℝ)*(A : ℝ))/(p : ℝ))

theorem reciprocal_dirichlet_radius_pos {p A : ℕ} (p0 : 0 < p) (A0 : 0 < A) :
    0 < ⌊Real.sqrt ((p : ℝ)*(A : ℝ))⌋₊ := by
  have pr : (1 : ℝ) ≤ p := by exact_mod_cast p0
  have ar : (1 : ℝ) ≤ A := by exact_mod_cast A0
  have h : (1 : ℝ) ≤ (p : ℝ)*(A : ℝ) := one_le_mul_of_one_le_of_one_le pr ar
  exact Nat.le_floor (by simpa using Real.sqrt_le_sqrt h)

theorem reciprocal_count_le_of_small_coefficients {p A count : ℕ} [NeZero p] (Apos : 0 < A) (Asmall : A < p)
    {s t : ℤ} (spos : 0 < s) (sR : s ≤ (⌊Real.sqrt ((p : ℝ)*(A : ℝ))⌋₊ : ℕ))
    (tbound : (↑|t| : ℝ) ≤ (p : ℝ)/(⌊Real.sqrt ((p : ℝ)*(A : ℝ))⌋₊ + 1 : ℝ))
    (countBound : let K : ℤ := (|t| * (A : ℤ)^2+2*|s| * (A : ℤ))/(p : ℤ)
      count ≤ 2*(∑ k ∈ Icc (-K) K, (s^2+t*k*(p : ℤ)).natAbs.divisors.card))
    {T : ℝ} (T0 : 0 ≤ T) (divisors : ∀ m ≤ 4*p^3, (m.divisors.card : ℝ) ≤ T) :
    (count : ℝ) ≤ inverseFibreBudget p A T := by
  let P := (p : ℝ)
  let B := (A : ℝ)
  let X := Real.sqrt (P*B)
  let R := ⌊X⌋₊
  have p0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have pp : 0 < P := by change 0 < (p : ℝ); exact_mod_cast p0
  have p1 : 1 ≤ P := by change 1 ≤ (p : ℝ); exact_mod_cast p0
  have b1 : 1 ≤ B := by change 1 ≤ (A : ℝ); exact_mod_cast Apos
  have bp : B < P := by change (A : ℝ) < (p : ℝ); exact_mod_cast Asmall
  have x1 : 1 ≤ X := by
    have h : (1 : ℝ) ≤ P*B := one_le_mul_of_one_le_of_one_le p1 b1
    simpa [X] using Real.sqrt_le_sqrt h
  have xp : 0 < X := zero_lt_one.trans_le x1
  have xP : X < P := by
    have h : P*B < P^2 := by rw [pow_two]; exact mul_lt_mul_of_pos_left bp pp
    simpa only [X,Real.sqrt_sq pp.le] using Real.sqrt_lt_sqrt (by positivity : 0 ≤ P*B) h
  have xSq : X^2 = P*B := Real.sq_sqrt (by positivity)
  have Rle : (R : ℝ) ≤ X := Nat.floor_le xp.le
  have Rplus : X ≤ (R : ℝ)+1 := (Nat.lt_floor_add_one X).le
  let K : ℤ := (|t| * (A : ℤ)^2+2*|s| * (A : ℤ))/(p : ℤ)
  let S := ((|s| : ℤ) : ℝ)
  let U := ((|t| : ℤ) : ℝ)
  have S0 : 0 ≤ S := by unfold S; exact_mod_cast abs_nonneg s
  have U0 : 0 ≤ U := by unfold U; exact_mod_cast abs_nonneg t
  change s ≤ (R : ℤ) at sR
  have SR : S ≤ R := by unfold S; rw [abs_of_pos spos]; exact_mod_cast sR
  have SX : S ≤ X := SR.trans Rle
  have UP : U ≤ P := by
    refine tbound.trans ?_
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (R : ℝ)+1)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ (R : ℝ)+1 from le_add_of_nonneg_left (Nat.cast_nonneg R)) pp.le
  have K0 : 0 ≤ K := by unfold K; positivity
  have Kmul : (K : ℝ)*P ≤ U*B^2+2*S*B := by
    have fact := Int.ediv_mul_le (|t| * (A : ℤ)^2+2*|s| * (A : ℤ))
      (show (p : ℤ) ≠ 0 by exact_mod_cast p0.ne')
    change K*(p : ℤ) ≤ |t| * (A : ℤ)^2+2*|s| * (A : ℤ) at fact
    unfold P U B S
    exact_mod_cast fact
  have first : U*B^2 ≤ B*X := by
    calc
      _ ≤ (P/((R : ℝ)+1))*B^2 := mul_le_mul_of_nonneg_right tbound (by positivity)
      _ ≤ (P/X)*B^2 :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left pp.le xp Rplus) (by positivity)
      _ = B*X := by
        rw [div_mul_eq_mul_div]
        symm
        apply (eq_div_iff xp.ne').mpr
        calc
          B*X*X = B*X^2 := by ring
          _ = P*B^2 := by rw [xSq]; ring
  have second : 2*S*B ≤ 2*B*X := by
    calc
      _ ≤ 2*X*B := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left SX (by norm_num)) (zero_le_one.trans b1)
      _ = _ := by ring
  have Kbound : (K : ℝ) ≤ 3*B*X/P := by
    apply (le_div_iff₀ pp).mpr
    exact Kmul.trans ((add_le_add first second).trans_eq (by ring))
  have Kcoarse : (K : ℝ) ≤ 3*P := by
    refine Kbound.trans ?_
    apply (div_le_iff₀ pp).mpr
    exact (mul_le_mul (mul_le_mul_of_nonneg_left bp.le (by norm_num)) xP.le xp.le
      (by positivity)).trans_eq (by ring)
  have cardCap : ((Icc (-K) K).card : ℝ) ≤ 1+6*B*X/P := by
    have cc : ((Icc (-K) K).card : ℤ) = K+1-(-K) :=
      Int.card_Icc_of_le (-K) K (by omega)
    have cc' : ((Icc (-K) K).card : ℝ) = 2*(K : ℝ)+1 := by
      exact_mod_cast (show ((Icc (-K) K).card : ℤ) = 2*K+1 by omega)
    rw [cc']
    calc
      _ ≤ 2*(3*B*X/P)+1 := add_le_add (mul_le_mul_of_nonneg_left Kbound (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
      _ = _ := by ring
  have detCap (k : ℤ) (hk : k ∈ Icc (-K) K) : (s^2+t*k*(p : ℤ)).natAbs ≤ 4*p^3 := by
    have kabs : (↑|k| : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast abs_le.mpr (mem_Icc.mp hk)
    have ss : |(s : ℝ)| ≤ P := by rw [← Int.cast_abs]; exact SX.trans xP.le
    have tt : |(t : ℝ)| ≤ P := by rw [← Int.cast_abs]; exact UP
    have kk : |(k : ℝ)| ≤ 3*P := by rw [← Int.cast_abs]; exact kabs.trans Kcoarse
    have main : |(s : ℝ)^2+(t : ℝ)*(k : ℝ)*P| ≤ 4*P^3 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_pow,abs_mul,abs_mul,abs_of_pos pp]
      calc
        _ ≤ P^2+(P*(3*P))*P := add_le_add (pow_le_pow_left₀ (abs_nonneg _) ss 2)
          (mul_le_mul_of_nonneg_right (mul_le_mul tt kk (abs_nonneg _) pp.le) pp.le)
        _ = P^2+3*P^3 := by ring
        _ ≤ _ := by
          have powLe : P^2 ≤ P^3 := pow_le_pow_right₀ p1 (by norm_num)
          linarith only [powLe]
    have norm : ((s^2+t*k*(p : ℤ)).natAbs : ℝ) ≤ 4*(p : ℝ)^3 := by
      simpa only [Nat.cast_natAbs,Int.cast_abs,Int.cast_add,Int.cast_pow,Int.cast_mul,Int.cast_natCast,P] using main
    exact_mod_cast norm
  have countR : (count : ℝ) ≤
    2*(∑ k ∈ Icc (-K) K, ((s^2+t*k*(p : ℤ)).natAbs.divisors.card : ℝ)) := by
    exact_mod_cast countBound
  calc
    _ ≤ _ := countR
    _ ≤ 2*(∑ _ ∈ Icc (-K) K, T) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun k hk => divisors _ (detCap k hk)) (by norm_num)
    _ = 2*T*((Icc (-K) K).card : ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left cardCap (by positivity)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_fourth_moment -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical ComplexConjugate Finset

noncomputable section

theorem cyclic_weighted_parseval {p : ℕ} [NeZero p] (g : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖∑ y : ZMod p, g y*ZMod.stdAddChar (x*y)‖^2) =
      (p : ℝ)*(∑ y : ZMod p, ‖g y‖^2) := by
  let H (x : ZMod p) := ∑ y : ZMod p, g y*ZMod.stdAddChar (x*y)
  let G (x y z : ZMod p) := g y*conj (g z)*ZMod.stdAddChar (x*(y-z))
  have expand (x : ZMod p) : ((‖H x‖^2 : ℝ) : ℂ) = ∑ y : ZMod p, ∑ z : ZMod p, G x y z := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    unfold H
    simp only [map_sum,sum_mul_sum,map_mul,conj_stdAddChar]
    refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
    unfold G
    rw [show x*(y-z) = x*y + -(x*z) by ring,AddChar.map_add_eq_mul]
    ring
  have reorder :
      (∑ x : ZMod p, ∑ y : ZMod p, ∑ z : ZMod p, G x y z) =
        ∑ y : ZMod p, ∑ z : ZMod p, ∑ x : ZMod p, G x y z := by
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_comm
  change (∑ x : ZMod p, ‖H x‖^2) = _
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast]
  change Complex.ofRealHom (∑ x : ZMod p, ‖H x‖^2) =
    (p : ℂ)*Complex.ofRealHom (∑ y : ZMod p, ‖g y‖^2)
  rw [map_sum]
  change (∑ x : ZMod p, ((‖H x‖^2 : ℝ) : ℂ)) = _
  simp only [expand,reorder]
  rw [map_sum,mul_sum]
  refine sum_congr rfl fun y _ => ?_
  have every (z : ZMod p) : ∑ x : ZMod p, G x y z =
      if y = z then (p : ℂ)*(g y*conj (g y)) else 0 := by
    unfold G
    rw [← mul_sum,sum_mul_stdAddChar]
    by_cases h : y = z
    · subst z
      simp [mul_comm]
    · simp [h, sub_ne_zero.mpr h]
  simp only [every,sum_ite_eq,mem_univ,ite_true,Complex.mul_conj',map_pow]
  rfl

def reciprocalPairKey (p : ℕ) (i : ℕ × ℕ) : ZMod p := (i.1 : ZMod p)⁻¹+(i.2 : ZMod p)⁻¹

def inverseFrequencySum (p : ℕ) [NeZero p] (I : Finset ℕ) (weight : ℕ → ℂ) (x : ZMod p) : ℂ :=
  ∑ a ∈ I, weight a*ZMod.stdAddChar (x*(a : ZMod p)⁻¹)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_bilinear -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem int_cast_injOn_Ioc_zero {p : ℕ} [NeZero p] :
    Set.InjOn (fun j : ℤ => (j : ZMod p)) ((Ioc (0 : ℤ) (p : ℤ) : Finset ℤ) : Set ℤ) := by
  intro x hx y hy h
  have xr := mem_Ioc.mp (show x ∈ Ioc (0 : ℤ) (p : ℤ) from hx)
  have yr := mem_Ioc.mp (show y ∈ Ioc (0 : ℤ) (p : ℤ) from hy)
  change (x : ZMod p) = (y : ZMod p) at h
  have shifted : ((x-1 : ℤ) : ZMod p) = ((y-1 : ℤ) : ZMod p) := by rw [Int.cast_sub,Int.cast_sub,h]
  have eq := (ZMod.intCast_eq_intCast_iff (x-1) (y-1) p).mp shifted
  change (x-1) % (p : ℤ) = (y-1) % (p : ℤ) at eq
  rw [Int.emod_eq_of_lt (by omega) (by omega),Int.emod_eq_of_lt (by omega) (by omega)] at eq
  omega

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_unit_fibre -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

def inverseUnitCollisionFiber (m A : ℕ) (target : ZMod m) : Finset (ℕ × ℕ) :=
  (inverseCollisionFiber m A target).filter fun i => i.1.Coprime m ∧ i.2.Coprime m

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_frequency_reduced_period -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

def inverseFrequencyPeriod (m : ℕ) (c : ZMod m) : ℕ :=
  m/(m.gcd c.val)

theorem inverse_frequency_period_pos {m : ℕ} [NeZero m] (c : ZMod m) :
    0 < inverseFrequencyPeriod m c := by
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  exact Nat.div_pos (Nat.le_of_dvd m0 (Nat.gcd_dvd_left m c.val)) (Nat.gcd_pos_of_pos_left _ m0)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_fourier_phase_gcd -/
section

namespace GoldbachTypeII13

noncomputable section

theorem gcd_fourier_phase_product_le {m : ℕ} [NeZero m] (h c : ZMod m) :
    m.gcd (-(h*c)).val ≤ m.gcd h.val*m.gcd c.val := by
  let z := -(h*c)
  let d := m.gcd z.val
  let φ := ZMod.castHom (Nat.gcd_dvd_left m z.val) (ZMod d)
  have dm : d ∣ m := Nat.gcd_dvd_left _ _
  have m0 := Nat.pos_of_ne_zero (NeZero.ne m)
  have zero : φ z=0 := by
    rw [← ZMod.natCast_zmod_val z,map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.gcd_dvd_right _ _)
  have val (x : ZMod m) : φ x = (x.val : ZMod d) := by
    have t := congrArg φ (ZMod.natCast_zmod_val x)
    rw [map_natCast] at t
    exact t.symm
  have dvd : d ∣ h.val*c.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    change φ (-(h*c)) = 0 at zero
    rw [map_neg,map_mul,val h,val c] at zero
    rw [Nat.cast_mul]
    exact neg_eq_zero.mp zero
  have split : d ∣ d.gcd h.val*d.gcd c.val := by
    simpa only [Nat.gcd_comm] using (Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr dvd)
  have go (a : ℕ) : d.gcd a ∣ m.gcd a :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left d a).trans dm) (Nat.gcd_dvd_right d a)
  have out : d ∣ m.gcd h.val*m.gcd c.val := split.trans (Nat.mul_dvd_mul (go h.val) (go c.val))
  exact Nat.le_of_dvd (mul_pos (Nat.gcd_pos_of_pos_left _ m0) (Nat.gcd_pos_of_pos_left _ m0)) out

theorem gcd_val_nat_cast_le_gcd {m : ℕ} [NeZero m] (n : ℕ) :
    m.gcd (n : ZMod m).val ≤ m.gcd n := by
  let c := (n : ZMod m)
  let d := m.gcd c.val
  let φ := ZMod.castHom (Nat.gcd_dvd_left m c.val) (ZMod d)
  have h : φ c=0 := by
    rw [← ZMod.natCast_zmod_val c,map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.gcd_dvd_right _ _)
  have hn : d ∣ n := by
    unfold c at h
    rw [map_natCast] at h
    exact (ZMod.natCast_eq_zero_iff _ _).mp h
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne m)))
    (Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hn)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_inverse_ramp_bound -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem norm_gated_inverse_ramp_le_weil {m A : ℕ} [NeZero m] (c : ZMod m)
    (I : Finset ℕ) (base : I ⊆ Icc 1 A) (cop : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ) {L R : ℤ} (span : R-L ≤ m)
    {T : ℝ} (T0 : 0 ≤ T) (weights : ∀ i ∈ I, ‖α i‖ ≤ T)
    (s : ℕ → ZMod m) (t : ℤ → ZMod m) (z : ℕ → ℤ → ℤ)
    (phase : ∀ i j, (z i j : ZMod m) = c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹-s i-t j) :
    let J := intIntervalModUnits m L R
    let Y := ∑ j ∈ J, ‖β j‖^2
    let D := Real.sqrt (Y*((#J : ℝ)*(∑ i ∈ I, ‖α i‖^2)))
    let E := Real.sqrt (Y*(2*(A : ℝ)^2*T^2*(m.divisors.card : ℝ)*weilReciprocalBudget m)*
      Real.sqrt (m.gcd c.val))
    ‖gatedBilinearSum I J α β lo hi (fun i j => (centeredInverseRamp m (z i j-1) : ℂ))‖ ≤
      (1+Real.log m)*D+((m.divisors.card : ℝ)*(1+Real.log m))*E := by
  dsimp only
  let J := intIntervalModUnits m L R
  let Y := ∑ j ∈ J, ‖β j‖^2
  let V := (#J : ℝ)*(∑ i ∈ I, ‖α i‖^2)
  let W := 2*(A : ℝ)^2*T^2*(m.divisors.card : ℝ)*weilReciprocalBudget m
  let D := Real.sqrt (Y*V)
  let E := Real.sqrt (Y*W*Real.sqrt (m.gcd c.val))
  let f (i : ℕ) (j : ℤ) := c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹
  have m0 : 0 < m := NeZero.pos m
  have Y0 : 0 ≤ Y := by unfold Y; positivity
  have V0 : 0 ≤ V := by unfold V; positivity
  have W0 : 0 ≤ W := by
    have := weil_reciprocal_budget_nonneg m0
    unfold W
    positivity
  have D0 : 0 ≤ D := Real.sqrt_nonneg _
  have E0 : 0 ≤ E := Real.sqrt_nonneg _
  have dSq : D^2=Y*V := Real.sq_sqrt (mul_nonneg Y0 V0)
  have eSq : E^2=Y*W*Real.sqrt (m.gcd c.val) :=
    Real.sq_sqrt (mul_nonneg (mul_nonneg Y0 W0) (Real.sqrt_nonneg _))
  have frequency (h : ZMod m) (_ : h ≠ 0) :
      ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (-(h*(f i j-s i-t j))))‖ ≤ D+E*(m.gcd h.val : ℝ) := by
    let H := (m.gcd h.val : ℝ)
    let F := gatedBilinearSum I J α β lo hi
      (fun i j => ZMod.stdAddChar (-(h*(f i j-s i-t j))))
    let u (i : ℕ) := α i*ZMod.stdAddChar (h*s i)
    let v (j : ℤ) := β j*ZMod.stdAddChar (h*t j)
    have uNorm (i : ℕ) : ‖u i‖=‖α i‖ := by simp only [u,norm_mul,norm_stdAddChar_eq_one,mul_one]
    have vNorm (j : ℤ) : ‖v j‖=‖β j‖ := by simp only [v,norm_mul,norm_stdAddChar_eq_one,mul_one]
    have phaseEq (i : ℕ) (j : ℤ) : -(h*f i j) = (-(h*c))*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹ := by
      unfold f
      ring
    have main : ‖F‖^2 ≤ Y*(V+W*Real.sqrt (m.gcd (-(h*c)).val)) := by
      unfold F
      rw [gated_phase_shift_eq_twisted_weights]
      simp_rw [phaseEq]
      have bound := norm_gated_weil_inverse_sq_le (-(h*c)) I base cop u v lo hi span T0
        (fun i hi => (uNorm i).trans_le (weights i hi))
      dsimp only at bound
      simp only [uNorm,vNorm] at bound
      exact bound
    have H1 : 1 ≤ H := by
      unfold H
      exact_mod_cast (show 1 ≤ m.gcd h.val from Nat.gcd_pos_of_pos_left _ m0)
    have H0 : 0 ≤ H := zero_le_one.trans H1
    have gcdH : Real.sqrt (m.gcd (-(h*c)).val) ≤ Real.sqrt (m.gcd c.val)*H^2 := by
      have raw : (m.gcd (-(h*c)).val : ℝ) ≤ (m.gcd c.val : ℝ)*H := by
        unfold H
        have finite : m.gcd (-(h*c)).val ≤ m.gcd c.val*m.gcd h.val :=
          (gcd_fourier_phase_product_le h c).trans_eq (Nat.mul_comm _ _)
        exact_mod_cast finite
      calc
        _ ≤ Real.sqrt ((m.gcd c.val : ℝ)*H) := Real.sqrt_le_sqrt raw
        _ = Real.sqrt (m.gcd c.val)*Real.sqrt H := by rw [Real.sqrt_mul (by positivity)]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((Real.sqrt_le_self_iff.mpr (Or.inr H1)).trans (by rw [pow_two]; nlinarith only [mul_nonneg H0 (sub_nonneg.mpr H1)]))
          (Real.sqrt_nonneg _)
    have scaled : Y*(V+W*(Real.sqrt (m.gcd c.val)*H^2)) = D^2+(E*H)^2 := by
      rw [mul_pow,dSq,eSq]
      ring
    have cross : 0 ≤ D*(E*H) := mul_nonneg D0 (mul_nonneg E0 H0)
    have squared : ‖F‖^2 ≤ (D+E*H)^2 := by
      calc
        _ ≤ Y*(V+W*Real.sqrt (m.gcd (-(h*c)).val)) := main
        _ ≤ Y*(V+W*(Real.sqrt (m.gcd c.val)*H^2)) :=
          mul_le_mul_of_nonneg_left (add_le_add (le_refl V) (mul_le_mul_of_nonneg_left gcdH W0)) Y0
        _ = _ := scaled
        _ ≤ _ := by nlinarith only [cross]
    calc
      ‖F‖ = Real.sqrt (‖F‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((D+E*H)^2) := Real.sqrt_le_sqrt squared
      _ = _ := Real.sqrt_sq (add_nonneg D0 (mul_nonneg E0 H0))
  have weight0 : 0 ≤ 1+Real.log (m : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m from m0)))
  have bound0 : 0 ≤ (1+Real.log m)*D+((m.divisors.card : ℝ)*(1+Real.log m))*E := by positivity
  exact norm_gated_inverse_ramp_le_of_prefix_bounds m0 I J α β lo hi z bound0 (fun k _ => by
    have h := norm_gated_interval_residue_le_of_frequency_bounds I J α β lo hi
      (fun i j => f i j-s i-t j) (show (0 : ℤ) ≤ (k : ℤ)+1 by positivity) D0 E0 frequency
    simpa only [phase,f] using h)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_ramp_scales -/
section

namespace GoldbachTypeII13

noncomputable section

theorem weil_inverse_ramp_scales {N M A S D G x : ℝ}
    (N1 : 1 ≤ N) (M0 : 0 ≤ M) (A0 : 0 ≤ A) (S0 : 0 ≤ S)
    (D1 : 1 ≤ D) (G0 : 0 ≤ G)
    (xLo : 31/512 ≤ x) (xHi : x ≤ 31/256)
    (aCap : A ≤ N^(x+17/4096)) (smCap : S*M*D^2 ≤ 2*N^(1+3/8192-x))
    (mCap : M ≤ N^(37/64 : ℝ)) (gCap : G ≤ N^(1/2048 : ℝ)) :
    M*D*(S*Real.sqrt A+A*Real.sqrt S*Real.sqrt (Real.sqrt M*Real.sqrt G)) ≤
      4*N^(1023/1024 : ℝ) := by
  have N0 : 0 < N := zero_lt_one.trans_le N1
  have D0 : 0 ≤ D := zero_le_one.trans D1
  have sqrtPow (t : ℝ) : Real.sqrt (N^t) = N^(t/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul N0.le]
    congr 1
    ring
  have sqrtA : Real.sqrt A ≤ N^((x+17/4096)/2) := by
    rw [← sqrtPow]
    exact Real.sqrt_le_sqrt aCap
  have diag : M*D*S*Real.sqrt A ≤ 2*N^(1023/1024 : ℝ) := by
    have factor : M*D*S ≤ S*M*D^2 := by
      have Dsq : D ≤ D^2 := by
        rw [pow_two]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left D1 D0
      calc
        _ = (S*M)*D := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left Dsq (mul_nonneg S0 M0)
    calc
      _ ≤ (2*N^(1+3/8192-x))*N^((x+17/4096)/2) :=
        mul_le_mul (factor.trans smCap) sqrtA (Real.sqrt_nonneg _) (by positivity)
      _ = 2*N^(1+3/8192-x+(x+17/4096)/2) := by rw [mul_assoc,← Real.rpow_add N0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le N1 (by linarith only [xLo])) (by norm_num)
  have rootProduct : M*D*A*Real.sqrt S*Real.sqrt (Real.sqrt M*Real.sqrt G) =
      A*Real.sqrt (S*M*D^2)*(M^(3/4 : ℝ))*(G^(1/4 : ℝ)) := by
    have quarter {y : ℝ} (hy : 0 ≤ y) : Real.sqrt (Real.sqrt y) = y^(1/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hy]
      norm_num
    have mThree : Real.sqrt M*M^(3/4 : ℝ) = M*M^(1/4 : ℝ) := by
      calc
        _ = M^(1/2 : ℝ)*M^(3/4 : ℝ) := by rw [Real.sqrt_eq_rpow]
        _ = M^((1:ℝ)/2+3/4) := by
          rw [Real.rpow_add_of_nonneg M0 (by norm_num) (by norm_num)]
        _ = M^((1:ℝ)+1/4) := by congr 1 <;> norm_num
        _ = _ := by rw [Real.rpow_add_of_nonneg M0 (by norm_num) (by norm_num),Real.rpow_one]
    rw [Real.sqrt_mul (mul_nonneg S0 M0),Real.sqrt_mul S0,Real.sqrt_sq D0,
      Real.sqrt_mul (Real.sqrt_nonneg M),quarter M0,quarter G0]
    calc
      _ = A*Real.sqrt S*D*(M*M^(1/4 : ℝ))*G^(1/4 : ℝ) := by ring
      _ = _ := by rw [← mThree]; ring
  have mp : M^(3/4 : ℝ) ≤ N^(3*(37/64)/4 : ℝ) := by
    calc
      _ ≤ (N^(37/64 : ℝ))^(3/4 : ℝ) :=
        Real.rpow_le_rpow M0 mCap (by norm_num)
      _ = _ := by rw [← Real.rpow_mul N0.le]; ring_nf
  have gp : G^(1/4 : ℝ) ≤ N^(1/(2048*4) : ℝ) := by
    calc
      _ ≤ (N^(1/2048 : ℝ))^(1/4 : ℝ) :=
        Real.rpow_le_rpow G0 gCap (by norm_num)
      _ = _ := by rw [← Real.rpow_mul N0.le]; ring_nf
  have sqrtP : Real.sqrt (S*M*D^2) ≤ 2*N^((1+3/8192-x)/2) := by
    have two : Real.sqrt 2 ≤ (2 : ℝ) := Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))
    calc
      _ ≤ Real.sqrt (2*N^(1+3/8192-x)) := Real.sqrt_le_sqrt smCap
      _ = Real.sqrt 2*N^((1+3/8192-x)/2) := by rw [Real.sqrt_mul (by norm_num),sqrtPow]
      _ ≤ _ := mul_le_mul_of_nonneg_right two (by positivity)
  have off : M*D*A*Real.sqrt S*Real.sqrt (Real.sqrt M*Real.sqrt G) ≤ 2*N^(1023/1024 : ℝ) := by
    rw [rootProduct]
    calc
      _ ≤ N^(x+17/4096)*(2*N^((1+3/8192-x)/2))*
          N^(3*(37/64)/4 : ℝ)*N^(1/(2048*4) : ℝ) := by
        gcongr
      _ = 2*N^(x+17/4096+(1+3/8192-x)/2+3*(37/64)/4+1/(2048*4)) := by
        calc
          _ = 2*(N^(x+17/4096)*N^((1+3/8192-x)/2)*
            N^(3*(37/64)/4 : ℝ)*N^(1/(2048*4) : ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add N0,← Real.rpow_add N0,← Real.rpow_add N0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le N1 (by linarith only [xHi])) (by norm_num)
  calc
    _ = M*D*S*Real.sqrt A+M*D*A*Real.sqrt S*Real.sqrt (Real.sqrt M*Real.sqrt G) := by ring
    _ ≤ 2*N^(1023/1024 : ℝ)+2*N^(1023/1024 : ℝ) := add_le_add diag off
    _ = _ := by ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_ramp_row_scale -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem norm_gated_inverse_ramp_le_weil_row {m A S : ℕ} [NeZero m] (c : ZMod m)
    (I : Finset ℕ) (base : I ⊆ Icc 1 A) (cop : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ) (span : S ≤ m)
    {T L : ℝ} (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (leftWeights : ∀ i ∈ I, ‖α i‖ ≤ T)
    (rightWeights : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T*L)
    (tau : (m.divisors.card : ℝ) ≤ T) (log : 1+Real.log m ≤ L)
    (s : ℕ → ZMod m) (t : ℤ → ZMod m) (z : ℕ → ℤ → ℤ)
    (phase : ∀ i j, (z i j : ZMod m) = c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹-s i-t j) :
    ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun i j => (centeredInverseRamp m (z i j-1) : ℂ))‖ ≤
      3*T^4*L^3*((S : ℝ)*Real.sqrt A+(A : ℝ)*Real.sqrt S*
        Real.sqrt (Real.sqrt m*Real.sqrt (m.gcd c.val))) := by
  let M := (m : ℝ)
  let a := (A : ℝ)
  let q := (S : ℝ)
  let G := Real.sqrt (m.gcd c.val)
  let J := intIntervalModUnits m 0 S
  let Y := ∑ j ∈ J, ‖β j‖^2
  let V := (#J : ℝ)*(∑ i ∈ I, ‖α i‖^2)
  let W := 2*a^2*T^2*(m.divisors.card : ℝ)*weilReciprocalBudget m
  let D := Real.sqrt (Y*V)
  let E := Real.sqrt (Y*W*G)
  have T0 : 0 ≤ T := zero_le_one.trans T1
  have L0 : 0 ≤ L := zero_le_one.trans L1
  have G0 : 0 ≤ G := Real.sqrt_nonneg _
  have Y0 : 0 ≤ Y := by unfold Y; positivity
  have V0 : 0 ≤ V := by unfold V; positivity
  have W0 : 0 ≤ W := by
    have := weil_reciprocal_budget_nonneg (NeZero.pos m)
    unfold W
    positivity
  have sp : (S : ℤ)-0 ≤ (m : ℤ) := by
    rw [sub_zero]
    exact_mod_cast span
  have cardA : (#I : ℝ) ≤ a := by
    change (#I : ℝ) ≤ (A : ℝ)
    exact_mod_cast (card_le_card base).trans_eq (by simp [Nat.card_Icc] : #(Icc 1 A) = A)
  have cardS : (#J : ℝ) ≤ q := by
    have sub : J ⊆ Ioc 0 (S : ℤ) := by
      intro j hj
      have data : j ∈ Ioc 0 (S : ℤ) ∧ IsUnit (j : ZMod m) := by
        simpa only [J,intIntervalModUnits,mem_filter] using hj
      exact data.1
    have h : #J ≤ S := (card_le_card sub).trans_eq (by rw [Int.card_Ioc,sub_zero,Int.toNat_natCast])
    change (#J : ℝ) ≤ (S : ℝ)
    exact_mod_cast h
  have rightSq : Y ≤ q*(T*L)^2 := by
    calc
      _ ≤ ∑ _ ∈ J, (T*L)^2 := sum_le_sum fun j hj =>
        pow_le_pow_left₀ (norm_nonneg _) (rightWeights j hj) 2
      _ = (#J : ℝ)*(T*L)^2 := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right cardS (sq_nonneg _)
  have leftSq : (∑ i ∈ I, ‖α i‖^2) ≤ a*T^2 := by
    calc
      _ ≤ ∑ _ ∈ I, T^2 := sum_le_sum fun i hi =>
        pow_le_pow_left₀ (norm_nonneg _) (leftWeights i hi) 2
      _ = (#I : ℝ)*T^2 := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right cardA (sq_nonneg _)
  have Vtop : V ≤ q*a*T^2 := by
    unfold V
    rw [mul_assoc]
    exact mul_le_mul cardS leftSq (by positivity) (by positivity)
  have Wtop : W ≤ 6*a^2*T^4*L*Real.sqrt M := by
    have log3 : 3+2*Real.log m ≤ 3*L := by linarith only [log,L1]
    have log0 : 0 ≤ 3+2*Real.log (m : ℝ) := by
      have h : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.pos m : 1 ≤ m)
      linarith only [Real.log_nonneg h]
    unfold W weilReciprocalBudget
    calc
      _ ≤ 2*a^2*T^2*T*(3*L*T*Real.sqrt M) := by gcongr
      _ = _ := by ring
  have Dtop : D ≤ (q*T^2*L)*Real.sqrt a := by
    unfold D
    calc
      _ ≤ Real.sqrt ((q*(T*L)^2)*(q*a*T^2)) :=
        Real.sqrt_le_sqrt (mul_le_mul rightSq Vtop V0 (by positivity))
      _ = _ := by
        rw [show (q*(T*L)^2)*(q*a*T^2) = (q*T^2*L)^2*a by ring,
          Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
  have Etop : E ≤ (3*a*T^3*L^2)*Real.sqrt q*Real.sqrt (Real.sqrt M*G) := by
    have coeff : (6 : ℝ)*L^3 ≤ 9*L^4 := by
      calc
        _ ≤ 9*L^3 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ L1 (by decide)) (by norm_num)
    have rad : (q*(T*L)^2)*(6*a^2*T^4*L*Real.sqrt M)*G ≤
        ((3*a*T^3*L^2)^2*q)*(Real.sqrt M*G) := by
      calc
        _ = (6*L^3)*(q*a^2*T^6*(Real.sqrt M*G)) := by ring
        _ ≤ (9*L^4)*(q*a^2*T^6*(Real.sqrt M*G)) := mul_le_mul_of_nonneg_right coeff (by positivity)
        _ = _ := by ring
    unfold E
    calc
      _ ≤ Real.sqrt ((q*(T*L)^2)*(6*a^2*T^4*L*Real.sqrt M)*G) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (mul_le_mul rightSq Wtop W0 (by positivity)) G0)
      _ ≤ Real.sqrt (((3*a*T^3*L^2)^2*q)*(Real.sqrt M*G)) := Real.sqrt_le_sqrt rad
      _ = _ := by rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
  have dCoeff : T^2*L^2 ≤ 3*T^4*L^3 := by
    have pT : T^2 ≤ T^4 := pow_le_pow_right₀ T1 (by decide)
    have pL : L^2 ≤ L^3 := pow_le_pow_right₀ L1 (by decide)
    calc
      _ ≤ T^4*L^3 := mul_le_mul pT pL (by positivity) (by positivity)
      _ ≤ _ := by nlinarith only [show 0 ≤ T^4*L^3 by positivity]
  have D0 : 0 ≤ D := Real.sqrt_nonneg _
  have E0 : 0 ≤ E := Real.sqrt_nonneg _
  have log0 : 0 ≤ 1+Real.log (m : ℝ) := by
    have h : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.pos m : 1 ≤ m)
    linarith only [Real.log_nonneg h]
  calc
    _ ≤ (1+Real.log m)*D+((m.divisors.card : ℝ)*(1+Real.log m))*E :=
      norm_gated_inverse_ramp_le_weil c I base cop α β lo hi sp T0 leftWeights s t z phase
    _ ≤ L*((q*T^2*L)*Real.sqrt a)+(T*L)*((3*a*T^3*L^2)*Real.sqrt q*Real.sqrt (Real.sqrt M*G)) := by
      exact add_le_add
        (mul_le_mul log Dtop D0 L0)
        (mul_le_mul (mul_le_mul tau log log0 T0) Etop E0 (by positivity))
    _ = (T^2*L^2)*(q*Real.sqrt a)+(3*T^4*L^3)*(a*Real.sqrt q*Real.sqrt (Real.sqrt M*G)) := by ring
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right dCoeff (by positivity)) (le_refl _)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_small_composite_fibre -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

private theorem inverse_unit_nat_cast_injective {m a b : ℕ}
    (ha : a < m) (hb : b < m) (au : IsUnit (a : ZMod m)) (bu : IsUnit (b : ZMod m))
    (eq : (a : ZMod m)⁻¹ = (b : ZMod m)⁻¹) : a=b := by
  have h : (a : ZMod m)=(b : ZMod m) := calc
    _ = ((b : ZMod m)⁻¹*(b : ZMod m))*(a : ZMod m) := by rw [ZMod.inv_mul_of_unit _ bu,one_mul]
    _ = ((a : ZMod m)⁻¹*(a : ZMod m))*(b : ZMod m) := by rw [← eq]; ring
    _ = _ := by rw [ZMod.inv_mul_of_unit _ au,one_mul]
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt ha,ZMod.val_natCast_of_lt hb] at h'

theorem inverse_unit_fibre_le_of_nonzero_dirichlet_coefficient {m A : ℕ} [NeZero m]
    (A0 : 0 < A) (Am : A < m) (target : ZMod m)
    {s t : ℤ} (sPos : 0 < s) (sR : s ≤ (⌊Real.sqrt ((m : ℝ)*(A : ℝ))⌋₊ : ℕ))
    (tBound : (↑|t| : ℝ) ≤ (m : ℝ)/(⌊Real.sqrt ((m : ℝ)*(A : ℝ))⌋₊+1 : ℝ))
    (cong : (t : ZMod m) = (s : ZMod m)*target) (t0 : t ≠ 0)
    {T : ℝ} (T0 : 0 ≤ T) (divisors : ∀ k ≤ 4*m^3, (k.divisors.card : ℝ) ≤ T) :
    ((inverseUnitCollisionFiber m A target).card : ℝ) ≤ 2+inverseFibreBudget m A T := by
  let X := inverseUnitCollisionFiber m A target
  have uData (i : ℕ × ℕ) (hi : i ∈ X) :
      i ∈ Icc 1 A ×ˢ Icc 1 A ∧ reciprocalPairKey m i = target ∧
        IsUnit (i.1 : ZMod m) ∧ IsUnit (i.2 : ZMod m) := by
    obtain ⟨hh,cc,dd⟩ := mem_filter.mp hi
    obtain ⟨ranges,eq⟩ := mem_filter.mp hh
    exact ⟨ranges,eq,(ZMod.isUnit_iff_coprime _ _).mpr cc,(ZMod.isUnit_iff_coprime _ _).mpr dd⟩
  let F := X.filter (fun i => t*(i.1 : ℤ) ≠ s ∧ t*(i.2 : ℤ) ≠ s)
  let L := X.filter (fun i => t*(i.1 : ℤ) = s)
  let U := X.filter (fun i => t*(i.2 : ℤ) = s)
  have shift (a b : ℕ) (ha : t*(a : ℤ)=s) (hb : t*(b : ℤ)=s) : a=b := by
    have z := mul_left_cancel₀ t0 (ha.trans hb.symm)
    exact_mod_cast z
  have fst_eq (a b : ℕ × ℕ) (ha : a ∈ X) (hb : b ∈ X) (eq : a.1=b.1) : a=b := by
    obtain ⟨ra,hka,_,ua⟩ := uData a ha
    obtain ⟨rb,hkb,_,ub⟩ := uData b hb
    have hh := hka.trans hkb.symm
    unfold reciprocalPairKey at hh
    rw [eq] at hh
    have same := add_left_cancel hh
    exact Prod.ext eq (inverse_unit_nat_cast_injective
      ((mem_Icc.mp (mem_product.mp ra).2).2.trans_lt Am) ((mem_Icc.mp (mem_product.mp rb).2).2.trans_lt Am) ua ub same)
  have snd_eq (a b : ℕ × ℕ) (ha : a ∈ X) (hb : b ∈ X) (eq : a.2=b.2) : a=b := by
    obtain ⟨ra,hka,ua,_⟩ := uData a ha
    obtain ⟨rb,hkb,ub,_⟩ := uData b hb
    have hh := hka.trans hkb.symm
    unfold reciprocalPairKey at hh
    rw [eq] at hh
    have same := add_right_cancel hh
    exact Prod.ext (inverse_unit_nat_cast_injective
      ((mem_Icc.mp (mem_product.mp ra).1).2.trans_lt Am) ((mem_Icc.mp (mem_product.mp rb).1).2.trans_lt Am) ua ub same) eq
  have lSize : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    exact fst_eq a b (mem_filter.mp ha).1 (mem_filter.mp hb).1 (shift a.1 b.1 (mem_filter.mp ha).2 (mem_filter.mp hb).2)
  have uSize : U.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    exact snd_eq a b (mem_filter.mp ha).1 (mem_filter.mp hb).1 (shift a.2 b.2 (mem_filter.mp ha).2 (mem_filter.mp hb).2)
  have cover : X ⊆ F ∪ L ∪ U := by
    intro i hi
    by_cases a : t*(i.1 : ℤ)=s
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hi,a⟩))
    · by_cases b : t*(i.2 : ℤ)=s
      · exact mem_union_right _ (mem_filter.mpr ⟨hi,b⟩)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hi,a,b⟩))
  have total : X.card ≤ F.card+2 :=
    (card_le_card cover).trans ((card_union_le _ _).trans (by
      have d := card_union_le F L
      omega))
  have fCount := reciprocal_card_le_of_nonzero_determinant_cover m A (X := F) t0
    (fun i hi => (uData i (mem_filter.mp hi).1).1) (by
      intro i hi
      obtain ⟨sub,fa,fb⟩ := mem_filter.mp hi
      obtain ⟨_,_,ua,ub⟩ := uData i sub
      obtain ⟨k,ks,eq⟩ := reciprocal_fibre_pair_factorization_of_units cong (mem_filter.mp sub).1 ua ub
      exact ⟨k,ks,fun no => (mul_ne_zero (sub_ne_zero.mpr fa) (sub_ne_zero.mpr fb)) (eq.trans no),eq⟩)
  have size := reciprocal_count_le_of_small_coefficients A0 Am sPos sR tBound fCount T0 divisors
  have trans : (X.card : ℝ) ≤ (F.card : ℝ)+2 := by exact_mod_cast total
  exact trans.trans ((add_le_add_left size 2).trans_eq (by ring))


theorem inverse_unit_fibre_card_le_left_size {m A : ℕ} (Am : A < m) (target : ZMod m) :
    (inverseUnitCollisionFiber m A target).card ≤ A := by
  let X := inverseUnitCollisionFiber m A target
  have maps : Set.MapsTo (Prod.fst : ℕ × ℕ → ℕ) X (↑(Icc 1 A) : Set ℕ) := by
    intro i hi
    exact (mem_product.mp (mem_filter.mp (mem_filter.mp hi).1).1).1
  have inj : Set.InjOn (Prod.fst : ℕ × ℕ → ℕ) X := by
    intro a ha b hb h
    have av := mem_filter.mp ha
    have bv := mem_filter.mp hb
    have ae := mem_filter.mp av.1
    have be := mem_filter.mp bv.1
    have eq := ae.2.trans be.2.symm
    change (a.1 : ZMod m)⁻¹+(a.2 : ZMod m)⁻¹=(b.1 : ZMod m)⁻¹+(b.2 : ZMod m)⁻¹ at eq
    change a.1=b.1 at h
    rw [h] at eq
    exact Prod.ext h (inverse_unit_nat_cast_injective
      ((mem_Icc.mp (mem_product.mp ae.1).2).2.trans_lt Am)
      ((mem_Icc.mp (mem_product.mp be.1).2).2.trans_lt Am)
      ((ZMod.isUnit_iff_coprime _ _).mpr av.2.2) ((ZMod.isUnit_iff_coprime _ _).mpr bv.2.2)
      (add_left_cancel eq))
  exact (card_le_card_of_injOn _ maps inj).trans_eq (by simp [Nat.card_Icc])

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_small_order_mass -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical Finset

noncomputable section

theorem inverse_frequency_period_dvd_of_mul_eq_zero {m : ℕ} [NeZero m]
    (c : ZMod m) {s : ℤ} (h : (s : ZMod m)*c=0) :
    ((inverseFrequencyPeriod m c : ℕ) : ℤ) ∣ s := by
  have natval : (((c.val : ℕ) : ℤ) : ZMod m)=c := by rw [Int.cast_natCast,ZMod.natCast_val,ZMod.cast_id]
  have hEq : (c.val : ℤ)*s ≡ (c.val : ℤ)*0 [ZMOD (m : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mp (by
      simp only [Int.cast_mul,natval,Int.cast_zero,mul_zero]
      rw [mul_comm]
      exact h)
  have m0 : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have e := Int.ModEq.cancel_left_div_gcd m0 hEq
  apply Int.modEq_zero_iff_dvd.mp
  unfold inverseFrequencyPeriod
  rw [Int.natCast_ediv]
  exact e

theorem reciprocal_pair_gcd_dvd_sum {m : ℕ} [NeZero m] (i : ℕ × ℕ)
    (au : IsUnit (i.1 : ZMod m)) (bu : IsUnit (i.2 : ZMod m)) :
    m.gcd (reciprocalPairKey m i).val ∣ i.1+i.2 := by
  let z := reciprocalPairKey m i
  let d := m.gcd z.val
  let φ := ZMod.castHom (Nat.gcd_dvd_left m z.val) (ZMod d)
  have easy : φ z=0 := by
    rw [← ZMod.natCast_zmod_val z,map_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.gcd_dvd_right _ _)
  have val : z*(((i.1*i.2 : ℕ)) : ZMod m)=((i.1+i.2 : ℕ) : ZMod m) := by
    unfold z reciprocalPairKey
    rw [Nat.cast_mul,Nat.cast_add,add_mul,← mul_assoc ((i.1 : ZMod m)⁻¹),ZMod.inv_mul_of_unit _ au,one_mul,
      mul_left_comm ((i.2 : ZMod m)⁻¹),ZMod.inv_mul_of_unit _ bu,mul_one,add_comm]
  have rr := congrArg φ val
  rw [map_mul,easy,zero_mul,map_natCast] at rr
  exact (ZMod.natCast_eq_zero_iff _ _).mp rr.symm

private theorem card_pair_sum_multiple_le {A d : ℕ} (d0 : 0 < d) :
    #((Icc 1 A ×ˢ Icc 1 A).filter (fun i : ℕ × ℕ => d ∣ i.1+i.2)) ≤ A*(2*A/d) := by
  let X := (Icc 1 A ×ˢ Icc 1 A).filter (fun i : ℕ × ℕ => d ∣ i.1+i.2)
  let Y := Icc 1 A ×ˢ Icc 1 (2*A/d)
  have b : #X ≤ #Y := by
    refine card_le_card_of_injOn (fun i : ℕ × ℕ => (i.1,(i.1+i.2)/d)) ?_ ?_
    · intro i hi
      obtain ⟨box,dvd⟩ := mem_filter.mp hi
      obtain ⟨aa,bb⟩ := mem_product.mp box
      have lo : 0 < i.1+i.2 := by have := (mem_Icc.mp aa).1; omega
      have hi : i.1+i.2 ≤ 2*A := by
        have a := (mem_Icc.mp aa).2
        have b := (mem_Icc.mp bb).2
        omega
      exact mem_product.mpr ⟨aa,mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd lo dvd) d0,Nat.div_le_div_right hi⟩⟩
    · intro a ha b hb eq
      have h1 := congrArg (Prod.fst : ℕ × ℕ → ℕ) eq
      have h2 := congrArg (Prod.snd : ℕ × ℕ → ℕ) eq
      change a.1=b.1 at h1
      change (a.1+a.2)/d=(b.1+b.2)/d at h2
      have prod := congrArg (fun k : ℕ => k*d) h2
      rw [Nat.div_mul_cancel (mem_filter.mp ha).2,Nat.div_mul_cancel (mem_filter.mp hb).2] at prod
      exact Prod.ext h1 (by omega)
  exact b.trans_eq (by simp [Y,Nat.card_Icc])

theorem card_inverse_pairs_of_short_period_le {m A R : ℕ} [NeZero m]
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (cop : ∀ a ∈ I, a.Coprime m)
    {T : ℝ} (divCount : (m.divisors.card : ℝ) ≤ T) :
    (#((I ×ˢ I).filter (fun i => inverseFrequencyPeriod m (reciprocalPairKey m i) ≤ R)) : ℝ) ≤
      2*T*(A : ℝ)^2*(R : ℝ)/(m : ℝ) := by
  let Bad := (I ×ˢ I).filter (fun i => inverseFrequencyPeriod m (reciprocalPairKey m i) ≤ R)
  let J := m.divisors.filter (fun d => m/d≤R)
  let F (d : ℕ) := (Icc 1 A ×ˢ Icc 1 A).filter (fun i : ℕ × ℕ => d ∣ i.1+i.2)
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have mp : (0 : ℝ) < m := by exact_mod_cast m0
  have cover : Bad ⊆ J.biUnion F := by
    intro i hi
    let z := reciprocalPairKey m i
    let d := m.gcd z.val
    obtain ⟨pair,rank⟩ := mem_filter.mp hi
    obtain ⟨ha,hb⟩ := mem_product.mp pair
    have dm : d ∣ m := Nat.gcd_dvd_left _ _
    have rel : d ∣ i.1+i.2 := reciprocal_pair_gcd_dvd_sum i
      ((ZMod.isUnit_iff_coprime _ _).mpr (cop _ ha)) ((ZMod.isUnit_iff_coprime _ _).mpr (cop _ hb))
    exact mem_biUnion.mpr ⟨d,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dm,m0.ne'⟩,rank⟩,
      mem_filter.mpr ⟨mem_product.mpr ⟨Icap ha,Icap hb⟩,rel⟩⟩
  have each (d : ℕ) (hd : d ∈ J) : ((F d).card : ℝ) ≤ 2*(A : ℝ)^2*(R : ℝ)/(m : ℝ) := by
    obtain ⟨base,hR⟩ := mem_filter.mp hd
    have dm := (Nat.mem_divisors.mp base).1
    have d0 : 0 < d := Nat.pos_of_dvd_of_pos dm m0
    have dp : (0 : ℝ) < d := by exact_mod_cast d0
    have hd' : m ≤ R*d := by
      rw [← Nat.div_mul_cancel dm]
      exact Nat.mul_le_mul_right d hR
    have inv : 1/(d : ℝ) ≤ (R : ℝ)/(m : ℝ) :=
      (div_le_div_iff₀ dp mp).mpr (by simpa only [one_mul] using (by exact_mod_cast hd' : (m : ℝ) ≤ (R : ℝ)*(d : ℝ)))
    calc
      _ ≤ (A : ℝ)*((2*A/d : ℕ) : ℝ) := by exact_mod_cast card_pair_sum_multiple_le (A := A) d0
      _ ≤ (A : ℝ)*(2*(A : ℝ)/(d : ℝ)) := mul_le_mul_of_nonneg_left
        ((le_div_iff₀ dp).mpr (by exact_mod_cast Nat.div_mul_le_self (2*A) d)) (by positivity)
      _ = (2*(A : ℝ)^2)*(1/(d : ℝ)) := by ring
      _ ≤ (2*(A : ℝ)^2)*((R : ℝ)/(m : ℝ)) := mul_le_mul_of_nonneg_left inv (by positivity)
      _ = _ := by ring
  have Jc : (J.card : ℝ) ≤ T :=
    (show (J.card : ℝ) ≤ (m.divisors.card : ℝ) by exact_mod_cast card_le_card (filter_subset _ m.divisors)).trans divCount
  change (Bad.card : ℝ) ≤ _
  calc
    _ ≤ ∑ d ∈ J, ((F d).card : ℝ) := by
      exact_mod_cast (card_le_card cover).trans card_biUnion_le
    _ ≤ ∑ _ ∈ J, 2*(A : ℝ)^2*(R : ℝ)/(m : ℝ) := sum_le_sum each
    _ = (J.card : ℝ)*(2*(A : ℝ)^2*(R : ℝ)/(m : ℝ)) := by simp
    _ ≤ T*(2*(A : ℝ)^2*(R : ℝ)/(m : ℝ)) := mul_le_mul_of_nonneg_right Jc (by positivity)
    _ = _ := by ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_composite_fourth_moment -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical Finset

noncomputable section

theorem inverse_frequency_fourth_moment_le_of_squared_fibre_mass {p A : ℕ} [NeZero p]
    (I : Finset ℕ) (weight : ℕ → ℂ) {W B : ℝ}
    (W0 : 0 ≤ W) (wBound : ∀ a ∈ I, ‖weight a‖ ≤ W)
    (mass : (∑ z : ZMod p, (((I ×ˢ I).filter (fun i => reciprocalPairKey p i = z)).card : ℝ)^2) ≤
      (A : ℝ)^2*(1+B)) :
    (∑ x : ZMod p, ‖inverseFrequencySum p I weight x‖^4) ≤
      (p : ℝ)*(A : ℝ)^2*(1+B)*W^4 := by
  let fibres (z : ZMod p) := (I ×ˢ I).filter (fun i => reciprocalPairKey p i = z)
  let coef (z : ZMod p) : ℂ := ∑ i ∈ fibres z, weight i.1*weight i.2
  let H (x : ZMod p) := inverseFrequencySum p I weight x
  have square (x : ZMod p) : (H x)^2 = ∑ z : ZMod p, coef z*ZMod.stdAddChar (x*z) := by
    unfold H inverseFrequencySum
    rw [pow_two,sum_mul_sum]
    calc
      _ = ∑ i ∈ I ×ˢ I, (weight i.1*weight i.2)*ZMod.stdAddChar (x*reciprocalPairKey p i) := by
        rw [sum_product]
        refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
        simp only [reciprocalPairKey,mul_add,AddChar.map_add_eq_mul]
        ring
      _ = _ := by
        rw [← sum_fiberwise_of_maps_to (fun _ _ => mem_univ (reciprocalPairKey p _))]
        refine sum_congr rfl fun z _ => ?_
        unfold coef
        rw [sum_mul]
        exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
  have size (z : ZMod p) : ‖coef z‖ ≤ ((fibres z).card : ℝ)*W^2 := by
    unfold coef
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ fibres z, W^2 := by
        refine sum_le_sum fun i hi => ?_
        obtain ⟨h1,h2⟩ := mem_product.mp (mem_filter.mp hi).1
        rw [norm_mul,pow_two]
        exact mul_le_mul (wBound _ h1) (wBound _ h2) (norm_nonneg _) W0
      _ = _ := by simp
  have bound_sq (z : ZMod p) :
      ‖coef z‖^2 ≤ (((fibres z).card : ℝ)^2)*W^4 := by
    calc
      _ ≤ (((fibres z).card : ℝ)*W^2)^2 := pow_le_pow_left₀ (norm_nonneg _) (size z) 2
      _ = _ := by ring
  have total : (∑ z : ZMod p, ‖coef z‖^2) ≤ (A : ℝ)^2*(1+B)*W^4 := by
    calc
      _ ≤ ∑ z : ZMod p, (((fibres z).card : ℝ)^2)*W^4 := sum_le_sum fun z _ => bound_sq z
      _ = (∑ z : ZMod p, (((fibres z).card : ℝ)^2))*W^4 := (sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right mass (by positivity)
  change (∑ x : ZMod p, ‖H x‖^4) ≤ _
  calc
    _ = ∑ x : ZMod p, ‖∑ z : ZMod p, coef z*ZMod.stdAddChar (x*z)‖^2 := by
      refine sum_congr rfl fun x _ => ?_
      rw [← square,norm_pow,← pow_mul]
    _ ≤ _ := by
      rw [cyclic_weighted_parseval]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left total (by positivity : (0 : ℝ) ≤ p)

private theorem sum_card_fibres_with_predicate {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : Finset ι) (f : ι → κ) (P : κ → Prop) [DecidablePred P] :
    (∑ z ∈ (univ : Finset κ).filter P, (X.filter (fun i => f i=z)).card) =
      (X.filter (fun i => P (f i))).card := by
  let Y := X.filter fun i => P (f i)
  let Z := (univ : Finset κ).filter P
  have maps : ∀ i ∈ Y, f i ∈ Z := fun i hi => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
  have count : (∑ z ∈ Z, (Y.filter (fun i => f i=z)).card) = Y.card := by
    simp only [card_eq_sum_ones]
    exact sum_fiberwise_of_maps_to maps (fun _ => (1 : ℕ))
  change (∑ z ∈ Z, (X.filter (fun i => f i=z)).card) = Y.card
  rw [← count]
  refine sum_congr rfl fun z hz => ?_
  have eq : X.filter (fun i => f i=z) = Y.filter (fun i => f i=z) := by
    ext i
    unfold Y
    simp only [mem_filter]
    have zP := (mem_filter.mp hz).2
    constructor
    · rintro ⟨ix,eq⟩
      exact ⟨⟨ix,eq.symm ▸ zP⟩,eq⟩
    · intro h
      exact ⟨h.1.1,h.2⟩
  rw [eq]

theorem inverse_frequency_fourth_moment_composite_le {m A : ℕ} [NeZero m]
    (A0 : 0 < A) (Am : A < m) (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (cop : ∀ a ∈ I, a.Coprime m)
    (weight : ℕ → ℂ) {W T : ℝ} (W0 : 0 ≤ W) (wBound : ∀ a ∈ I, ‖weight a‖ ≤ W)
    (T1 : 1 ≤ T) (divisors : ∀ k ≤ 4*m^3, (k.divisors.card : ℝ) ≤ T) :
    (∑ x : ZMod m, ‖inverseFrequencySum m I weight x‖^4) ≤
      (m : ℝ)*(A : ℝ)^2*(1+inverseFibreBudget m A (2*T))*W^4 := by
  let M := (m : ℝ)
  let D := (A : ℝ)
  let X := Real.sqrt (M*D)
  let R := ⌊X⌋₊
  let f := reciprocalPairKey m
  let F (z : ZMod m) := (I ×ˢ I).filter (fun i => f i=z)
  let poor (z : ZMod m) : Prop := inverseFrequencyPeriod m z ≤ R
  let B := (univ : Finset (ZMod m)).filter poor
  let G := (univ : Finset (ZMod m)).filter (fun z => ¬poor z)
  let V := inverseFibreBudget m A T
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have R0 : 0 < R := reciprocal_dirichlet_radius_pos m0 A0
  have T0 := zero_le_one.trans T1
  have V0 : 0 ≤ V := by unfold V inverseFibreBudget; positivity
  have cover (z : ZMod m) : F z ⊆ inverseUnitCollisionFiber m A z := by
    intro i hi
    obtain ⟨box,eq⟩ := mem_filter.mp hi
    obtain ⟨ha,hb⟩ := mem_product.mp box
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨Icap ha,Icap hb⟩,eq⟩,cop _ ha,cop _ hb⟩
  have size (z : ZMod m) : ((F z).card : ℝ) ≤ D := by
    change ((F z).card : ℝ) ≤ (A : ℝ)
    exact_mod_cast (card_le_card (cover z)).trans (inverse_unit_fibre_card_le_left_size Am z)
  have good (z : ZMod m) (hz : z ∈ G) : ((F z).card : ℝ) ≤ 2+V := by
    obtain ⟨s,t,s0,sR,cong,tb⟩ := reciprocal_dirichlet_candidate z R0
    have t0 : t ≠ 0 := by
      intro bad
      rw [bad,Int.cast_zero] at cong
      have dvd := inverse_frequency_period_dvd_of_mul_eq_zero z cong.symm
      have small : inverseFrequencyPeriod m z ≤ R := by
        exact_mod_cast (Int.le_of_dvd s0 dvd).trans sR
      exact (mem_filter.mp hz).2 small
    exact (show ((F z).card : ℝ) ≤ (inverseUnitCollisionFiber m A z).card from by exact_mod_cast card_le_card (cover z)).trans
      (inverse_unit_fibre_le_of_nonzero_dirichlet_coefficient A0 Am z s0 sR tb cong t0 T0 divisors)
  have Jd : (m.divisors.card : ℝ) ≤ T := divisors m (by
    have h : m ≤ m^3 := by simpa only [pow_one] using pow_le_pow_right₀ m0 (show 1 ≤ 3 by decide)
    omega)
  have badSize : (∑ z ∈ B, ((F z).card : ℝ)) ≤ 2*T*D^2*(R : ℝ)/M := by
    have eq := sum_card_fibres_with_predicate (I ×ˢ I) f poor
    unfold B F
    rw [← Nat.cast_sum,eq]
    exact card_inverse_pairs_of_short_period_le I Icap cop Jd
  have totalSize : (∑ z : ZMod m, ((F z).card : ℝ)) ≤ D^2 := by
    have eq : (∑ z : ZMod m, (F z).card) = (I ×ˢ I).card := by
      simp only [card_eq_sum_ones]
      exact sum_fiberwise_of_maps_to (fun i (_ : i ∈ I ×ˢ I) => mem_univ (f i)) (fun _ => (1 : ℕ))
    rw [← Nat.cast_sum,eq,card_product,Nat.cast_mul,pow_two]
    have c : (I.card : ℝ) ≤ D := by change (I.card : ℝ) ≤ A; exact_mod_cast (card_le_card Icap).trans_eq (by simp)
    exact mul_le_mul c c (by positivity) (by positivity)
  have goodSize : (∑ z ∈ G, ((F z).card : ℝ)) ≤ D^2 :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)).trans totalSize
  have scale : 2*T*D*(R : ℝ)/M ≤ 2*T*(D*X/M) := by
    have f : (R : ℝ) ≤ X := Nat.floor_le (by unfold X; positivity)
    calc
      _ ≤ 2*T*D*X/M := by gcongr
      _ = _ := by ring
  have budget : 2+V+2*T*D*(R : ℝ)/M ≤ 1+inverseFibreBudget m A (2*T) := by
    have x0 : 0 ≤ D*X/M := by unfold X; positivity
    have eqV (U : ℝ) : inverseFibreBudget m A U = 2*U*(1+6*(D*X/M)) := by
      unfold inverseFibreBudget D X M
      ring
    unfold V
    rw [eqV,eqV]
    nlinarith only [T1,scale,mul_nonneg T0 x0]
  apply inverse_frequency_fourth_moment_le_of_squared_fibre_mass (A := A) I weight W0 wBound
  change (∑ z : ZMod m, ((F z).card : ℝ)^2) ≤ D^2*(1+inverseFibreBudget m A (2*T))
  rw [← sum_filter_add_sum_filter_not univ poor]
  change (∑ z ∈ B, ((F z).card : ℝ)^2)+(∑ z ∈ G, ((F z).card : ℝ)^2) ≤ _
  have bad : (∑ z ∈ B, ((F z).card : ℝ)^2) ≤ D*(2*T*D^2*(R : ℝ)/M) := by
    calc
      _ ≤ ∑ z ∈ B, D*((F z).card : ℝ) := by
        refine sum_le_sum fun z _ => ?_
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (size z) (by positivity)
      _ = D*∑ z ∈ B, ((F z).card : ℝ) := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left badSize (by positivity)
  have gd : (∑ z ∈ G, ((F z).card : ℝ)^2) ≤ (2+V)*D^2 := by
    calc
      _ ≤ ∑ z ∈ G, (2+V)*((F z).card : ℝ) := by
        refine sum_le_sum fun z hz => ?_
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (good z hz) (by positivity)
      _ = (2+V)*∑ z ∈ G, ((F z).card : ℝ) := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left goodSize (by positivity)
  calc
    _ ≤ D*(2*T*D^2*(R : ℝ)/M)+(2+V)*D^2 := add_le_add bad gd
    _ = D^2*(2+V+2*T*D*(R : ℝ)/M) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left budget (by positivity)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weighted_unit_ratio_product_interval -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem gated_bilinear_sum_eq_pair_sum {ι : Type*}
    (I : Finset ι) (J : Finset ℤ) (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ) (f : ι → ℤ → ℂ) :
    gatedBilinearSum I J α β lo hi f =
      ∑ j ∈ J, ∑ a ∈ I, if lo a < j ∧ j ≤ hi a then α a*β j*f a j else 0 := by
  unfold gatedBilinearSum
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  split_ifs <;> ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_wide_noncommon_rows -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Geometric DyadicMixedB4GcdHarmonic
open scoped Classical

noncomputable section

theorem sum_dividing_rational_bounds_le (n A q : ℕ) (qPos : 0 < q) :
    (∑ u ∈ (Icc 1 A).filter (fun u => q∣u), (n : ℝ)/(u : ℝ)) ≤
      (n : ℝ)/q*(1+Real.log (A : ℝ)) := by
  calc
    _ = (n : ℝ) * ∑ u ∈ (Icc 1 A).filter (fun u => q∣u), (u : ℝ)⁻¹ := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => div_eq_mul_inv _ _
    _ = (n : ℝ)/q * ∑ k ∈ Icc 1 (A/q), (k : ℝ)⁻¹ := by
      rw [sum_inverse_multiples q A qPos]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self A q))
        (fun _ _ _ => by positivity)).trans (sum_inverse_Icc_le A)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_common_wide_mass -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def divisibleStepMass {ι : Type*} (q : ℕ) (I : Finset ι) (g : ι → ℕ) (c : ι → ℂ) (F : ℕ → ℝ) : ℝ :=
  ∑ i ∈ I.filter (fun i => q∣g i), ‖c i‖*F (g i)

private theorem divisible_step_mass_le_of_bound {ι : Type*} (A q : ℕ) (I : Finset ι)
    (g : ι → ℕ) (c : ι → ℂ) (F : ℕ → ℝ) (W : ℝ)
    (steps : ∀ i ∈ I, g i ∈ Icc 1 A)
    (f0 : ∀ u ∈ Icc 1 A, 0 ≤ F u)
    (weights : ∀ u ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => g i=u), ‖c i‖) ≤ W) :
    divisibleStepMass q I g c F ≤ W * ∑ u ∈ (Icc 1 A).filter (fun u => q∣u), F u := by
  let J := I.filter fun i => q∣g i
  let S := (Icc 1 A).filter fun u => q∣u
  have range (i : ι) (hi : i ∈ J) : g i ∈ S :=
    mem_filter.mpr ⟨steps i (mem_filter.mp hi).1,(mem_filter.mp hi).2⟩
  have mass (u : ℕ) (hu : u ∈ S) : (∑ i ∈ J.filter (fun i => g i=u), ‖c i‖) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (weights u (mem_filter.mp hu).1)
  unfold divisibleStepMass
  calc
    _ = ∑ u ∈ S, (∑ i ∈ J.filter (fun i => g i=u), ‖c i‖)*F u := by
      rw [← sum_fiberwise_of_maps_to range (fun i => ‖c i‖*F (g i))]
      refine sum_congr rfl fun u _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
    _ ≤ ∑ u ∈ S,W*F u :=
      sum_le_sum fun u hu => mul_le_mul_of_nonneg_right (mass u hu) (f0 u (mem_filter.mp hu).1)
    _ = _ := (mul_sum ..).symm

theorem divisible_constant_step_mass_le {ι : Type*} (A q : ℕ) (I : Finset ι)
    (g : ι → ℕ) (c : ι → ℂ) {W : ℝ} (W0 : 0 ≤ W)
    (steps : ∀ i ∈ I, g i ∈ Icc 1 A)
    (weights : ∀ u ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => g i=u), ‖c i‖) ≤ W) :
    divisibleStepMass q I g c (fun _ => 1) ≤ W*((A : ℝ)/q) := by
  have eq : (Icc 1 A).filter (fun u => q∣u) = (range (A+1)).filter (fun u => u ≠ 0 ∧ q∣u) := by
    ext u
    simp only [mem_filter,mem_range,mem_Icc]
    omega
  have upper : ((Icc 1 A).filter (fun u => q∣u)).card ≤ A/q := by
    rw [eq, Nat.card_multiples']
  refine (divisible_step_mass_le_of_bound A q I g c (fun _ => 1) W steps (fun _ _ => zero_le_one) weights).trans ?_
  rw [sum_const,nsmul_eq_mul,mul_one]
  exact mul_le_mul_of_nonneg_left ((by exact_mod_cast upper :
    (((Icc 1 A).filter (fun u => q∣u)).card : ℝ) ≤ ((A/q : ℕ) : ℝ)).trans Nat.cast_div_le) W0

theorem divisible_inverse_step_mass_le {ι : Type*} (n A q : ℕ) (qPos : 0 < q) (I : Finset ι)
    (g : ι → ℕ) (c : ι → ℂ) {W : ℝ} (W0 : 0 ≤ W)
    (steps : ∀ i ∈ I, g i ∈ Icc 1 A)
    (weights : ∀ u ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => g i=u), ‖c i‖) ≤ W) :
    divisibleStepMass q I g c (fun u => (n : ℝ)/u) ≤ W*((n : ℝ)/q*(1+Real.log (A : ℝ))) := by
  refine (divisible_step_mass_le_of_bound A q I g c (fun u => (n : ℝ)/u) W steps
    (fun _ _ => by positivity) weights).trans ?_
  exact mul_le_mul_of_nonneg_left (sum_dividing_rational_bounds_le n A q qPos) W0

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_subcritical_medium_residue -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

private theorem sum_weighted_steps_le {ι : Type*} (I : Finset ι) (u : ι → ℕ)
    (w : ι → ℂ) (value : ℕ → ℝ) {A : ℕ} {W : ℝ}
    (steps : ∀ i ∈ I, u i ∈ Icc 1 A) (value0 : ∀ m ∈ Icc 1 A, 0 ≤ value m)
    (mass : ∀ m ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i = m), ‖w i‖) ≤ W) :
    (∑ i ∈ I, ‖w i‖*value (u i)) ≤ W*∑ m ∈ Icc 1 A, value m := by
  rw [← sum_fiberwise_of_maps_to steps, mul_sum]
  refine sum_le_sum fun m hm => ?_
  have equality : (∑ i ∈ I.filter (fun i => u i = m), ‖w i‖*value (u i)) =
      (∑ i ∈ I.filter (fun i => u i = m), ‖w i‖)*value m := by
    rw [sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [(mem_filter.mp hi).2]
  rw [equality]
  exact mul_le_mul_of_nonneg_right (mass m hm) (value0 m hm)

theorem sum_norm_mul_le_of_step_mass {ι : Type*} (I : Finset ι) (step : ι → ℕ)
    (w : ι → ℂ) (val : ℕ → ℝ) {A : ℕ} {W : ℝ}
    (steps : ∀ i ∈ I, step i ∈ Icc 1 A) (nonneg : ∀ m ∈ Icc 1 A, 0 ≤ val m)
    (mass : ∀ m ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => step i = m), ‖w i‖) ≤ W) :
    (∑ i ∈ I, ‖w i‖*val (step i)) ≤ W*∑ m ∈ Icc 1 A, val m :=
  sum_weighted_steps_le I step w val steps nonneg mass

theorem sum_norm_le_of_step_mass {ι : Type*} (I : Finset ι) (step : ι → ℕ)
    (w : ι → ℂ) {A : ℕ} {W : ℝ}
    (steps : ∀ i ∈ I, step i ∈ Icc 1 A)
    (mass : ∀ m ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => step i = m), ‖w i‖) ≤ W) :
    (∑ i ∈ I, ‖w i‖) ≤ W*(A : ℝ) := by
  simpa [Nat.card_Icc] using sum_weighted_steps_le I step w (fun _ => 1) steps
    (fun _ _ => zero_le_one) mass

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_medium_exact_partition -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale
open scoped Classical

noncomputable section

def prefixStepGate (n u v : ℕ) : Prop :=
  maximumStep n^2 < u*v ∧ u.gcd v ≤ maximumStep n

instance (n u v : ℕ) : Decidable (prefixStepGate n u v) :=
  inferInstanceAs (Decidable (maximumStep n^2 < u*v ∧ u.gcd v ≤ maximumStep n))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_medium_proper_prime_power -/
section

namespace GoldbachTypeII13

open Finset Filter Topology ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4PairIntegral DyadicMixedB4TailScale DyadicMixedB4MoebiusGauss
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def properPrimePowersUpTo (A : ℕ) : Finset ℕ :=
  (Icc 1 A).filter (fun b => ¬b.Prime ∧ IsPrimePow b)

theorem card_proper_prime_powers_up_to_le (A : ℕ) :
    #(properPrimePowersUpTo A) ≤ A.sqrt*Nat.log 2 A := by
  let P := Icc 1 A.sqrt ×ˢ Icc 1 (Nat.log 2 A)
  let f (i : ℕ × ℕ) := i.1^i.2
  have cover : properPrimePowersUpTo A ⊆ P.image f := by
    intro b hb
    obtain ⟨range,np,pow⟩ := mem_filter.mp hb
    obtain ⟨p,k,prime,k0,e⟩ := (isPrimePow_nat_iff b).mp pow
    have k2 : 2 ≤ k := by
      by_contra! small
      have k1 : k = 1 := by omega
      have eb : p = b := by simpa only [k1,pow_one] using e
      exact np (eb ▸ prime)
    have prime2 := prime.two_le
    have bound : p^k ≤ A := e ▸ (mem_Icc.mp range).2
    have sqrt : p ≤ A.sqrt := Nat.le_sqrt'.mpr ((pow_le_pow_right₀ prime.one_le k2).trans bound)
    have kCap : k ≤ Nat.log 2 A :=
      Nat.le_log_of_pow_le (by decide) ((Nat.pow_le_pow_left prime2 _).trans bound)
    exact mem_image.mpr ⟨(p,k),mem_product.mpr ⟨mem_Icc.mpr ⟨prime.one_le,sqrt⟩,mem_Icc.mpr ⟨k0,kCap⟩⟩, e⟩
  exact (card_le_card cover).trans ((card_image_le).trans_eq (by simp [P,Nat.card_Icc]))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_prime_hyperbola_saving -/
section

namespace GoldbachTypeII13

open Finset Filter Topology ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4PairIntegral DyadicMixedB4TailScale
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def primeHyperbolaFactorFloor (n k : ℕ) : ℕ := ⌊(n : ℝ)^((k : ℝ)/256)⌋₊

def primeHyperbolaFactorLo (n k : ℕ) : ℕ := max (cutoffU n) (primeHyperbolaFactorFloor n k)

def primeHyperbolaFactorBlock (n k : ℕ) : Finset ℕ :=
  Ioc (primeHyperbolaFactorLo n k) (min (lowCut n) (primeHyperbolaFactorFloor n (k+1)))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_prime_hyperbola_bridge -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical Finset

noncomputable section

theorem prime_hyperbola_factor_blocks_cover {n a : ℕ} (n1 : 1 ≤ n)
    (ha : a ∈ Ioc (cutoffU n) (lowCut n)) :
    ∃! k, k ∈ Icc 16 63 ∧ a ∈ primeHyperbolaFactorBlock n k := by
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have mono : Monotone (primeHyperbolaFactorFloor n) := by
    intro j k le
    have hr : (j : ℝ) ≤ k := by exact_mod_cast le
    exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR
      (div_le_div_of_nonneg_right hr (by norm_num)))
  have Lo : primeHyperbolaFactorFloor n 16 = cutoffU n := by
    unfold primeHyperbolaFactorFloor cutoffU
    norm_num
  have Hi : primeHyperbolaFactorFloor n 64 = lowCut n := by
    unfold primeHyperbolaFactorFloor lowCut
    norm_num
  have upper : a ≤ primeHyperbolaFactorFloor n 64 := Hi.symm ▸ (mem_Ioc.mp ha).2
  have existsBlock : ∃ t : ℕ, a ≤ primeHyperbolaFactorFloor n t := ⟨64,upper⟩
  let t := Nat.find existsBlock
  have tLe : t ≤ 64 := Nat.find_min' existsBlock upper
  have tHi : a ≤ primeHyperbolaFactorFloor n t := Nat.find_spec existsBlock
  have tLo : 16 < t := by
    apply lt_of_not_ge
    intro h
    have impossible := tHi.trans (mono h)
    rw [Lo] at impossible
    exact (not_le_of_gt (mem_Ioc.mp ha).1) impossible
  let k := t-1
  have kn : k+1=t := by unfold k; omega
  have kt : k<t := by unfold k; omega
  have kMem : k ∈ Icc 16 63 := mem_Icc.mpr ⟨by omega,by omega⟩
  have lo : primeHyperbolaFactorFloor n k < a := lt_of_not_ge (Nat.find_min existsBlock kt)
  have hi : a ≤ primeHyperbolaFactorFloor n (k+1) := by rw [kn]; exact tHi
  have inK : a ∈ primeHyperbolaFactorBlock n k :=
    mem_Ioc.mpr ⟨max_lt (mem_Ioc.mp ha).1 lo,le_min (mem_Ioc.mp ha).2 hi⟩
  refine ⟨k,⟨kMem,inK⟩,fun j hj => ?_⟩
  have separate (b c : ℕ) (hb : a ∈ primeHyperbolaFactorBlock n b)
      (hc : a ∈ primeHyperbolaFactorBlock n c) (bc : b < c) : False := by
    have upper : a ≤ primeHyperbolaFactorFloor n (b+1) := (mem_Ioc.mp hb).2.trans (min_le_right _ _)
    have lower : primeHyperbolaFactorFloor n c < a := (le_max_right _ _).trans_lt (mem_Ioc.mp hc).1
    exact (not_le_of_gt lower) (upper.trans (mono bc))
  exact le_antisymm (le_of_not_gt (separate k j inK hj.2)) (le_of_not_gt (separate j k hj.2 inK))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_gcd_product_factor_split -/
section

namespace GoldbachTypeII13

theorem divide_left_product_of_gcd {d a j : ℕ} (d0 : 0 < d) (dvd : d ∣ a*j) :
    let e := a.gcd d
    let k := d/e
    k ∣ j ∧ (a*j)/d = (a/e)*(j/k) := by
  dsimp only
  let e := a.gcd d
  let k := d/e
  let b := a/e
  have e0 : 0 < e := Nat.gcd_pos_of_pos_right a d0
  have ek : e*k=d := Nat.mul_div_cancel' (Nat.gcd_dvd_right a d)
  have eb : e*b=a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a d)
  have reduced : k ∣ b*j := by
    apply (Nat.mul_dvd_mul_iff_left e0).mp
    rw [ek, ← mul_assoc, eb]
    exact dvd
  have cop : k.Coprime b := (Nat.coprime_div_gcd_div_gcd e0).symm
  have kj : k ∣ j := cop.dvd_of_dvd_mul_left reduced
  refine ⟨kj, ?_⟩
  change (a*j)/d = b*(j/k)
  apply Nat.eq_of_mul_eq_mul_right d0
  rw [Nat.div_mul_cancel dvd]
  symm
  calc
    _ = (e*b)*((j/k)*k) := by rw [← ek]; ring
    _ = _ := by rw [eb,Nat.div_mul_cancel kj]

theorem gcd_right_step_dvd_cofactor_when_prime_nondvd {n u p q : ℕ}
    (prime : p.Prime) (ndvd : ¬p ∣ n) (gd : u.gcd (p*q) ∣ n) :
    let d := u.gcd (p*q)
    d ∣ q ∧ (p*q)/d = p*(q/d) ∧ ¬p ∣ n/d := by
  dsimp only
  let d := u.gcd (p*q)
  have notd : ¬p ∣ d := fun dvd => ndvd (dvd.trans gd)
  have cop : d.Coprime p := (prime.coprime_iff_not_dvd.mpr notd).symm
  have dq : d ∣ q := cop.dvd_of_dvd_mul_left (Nat.gcd_dvd_right u (p*q))
  have divN : n/d ∣ n := ⟨d,(Nat.div_mul_cancel gd).symm⟩
  exact ⟨dq,Nat.mul_div_assoc p dq,fun dvd => ndvd (dvd.trans divN)⟩

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_extended_wide_approx -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def extendedWideStepCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(21/32 : ℝ)⌋₊

theorem extended_wide_step_le {n : ℕ} (hn : 0 < n) : extendedWideStepCap n ≤ n :=
  Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_extended_target_divisor_cut -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical Finset

noncomputable section

def targetDivisorCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/128 : ℝ)⌋₊

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_expanded_high_divided_hyperbola_windows -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def expandedHighModulusCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(515/1024 : ℝ)⌋₊

def expandedHyperbolaProductCap (n : ℕ) : ℕ := 2*⌊(n : ℝ)^(513/512 : ℝ)⌋₊

def expandedHighDividedHyperbolaFactors (n m g e k : ℕ) : Finset ℕ :=
  (Ioc (primeHyperbolaFactorLo n k/e) (min (lowCut n) (primeHyperbolaFactorFloor n (k+1))/e)).filter
    (fun a => (e*a).gcd g=e ∧ a.Coprime (m/g))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_short_low_divided_hyperbola_windows -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

set_option maxHeartbeats 2300000

def shortLowModulusCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(133/256 : ℝ)⌋₊

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_moderate_low_divided_hyperbola_windows -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

set_option maxHeartbeats 2300000

def moderateLowDividedHyperbolaCofactorCap (n r₀ g e k : ℕ) : ℕ :=
  (r₀/g)/(primeHyperbolaFactorLo n k/e+1)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_square_multiple_support -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def squareMultipleSupport (n A : ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun m => ∃ h ∈ Ioc A n, h^2 ∣ m)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_thin_high_arithmetic_cuts -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open scoped Classical Finset

noncomputable section

def thinHighProductCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(8191/8192 : ℝ)⌋₊
def thinHighGcdCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/4096 : ℝ)⌋₊
def thinHighLeftDivisorCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/2048 : ℝ)⌋₊

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_expanded_wide_approx -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def expandedWideStepCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(511/768 : ℝ)⌋₊

theorem expanded_wide_step_le {n : ℕ} (hn : 0 < n) : expandedWideStepCap n ≤ n :=
  Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_bounded_outer_left_arithmetic -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open scoped Classical Finset

noncomputable section

def boundedOuterLeftKeptGate (gate : ℕ → ℕ → ℕ → Prop) (n u v : ℕ) : Prop :=
  gate n u v ∧ thinHighProductCap n < u*v ∧
    u.gcd v ≤ thinHighGcdCap n ∧ v.gcd n ≤ targetDivisorCap n

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_high_far_strip_windows_geometry -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def highFarStripProductCap (n : ℕ) : ℕ := 2*⌊(n : ℝ)^(4097/4096 : ℝ)⌋₊

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_far_inner_arithmetic -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def farInnerGate (n u v : ℕ) : Prop :=
  prefixStepGate n u v ∧ highFarStripProductCap n < u*v

def farInnerThinGate (n u v : ℕ) : Prop :=
  boundedOuterLeftKeptGate farInnerGate n u v ∧ u.gcd n ≤ thinHighLeftDivisorCap n

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_moderate_low_divided_hyperbola_bridge -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical Finset

noncomputable section

set_option maxHeartbeats 2200000

def moderateLowDividedHyperbolaLeftItems (n m g e k l₀ r₀ : ℕ) : Finset (ℕ × ℕ) :=
  (bilateralLeftWaveItems n).filter fun i =>
    i.1 ∈ primeHyperbolaFactorBlock n k ∧ (leftBilinearStep i).gcd m = g ∧ i.1.gcd g = e ∧
      l₀ < leftBilinearStep i ∧ leftBilinearStep i ≤ r₀

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_wider_low_far_window -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

set_option maxHeartbeats 2300000

def widerLowFarModulusCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(535/1024 : ℝ)⌋₊

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_moderate_low_divided_hyperbola_saving -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

abbrev ModerateLowBounds := ℕ → RightLowWaveIndex → ℕ → ℕ

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_low_product_families -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def lowPrimeItems (n : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter (fun j => j.1.Prime ∧ ¬j.1 ∣ n)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_target_divisor_support -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

def sparseTargetDivisorCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/2048 : ℝ)⌋₊

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_outside_target_trimming -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def targetDivisorKept (n u : ℕ) : Prop := u.gcd n ≤ sparseTargetDivisorCap n

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_after_short_right -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4Scale
open scoped Classical

noncomputable section

def rightStepIsShort (n : ℕ) (j : RightLowWaveIndex) : Prop := rightLowWaveStep j ≤ maximumStep n

def longRightLowItems (n : ℕ) : Finset RightLowWaveIndex :=
  (lowPrimeItems n).filter (fun j => ¬rightStepIsShort n j)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_high_prime_factor_weights -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4MoebiusGauss
open scoped Classical Moebius

noncomputable section

def restrictedMangoldtAfter (P : ℕ) (keep : ℕ → Prop) : ArithmeticFunction ℝ :=
  ⟨fun b => if P<b ∧ keep b then vonMangoldt b else 0, by simp⟩

def restrictedVaughanFactor (P : ℕ) (keep : ℕ → Prop) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ) - truncateArithmetic (μ : ArithmeticFunction ℝ) P) *
    restrictedMangoldtAfter P keep

private theorem norm_restricted_mangoldt_after_le {n b : ℕ} (bn : b ≤ n) (P : ℕ)
    (keep : ℕ → Prop) : ‖(restrictedMangoldtAfter P keep b : ℂ)‖ ≤ logBudget n := by
  change ‖((if P<b ∧ keep b then vonMangoldt b else 0 : ℝ) : ℂ)‖ ≤ _
  by_cases h : P<b ∧ keep b
  · rw [if_pos h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
    exact vonMangoldt_le_log.trans (log_le_logBudget ((Nat.zero_le _).trans_lt h.1) bn)
  · simp [h,zero_le_one.trans (one_le_logBudget n)]

theorem norm_restricted_vaughan_factor_le {n b : ℕ} (P : ℕ) (bn : b ≤ n) (keep : ℕ → Prop)
    {T : ℝ} (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖(restrictedVaughanFactor P keep b : ℂ)‖ ≤ T*logBudget n := by
  let m := ((μ : ArithmeticFunction ℝ) - truncateArithmetic (μ : ArithmeticFunction ℝ) P)
  let f := restrictedMangoldtAfter P keep
  have mb (x : ℕ) (_ : x ≤ n) : ‖(m x : ℂ)‖ ≤ 1 := by
    change ‖(((μ x : ℝ) - (if x≤P then (μ x : ℝ) else 0) : ℝ) : ℂ)‖ ≤ 1
    by_cases cut : x ≤ P
    · simp [cut]
    · simpa [cut,moebiusComplex] using norm_moebiusComplex_le_one x
  simpa only [restrictedVaughanFactor,m,f,one_mul] using norm_convolution_apply_le bn m f zero_le_one
    (zero_le_one.trans (one_le_logBudget n)) (divisors b bn) mb
    (fun x hx => norm_restricted_mangoldt_after_le hx P keep)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_high_proper_square_support -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail DyadicMixedB4Scale
open scoped Classical

noncomputable section

def highProperSquareCut (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/768 : ℝ)⌋₊

def highProperFrequencySupport (n : ℕ) : Finset ℕ := squareMultipleSupport n (highProperSquareCut n)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_left_prime_factor_weights -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical Moebius

noncomputable section

def leftRestrictedWeight (n : ℕ) (keep : ℕ → Prop) (i : ℕ × ℕ) : ℂ :=
  (leftBandMoebius n i.1 : ℂ) * (restrictedVaughanFactor (vaughanShortCut n) keep i.2 : ℂ)

def leftPrimeWeight (n : ℕ) := leftRestrictedWeight n Nat.Prime

theorem norm_bilateral_left_restricted_step_mass {n : ℕ} (keep : ℕ → Prop)
    {T : ℝ} (T0 : 0 ≤ T) (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (q : ℕ) (hq : q ∈ Icc 1 n) :
    (∑ i ∈ (bilateralLeftWaveItems n).filter (fun i => leftBilinearStep i=q),
      ‖leftRestrictedWeight n keep i‖) ≤ T^3*logBudget n := by
  apply norm_bilateral_left_step_mass_from_pointwise T0 divisorBound (leftRestrictedWeight n keep) _ q hq
  intro i hi
  have hs := (mem_product.mp (mem_filter.mp (mem_filter.mp hi).1).1).2
  have aStep : i.1 ≤ leftBilinearStep i := by
    simpa only [leftBilinearStep,Nat.mul_one] using Nat.mul_le_mul_left i.1 (mem_Icc.mp hs).1
  have aBound := aStep.trans (mem_filter.mp hi).2
  rw [leftRestrictedWeight,norm_mul]
  exact mul_le_mul ((norm_leftBandMoebius_le n i.1).trans (divisorBound i.1 aBound))
    (norm_restricted_vaughan_factor_le (vaughanShortCut n) (mem_Icc.mp hs).2 keep divisorBound)
    (norm_nonneg _) T0

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_symmetric_ramp_row_bridge -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical Finset

noncomputable section

set_option maxHeartbeats 2200000

def rightInverseRamp (n u v : ℕ) : ℝ :=
  let d := u.gcd v
  centeredInverseRamp (v/d) (((n/d : ℕ) : ℤ)*Nat.gcdA (u/d) (v/d)-1)

theorem centered_inverse_ramp_eq_of_cast_eq {m : ℕ} {x y : ℤ}
    (h : (x : ZMod m) = (y : ZMod m)) :
    centeredInverseRamp m (x-1) = centeredInverseRamp m (y-1) := by
  have shifted : ((x-1 : ℤ) : ZMod m) = ((y-1 : ℤ) : ZMod m) := by
    simpa only [Int.cast_sub,Int.cast_one,h]
  unfold centeredInverseRamp
  rw [(ZMod.intCast_eq_intCast_iff' (x-1) (y-1) m).mp shifted]

theorem cast_gcdA_eq_inv_of_coprime {u m : ℕ} (cop : u.Coprime m) :
    (Nat.gcdA u m : ZMod m) = (u : ZMod m)⁻¹ := by
  have bez := congrArg (fun z : ℤ => (z : ZMod m)) (Nat.gcd_eq_gcd_ab u m)
  rw [cop.gcd_eq_one] at bez
  have lin : (1 : ZMod m) = (u : ZMod m)*(Nat.gcdA u m : ZMod m) := by
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_one,Nat.cast_one,
      ZMod.natCast_self,zero_mul,add_zero] using bez
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ lin.symm).symm

def rightInverseRampPhase (num m : ℕ) (a : ℕ) (j : ℤ) : ℤ :=
  (((num : ZMod m)*(a : ZMod m)⁻¹*(j : ZMod m)⁻¹).val : ℕ)

theorem right_inverse_ramp_phase_cast (num m : ℕ) [NeZero m] (a : ℕ) (j : ℤ) :
    (rightInverseRampPhase num m a j : ZMod m) =
      (num : ZMod m)*(a : ZMod m)⁻¹*(j : ZMod m)⁻¹ := by
  unfold rightInverseRampPhase
  rw [Int.cast_natCast,ZMod.natCast_zmod_val]

def rightInverseRampWindow (n m g e k l₀ r₀ : ℕ) : ℂ :=
  let v := m/g
  let h := g/e
  let I := expandedHighDividedHyperbolaFactors n m g e k
  let J := intIntervalModUnits v 0 (moderateLowDividedHyperbolaCofactorCap n r₀ g e k)
  gatedBilinearSum I J (fun a => (leftBandMoebius n (e*a) : ℂ))
    (fun j => (restrictedVaughanFactor (vaughanShortCut n) Nat.Prime (h*j.toNat) : ℂ))
    (fun a => (l₀/g/a : ℕ)) (fun a => (r₀/g/a : ℕ))
    (fun a j => (centeredInverseRamp v (rightInverseRampPhase (n/g) v a j-1) : ℂ))

theorem right_inverse_ramp_window_eq_selected {n m g e k l₀ r₀ : ℕ}
    (mpos : 0 < m) (mN : m ≤ n) (lLower : leftMediumCap n ≤ l₀) (rUpper : r₀ ≤ extendedWideStepCap n)
    (g0 : 0 < g) (gm : g ∣ m) (e0 : 0 < e) (eg : e ∣ g) :
    rightInverseRampWindow n m g e k l₀ r₀ =
      ∑ i ∈ moderateLowDividedHyperbolaLeftItems n m g e k l₀ r₀,
        leftPrimeWeight n i * (rightInverseRamp n (leftBilinearStep i) m : ℂ) := by
  let v := m/g
  let h := g/e
  let l := l₀/g
  let r := r₀/g
  let aLo := primeHyperbolaFactorLo n k
  let aHi := min (lowCut n) (primeHyperbolaFactorFloor n (k+1))
  let S := moderateLowDividedHyperbolaCofactorCap n r₀ g e k
  let I := expandedHighDividedHyperbolaFactors n m g e k
  let J := intIntervalModUnits v 0 S
  let gate (a : ℕ) (j : ℤ) : Prop := ((l/a : ℕ) : ℤ) < j ∧ j ≤ ((r/a : ℕ) : ℤ)
  let P := (J ×ˢ I).filter fun t => gate t.2 t.1
  let liftPoint (t : ℤ × ℕ) : ℕ × ℕ := (e*t.2,h*t.1.toNat)
  let F (a : ℕ) (j : ℤ) := (centeredInverseRamp v (rightInverseRampPhase (n/g) v a j-1) : ℂ)
  let value (i : ℕ × ℕ) := leftPrimeWeight n i*(rightInverseRamp n (leftBilinearStep i) m : ℂ)
  let w (t : ℤ × ℕ) := leftPrimeWeight n (liftPoint t)*F t.2 t.1
  have n0 : 0 < n := mpos.trans_le mN
  have gE : e*h = g := Nat.mul_div_cancel' eg
  have h0 : 0 < h := Nat.div_pos (Nat.le_of_dvd g0 eg) e0
  have vG : g*v=m := Nat.mul_div_cancel' gm
  have vEq : m/g=v := rfl
  have v0 : 0 < v := Nat.div_pos (Nat.le_of_dvd mpos gm) g0
  have rN : r₀ ≤ n := rUpper.trans (extended_wide_step_le n0)
  have infoI {a : ℕ} (ha : a ∈ I) :
      aLo/e < a ∧ a ≤ aHi/e ∧ (e*a).gcd g=e ∧ a.Coprime v := by
    have H := mem_filter.mp ha
    exact ⟨(mem_Ioc.mp H.1).1,(mem_Ioc.mp H.1).2,H.2.1,H.2.2⟩
  have infoJ {z : ℤ} (hz : z ∈ J) : z ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (z : ZMod v) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hz
  have copJ {z : ℤ} (hz : z ∈ J) : z.toNat.Coprime v := by
    have z0 := (mem_Ioc.mp (infoJ hz).1).1.le
    have cast : (z.toNat : ZMod v) = (z : ZMod v) := by
      simpa only [Int.cast_natCast] using congrArg (fun j : ℤ => (j : ZMod v)) (Int.toNat_of_nonneg z0)
    exact (ZMod.isUnit_iff_coprime _ _).mp (cast.symm ▸ (infoJ hz).2)
  have baseEq (a j : ℕ) : e*a*(h*j) = g*(a*j) := by rw [← gE]; ring
  have aBounds (a : ℕ) : aLo/e < a ∧ a ≤ aHi/e ↔ aLo < e*a ∧ e*a ≤ aHi := by
    rw [Nat.div_lt_iff_lt_mul e0,Nat.le_div_iff_mul_le e0,Nat.mul_comm a e]
  have productBounds (u : ℕ) : l < u ∧ u ≤ r ↔ l₀ < g*u ∧ g*u ≤ r₀ := by
    change l₀/g < u ∧ u ≤ r₀/g ↔ _
    rw [Nat.div_lt_iff_lt_mul g0,Nat.le_div_iff_mul_le g0,Nat.mul_comm u g]
  have gateBounds (a : ℕ) (a0 : 0 < a) (j : ℤ) (j0 : 0 ≤ j) :
      gate a j ↔ l < a*j.toNat ∧ a*j.toNat ≤ r := by
    unfold gate
    rw [← Int.toNat_of_nonneg j0]
    simp only [Int.ofNat_lt,Int.ofNat_le,Int.toNat_natCast,Nat.div_lt_iff_lt_mul a0,
      Nat.le_div_iff_mul_le a0,Nat.mul_comm j.toNat a]
  have lift_mem (t : ℤ × ℕ) (ht : t ∈ P) : liftPoint t ∈ moderateLowDividedHyperbolaLeftItems n m g e k l₀ r₀ := by
    obtain ⟨hj,ha⟩ := mem_product.mp (mem_filter.mp ht).1
    obtain ⟨al,au,ag,ac⟩ := infoI ha
    have a0 := (Nat.zero_le _).trans_lt al
    have z0 := (mem_Ioc.mp (infoJ hj).1).1
    have j0 : 0 < t.1.toNat := by omega
    have ab := (aBounds t.2).mp ⟨al,au⟩
    have pb := (productBounds (t.2*t.1.toNat)).mp
      ((gateBounds _ a0 _ z0.le).mp (mem_filter.mp ht).2)
    rw [← baseEq] at pb
    have small : h*t.1.toNat ≤ e*t.2*(h*t.1.toNat) := by
      have ea1 : 1 ≤ e*t.2 := mul_pos e0 a0
      simpa only [one_mul] using Nat.mul_le_mul_right (h*t.1.toNat) ea1
    have jN : h*t.1.toNat ≤ n := small.trans (pb.2.trans rN)
    have base : liftPoint t ∈ leftBilinearItems n := mem_product.mpr
      ⟨mem_Ioc.mpr ⟨(le_max_left _ _).trans_lt ab.1,ab.2.trans (min_le_left _ _)⟩,
        mem_Icc.mpr ⟨mul_pos h0 j0,jN⟩⟩
    have acj : (t.2*t.1.toNat).Coprime v := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa only [Nat.cast_mul] using ((ZMod.isUnit_iff_coprime _ _).mpr ac).mul
        ((ZMod.isUnit_iff_coprime _ _).mpr (copJ hj))
    have gcd : (leftBilinearStep (liftPoint t)).gcd m=g := by
      change (e*t.2*(h*t.1.toNat)).gcd m = g
      rw [baseEq,← vG,Nat.gcd_mul_left,acj.gcd_eq_one,mul_one]
    have left : liftPoint t ∈ bilateralLeftWaveItems n :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨base,lLower.trans_lt pb.1⟩,pb.2.trans rN⟩
    exact mem_filter.mpr ⟨left,mem_Ioc.mpr ab,gcd,ag,pb.1,pb.2⟩
  have lift_surj (i : ℕ × ℕ) (hi : i ∈ moderateLowDividedHyperbolaLeftItems n m g e k l₀ r₀) :
      ∃ t ∈ P, liftPoint t=i := by
    obtain ⟨left,fac,gcd,egcd,upL,upR⟩ := mem_filter.mp hi
    change (i.1*i.2).gcd m = g at gcd
    have eA : e ∣ i.1 := egcd ▸ Nat.gcd_dvd_left i.1 g
    have gU : g ∣ i.1*i.2 := gcd ▸ Nat.gcd_dvd_left (i.1*i.2) m
    have hJ : h ∣ i.2 := by
      have flat := (divide_left_product_of_gcd g0 gU).1
      rw [egcd] at flat
      exact flat
    let a := i.1/e
    let j := i.2/h
    have ea : e*a=i.1 := Nat.mul_div_cancel' eA
    have hj : h*j=i.2 := Nat.mul_div_cancel' hJ
    have aB : aLo/e < a ∧ a ≤ aHi/e := (aBounds a).mpr (by rw [ea]; exact mem_Ioc.mp fac)
    have a0 := (Nat.zero_le _).trans_lt aB.1
    have jI := (mem_Icc.mp (mem_product.mp (mem_filter.mp (mem_filter.mp left).1).1).2)
    have j0 : 0 < j := Nat.div_pos (Nat.le_of_dvd jI.1 hJ) h0
    have poly : i.1*i.2=g*(a*j) := by rw [← baseEq,ea,hj]
    have ab : l < a*j ∧ a*j ≤ r := (productBounds _).mpr (by rw [← poly]; exact ⟨upL,upR⟩)
    have jS : j ≤ S := (Nat.le_div_iff_mul_le (Nat.succ_pos (aLo/e))).mpr
      (by rw [Nat.mul_comm]; exact (Nat.mul_le_mul_right j aB.1).trans ab.2)
    have cop : (a*j).Coprime v := by
      have core : (i.1*i.2/(i.1*i.2).gcd m).Coprime (m/(i.1*i.2).gcd m) :=
        Nat.coprime_div_gcd_div_gcd (gcd.symm ▸ g0)
      rw [gcd,vEq,poly,Nat.mul_div_cancel_left _ g0] at core
      exact core
    have aI : a ∈ I := mem_filter.mpr ⟨mem_Ioc.mpr aB,by rw [ea]; exact egcd,cop.coprime_dvd_left (dvd_mul_right _ _)⟩
    have jJ : (j : ℤ) ∈ J := by
      have unit : IsUnit ((j : ℤ) : ZMod v) := by
        rw [Int.cast_natCast]
        exact (ZMod.isUnit_iff_coprime _ _).mpr (cop.coprime_dvd_left (dvd_mul_left _ _))
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by exact_mod_cast j0,by exact_mod_cast jS⟩,unit⟩
    have jG : gate a (j : ℤ) := (gateBounds _ a0 _ (by positivity)).mpr (by simpa only [Int.toNat_natCast])
    exact ⟨((j : ℤ),a),mem_filter.mpr ⟨mem_product.mpr ⟨jJ,aI⟩,jG⟩,
      Prod.ext ea (by simpa only [liftPoint,Int.toNat_natCast] using hj)⟩
  have eval (t : ℤ × ℕ) (ht : t ∈ P) : w t=value (liftPoint t) := by
    have hi := lift_mem t ht
    have htJ := (mem_product.mp (mem_filter.mp ht).1).1
    have htI := (mem_product.mp (mem_filter.mp ht).1).2
    have z0 := (mem_Ioc.mp (infoJ htJ).1).1
    have alg : (leftBilinearStep (liftPoint t)).gcd m=g := (mem_filter.mp hi).2.2.1
    have c : (t.1.toNat : ZMod v) = (t.1 : ZMod v) := by
      simpa only [Int.cast_natCast] using congrArg (fun j : ℤ => (j : ZMod v)) (Int.toNat_of_nonneg z0.le)
    have cop : (t.2*t.1.toNat).Coprime v := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa only [Nat.cast_mul] using ((ZMod.isUnit_iff_coprime _ _).mpr (infoI htI).2.2.2).mul
        ((ZMod.isUnit_iff_coprime _ _).mpr (copJ htJ))
    let _ : NeZero v := ⟨v0.ne'⟩
    have inverse : ((t.2 : ZMod v)*(t.1 : ZMod v))⁻¹ = (t.2 : ZMod v)⁻¹*(t.1 : ZMod v)⁻¹ := by
      apply ZMod.inv_eq_of_mul_eq_one
      calc
        _ = ((t.2 : ZMod v)*(t.2 : ZMod v)⁻¹)*((t.1 : ZMod v)*(t.1 : ZMod v)⁻¹) := by ring
        _ = _ := by
          rw [ZMod.coe_mul_inv_eq_one t.2 (infoI htI).2.2.2,
            ZMod.mul_inv_of_unit _ (infoJ htJ).2,one_mul]
    have phase : (rightInverseRampPhase (n/g) v t.2 t.1 : ZMod v) =
        ((((n/g : ℕ) : ℤ)*Nat.gcdA (t.2*t.1.toNat) v : ℤ) : ZMod v) := by
      rw [right_inverse_ramp_phase_cast,Int.cast_mul,Int.cast_natCast,
        cast_gcdA_eq_inv_of_coprime cop,Nat.cast_mul,c,inverse]
      ring
    have product : leftBilinearStep (liftPoint t) = g*(t.2*t.1.toNat) := baseEq _ _
    unfold w value F rightInverseRamp
    rw [alg]
    dsimp only
    rw [product,Nat.mul_div_cancel_left _ g0,vEq,centered_inverse_ramp_eq_of_cast_eq phase]
  have eq : rightInverseRampWindow n m g e k l₀ r₀ = ∑ t ∈ P, w t := by
    change gatedBilinearSum I J (fun a => (leftBandMoebius n (e*a) : ℂ))
        (fun j => (restrictedVaughanFactor (vaughanShortCut n) Nat.Prime (h*j.toNat) : ℂ))
        (fun a => (l/a : ℕ)) (fun a => (r/a : ℕ)) F = _
    rw [gated_bilinear_sum_eq_pair_sum]
    unfold P
    rw [sum_filter,sum_product]
    refine sum_congr rfl fun j _ => sum_congr rfl fun a _ => ?_
    change ite (gate a j) _ 0 = ite (gate a j) _ 0
    by_cases hG : gate a j
    · rw [ite_eq_left hG,ite_eq_left hG]
      simp only [w,liftPoint,leftPrimeWeight,leftRestrictedWeight]
    · simp only [ite_eq_right hG]
  rw [eq]
  refine sum_bij (fun t _ => liftPoint t) lift_mem ?_ ?_ eval
  swap
  · intro i hi
    obtain ⟨t,ht,eqt⟩ := lift_surj i hi
    exact ⟨t,ht,eqt⟩
  intro t ht u hu heq
  have positive {x : ℤ × ℕ} (hx : x ∈ P) : 0 ≤ x.1 :=
    (mem_Ioc.mp (infoJ (mem_product.mp (mem_filter.mp hx).1).1).1).1.le
  have fst : e*t.2=e*u.2 := congrArg Prod.fst heq
  have snd : h*t.1.toNat=h*u.1.toNat := congrArg Prod.snd heq
  have jEq := Nat.eq_of_mul_eq_mul_left h0 snd
  exact Prod.ext (by rw [← Int.toNat_of_nonneg (positive ht),← Int.toNat_of_nonneg (positive hu),jEq])
    (Nat.eq_of_mul_eq_mul_left e0 fst)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_near_product_row -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4PairIntegral
open scoped Classical

noncomputable section

def weilNearProductCap (n : ℕ) : ℕ := 2*⌊(n : ℝ)^(1+3/8192 : ℝ)⌋₊

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_near_growth -/
section

namespace GoldbachTypeII13

open Filter Topology
open DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

theorem saving_of_weil_near_growth (f : ℕ → ℂ) (K : ℝ) (K0 : 0 ≤ K)
    (bound : ∀ n : ℕ, 1 ≤ n → ∀ T : ℝ, 1 ≤ T →
      (∀ m ≤ 4*n^3, (m.divisors.card : ℝ) ≤ T) →
        ‖f n‖ ≤ K*(n : ℝ)^(8191/8192 : ℝ)*T^9*logBudget n^5) : saving f := by
  intro ε ε0
  obtain ⟨D,D1,db⟩ := divisor_envelope_at_power 1048576 (by decide)
  let C := K*(4*D)^9
  have hlimit : Tendsto (fun n : ℕ => (n : ℝ)^(-(3/32768) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/32768)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(3/32768) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlimit
  have estimate : ∀ᶠ n : ℕ in atTop, ‖f n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le_power (1/1048576) (by norm_num),
      hl.eventually_lt_const ε0] with n hn logb final
    have nr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have np := zero_lt_one.trans_le nr
    have D0 := zero_le_one.trans D1
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/1048576 : ℝ)
    let T := (4*D)*X^3
    have X1 : 1 ≤ X := Real.one_le_rpow nr (by norm_num)
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) D1) (one_le_pow₀ X1)
    have cp : (4 : ℝ)^(1/1048576 : ℝ) ≤ 4 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have divs (m : ℕ) (hm : m ≤ 4*n^3) : (m.divisors.card : ℝ) ≤ T := by
      calc
        _ ≤ D*((4*n^3 : ℕ) : ℝ)^(1/(1048576 : ℕ) : ℝ) := db (4*n^3) m hm
        _ = D*((4 : ℝ)^(1/1048576 : ℝ)*X^3) := by
          push_cast
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul np.le]
          unfold X
          rw [← Real.rpow_mul_natCast np.le]
          norm_num
        _ ≤ D*(4*X^3) := by gcongr
        _ = _ := by unfold T; ring
    have ex : (n : ℝ)^(8191/8192 : ℝ)*X^32 = (n : ℝ)^(-(3/32768) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast np.le, ← Real.rpow_add np, ← Real.rpow_add_one np.ne']
      congr 1
      norm_num
    calc
      _ ≤ K*(n : ℝ)^(8191/8192 : ℝ)*T^9*logBudget n^5 := bound n hn T T1 divs
      _ ≤ K*(n : ℝ)^(8191/8192 : ℝ)*T^9*X^5 := by gcongr
      _ = C*((n : ℝ)^(8191/8192 : ℝ)*X^32) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(3/32768) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right final.le np.le
  obtain ⟨N,h⟩ := eventually_atTop.mp estimate
  exact ⟨N,fun n hn _ => h n hn⟩

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_near_product_saving -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def weilNearRowDivisors (n m : ℕ) : Finset ℕ :=
  n.divisors.filter fun g => g ∣ m ∧ g ≤ thinHighGcdCap n

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_near_product_selection -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical Finset

noncomputable section

theorem prime_hyperbola_factor_floor_mono {n : ℕ} (n1 : 1 ≤ n) :
    Monotone (primeHyperbolaFactorFloor n) := by
  intro a b ab
  unfold primeHyperbolaFactorFloor
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n1)
    (div_le_div_of_nonneg_right (by exact_mod_cast ab) (by norm_num))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_adaptive_scale -/
section

namespace GoldbachTypeII13

noncomputable section

def weilAdaptiveModulusExponent (x : ℝ) : ℝ := 37/64-(2/3)*(x-31/256)

theorem weil_inverse_ramp_adaptive_scales {N M A S D G x : ℝ}
    (N1 : 1 ≤ N) (M0 : 0 ≤ M) (A0 : 0 ≤ A) (S0 : 0 ≤ S)
    (D1 : 1 ≤ D) (G0 : 0 ≤ G) (xLo : 31/512 ≤ x) (mLarge : M ≤ N^(37/64 : ℝ))
    (aCap : A ≤ N^(x+17/4096)) (smCap : S*M*D^2 ≤ 2*N^(1+3/8192-x))
    (mCap : M ≤ N^weilAdaptiveModulusExponent x) (gCap : G ≤ N^(1/2048 : ℝ)) :
    M*D*(S*Real.sqrt A+A*Real.sqrt S*Real.sqrt (Real.sqrt M*Real.sqrt G)) ≤
      4*N^(1023/1024 : ℝ) := by
  by_cases short : x ≤ 31/256
  · exact weil_inverse_ramp_scales N1 M0 A0 S0 D1 G0 xLo short aCap smCap mLarge gCap
  · have xHi : (31/256 : ℝ) ≤ x := le_of_not_ge short
    let F := N^((x-31/256)/3)
    have N0 : 0 < N := zero_lt_one.trans_le N1
    have F1 : 1 ≤ F := Real.one_le_rpow N1 (by linarith)
    have F0 : 0 < F := zero_lt_one.trans_le F1
    have D0 := zero_le_one.trans D1
    have Fsq : F^2 = N^((2/3)*(x-31/256)) := by
      unfold F
      rw [pow_two,← Real.rpow_add N0]
      congr 1 <;> ring
    have Fcube : F^3 = N^(x-31/256) := by
      rw [pow_succ F 2,Fsq]
      unfold F
      rw [← Real.rpow_add N0]
      congr 1 <;> ring
    have mBound : M*F^2 ≤ N^(37/64 : ℝ) := by
      calc
        _ ≤ N^weilAdaptiveModulusExponent x*F^2 := mul_le_mul_of_nonneg_right mCap (by positivity)
        _ = _ := by rw [Fsq,← Real.rpow_add N0]; congr 1; unfold weilAdaptiveModulusExponent; ring
    have aBound : A/F^3 ≤ N^((31/256 : ℝ)+17/4096) := by
      apply (div_le_iff₀ (by positivity : 0<F^3)).mpr
      calc
        A ≤ N^(x+17/4096) := aCap
        _ = _ := by rw [Fcube,← Real.rpow_add N0]; congr 1; ring
    have pBound : (S*F)*(M*F^2)*D^2 ≤ 2*N^(1+3/8192-(31/256 : ℝ)) := by
      calc
        _ = (S*M*D^2)*F^3 := by ring
        _ ≤ (2*N^(1+3/8192-x))*F^3 := mul_le_mul_of_nonneg_right smCap (by positivity)
        _ = _ := by rw [Fcube,mul_assoc,← Real.rpow_add N0]; congr 1; ring
    have scaled := weil_inverse_ramp_scales N1 (show 0≤M*F^2 by positivity)
      (show 0≤A/F^3 by positivity) (show 0≤S*F by positivity)
      D1 G0 (x := 31/256) (by norm_num) le_rfl aBound pBound mBound gCap
    have diag : M*D*S*Real.sqrt A ≤ (M*F^2)*D*(S*F)*Real.sqrt (A/F^3) := by
      have H : Real.sqrt (F^3) ≤ F^3 :=
        Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ F1))
      have H0 : 0 < Real.sqrt (F^3) := Real.sqrt_pos.2 (by positivity)
      have ratio : 1 ≤ F^3/Real.sqrt (F^3) := (le_div_iff₀ H0).2 (by simpa using H)
      calc
        _ ≤ (M*D*S*Real.sqrt A)*(F^3/Real.sqrt (F^3)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left ratio (by positivity : 0≤M*D*S*Real.sqrt A)
        _ = _ := by rw [Real.sqrt_div A0]; ring
    have off : (M*F^2)*D*(A/F^3)*Real.sqrt (S*F)*
        Real.sqrt (Real.sqrt (M*F^2)*Real.sqrt G) =
        M*D*A*Real.sqrt S*Real.sqrt (Real.sqrt M*Real.sqrt G) := by
      rw [Real.sqrt_mul M0,Real.sqrt_sq F0.le,Real.sqrt_mul S0]
      rw [show Real.sqrt M*F*Real.sqrt G = (Real.sqrt M*Real.sqrt G)*F by ring,
        Real.sqrt_mul (by positivity)]
      calc
        _ = (M*D*A*Real.sqrt S*Real.sqrt (Real.sqrt M*Real.sqrt G))*
            ((F^2/F^3)*(Real.sqrt F*Real.sqrt F)) := by ring
        _ = _ := by
          rw [Real.mul_self_sqrt F0.le]
          field_simp [F0.ne'] <;> ring
    rw [mul_add] at scaled ⊢
    have lhs : M*D*(S*Real.sqrt A) ≤ (M*F^2)*D*((S*F)*Real.sqrt (A/F^3)) := by
      simpa only [mul_assoc] using diag
    have rhs : (M*F^2)*D*((A/F^3)*Real.sqrt (S*F)*Real.sqrt (Real.sqrt (M*F^2)*Real.sqrt G)) =
        M*D*(A*Real.sqrt S*Real.sqrt (Real.sqrt M*Real.sqrt G)) := by
      simpa only [mul_assoc] using off
    exact (add_le_add lhs rhs.ge).trans scaled

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_adaptive_window -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4PairIntegral
open scoped Classical

noncomputable section

def weilAdaptiveRightRampBlocks (n m : ℕ) : Finset ℕ :=
  (Icc 32 63).filter fun k => (m : ℝ) ≤
    (n : ℝ)^weilAdaptiveModulusExponent ((k : ℝ)/256-1/4096)

theorem norm_gated_inverse_ramp_saving_adaptive_row {n m A S d : ℕ} [NeZero m] (c : ZMod m)
    (I : Finset ℕ) (base : I ⊆ Icc 1 A) (cop : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ) (span : S ≤ m)
    {T L x : ℝ} (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (leftWeights : ∀ i ∈ I, ‖α i‖ ≤ T)
    (rightWeights : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T*L)
    (tau : (m.divisors.card : ℝ) ≤ T) (log : 1+Real.log m ≤ L)
    (s : ℕ → ZMod m) (t : ℤ → ZMod m) (z : ℕ → ℤ → ℤ)
    (phase : ∀ i j, (z i j : ZMod m) = c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹-s i-t j)
    (n1 : 1 ≤ n) (d1 : 1 ≤ d) (xLo : 31/512 ≤ x)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+17/4096))
    (productCap : (S : ℝ)*(m : ℝ)*(d : ℝ)^2 ≤ 2*(n : ℝ)^(1+3/8192-x))
    (mLarge : (m : ℝ) ≤ (n : ℝ)^(37/64 : ℝ))
    (mCap : (m : ℝ) ≤ (n : ℝ)^weilAdaptiveModulusExponent x)
    (gCap : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ)) :
    (m : ℝ)*(d : ℝ)*‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun i j => (centeredInverseRamp m (z i j-1) : ℂ))‖ ≤
      12*T^4*L^3*(n : ℝ)^(1023/1024 : ℝ) := by
  have bound := norm_gated_inverse_ramp_le_weil_row c I base cop α β lo hi span
    T1 L1 leftWeights rightWeights tau log s t z phase
  have scale := weil_inverse_ramp_adaptive_scales (show (1 : ℝ) ≤ n by exact_mod_cast n1)
    (by positivity : (0 : ℝ) ≤ m) (by positivity : (0 : ℝ) ≤ A) (by positivity : (0 : ℝ) ≤ S)
    (show (1 : ℝ) ≤ d by exact_mod_cast d1) (by positivity : (0 : ℝ) ≤ m.gcd c.val)
    xLo mLarge aCap productCap mCap gCap
  have T0 : 0 ≤ T := zero_le_one.trans T1
  have L0 : 0 ≤ L := zero_le_one.trans L1
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left bound (by positivity)
    _ = 3*T^4*L^3*((m : ℝ)*(d : ℝ)*((S : ℝ)*Real.sqrt A+
        (A : ℝ)*Real.sqrt S*Real.sqrt (Real.sqrt m*Real.sqrt (m.gcd c.val)))) := by ring
    _ ≤ 3*T^4*L^3*(4*(n : ℝ)^(1023/1024 : ℝ)) := mul_le_mul_of_nonneg_left scale (by positivity)
    _ = _ := by ring


theorem norm_adaptive_right_inverse_ramp_window_le {n m g e k l₀ r₀ : ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (mUpper : (m : ℝ) ≤ (n : ℝ)^(37/64 : ℝ))
    (mTarget : m.gcd n ≤ sparseTargetDivisorCap n)
    (g0 : 0 < g) (gn : g ∣ n) (gm : g ∣ m) (gSmall : g ≤ thinHighGcdCap n)
    (e0 : 0 < e) (eg : e ∣ g) (hk : k ∈ weilAdaptiveRightRampBlocks n m)
    (rM : r₀ ≤ m) (rProd : r₀*m ≤ weilNearProductCap n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ b ≤ n, (b.divisors.card : ℝ) ≤ T) :
    (m : ℝ)*‖rightInverseRampWindow n m g e k l₀ r₀‖ ≤
      12*T^4*logBudget n^3*(n : ℝ)^(1023/1024 : ℝ) := by
  let N := (n : ℝ)
  let v := m/g
  let h := g/e
  let A := primeHyperbolaFactorFloor n (k+1)/e
  let S := moderateLowDividedHyperbolaCofactorCap n r₀ g e k
  let I := expandedHighDividedHyperbolaFactors n m g e k
  let J := intIntervalModUnits v 0 S
  let aLo := primeHyperbolaFactorLo n k
  let aHi := min (lowCut n) (primeHyperbolaFactorFloor n (k+1))
  let x := (k : ℝ)/256-1/4096
  let α (a : ℕ) : ℂ := leftBandMoebius n (e*a)
  let β (j : ℤ) : ℂ := restrictedVaughanFactor (vaughanShortCut n) Nat.Prime (h*j.toNat)
  let c : ZMod v := (n/g : ℕ)
  have n1 : 1 ≤ n := m0.trans_le mN
  have N1 : 1 ≤ N := by unfold N; exact_mod_cast n1
  have N0 : 0 < N := zero_lt_one.trans_le N1
  have v0 : 0 < v := Nat.div_pos (Nat.le_of_dvd m0 gm) g0
  let _ : NeZero v := ⟨v0.ne'⟩
  have VG : v*g=m := Nat.div_mul_cancel gm
  have vN : v ≤ n := (Nat.div_le_self _ _).trans mN
  have rN : r₀ ≤ n := rM.trans mN
  have hG : h ≤ g := Nat.div_le_self _ _
  have gR : 0 < (g : ℝ) := by exact_mod_cast g0
  have vProd : (v : ℝ)*(g : ℝ)=(m : ℝ) := by exact_mod_cast VG
  have gCap : (g : ℝ) ≤ N^(1/4096 : ℝ) := by
    exact (by exact_mod_cast gSmall : (g : ℝ) ≤ (thinHighGcdCap n : ℝ)).trans (Nat.floor_le (by positivity))
  have eCap : (e : ℝ) ≤ N^(1/4096 : ℝ) :=
    (show (e : ℝ) ≤ (g : ℝ) by exact_mod_cast Nat.le_of_dvd g0 eg).trans gCap
  have vCap : (v : ℝ) ≤ N^(37/64 : ℝ) :=
    (show (v : ℝ) ≤ (m : ℝ) by exact_mod_cast Nat.div_le_self m g).trans mUpper
  have gcdCap : (v.gcd c.val : ℝ) ≤ N^(1/2048 : ℝ) := by
    have dvd : v.gcd (n/g) ∣ m.gcd n := Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans ⟨g,VG.symm⟩)
      ((Nat.gcd_dvd_right _ _).trans ⟨g,(Nat.div_mul_cancel gn).symm⟩)
    have bound : v.gcd c.val ≤ sparseTargetDivisorCap n := (gcd_val_nat_cast_le_gcd (m := v) (n/g)).trans
      ((Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ m0) dvd).trans mTarget)
    exact (show (v.gcd c.val : ℝ) ≤ sparseTargetDivisorCap n by exact_mod_cast bound).trans
      (Nat.floor_le (by positivity))
  have kLo : (32 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hk).1).1
  have xLo : 31/512 ≤ x := by unfold x; linarith only [kLo]
  have adapt : (v : ℝ) ≤ N^weilAdaptiveModulusExponent x :=
    (show (v : ℝ) ≤ m by exact_mod_cast Nat.div_le_self m g).trans (mem_filter.mp hk).2
  have aPow : primeHyperbolaFactorFloor n (k+1) = ⌊N^(x+17/4096)⌋₊ := by
    unfold primeHyperbolaFactorFloor x N
    rw [Nat.cast_add,Nat.cast_one]
    congr 2
    ring
  have aCap : (A : ℝ) ≤ N^(x+17/4096) :=
    (by exact_mod_cast Nat.div_le_self (primeHyperbolaFactorFloor n (k+1)) e :
      (A : ℝ) ≤ (primeHyperbolaFactorFloor n (k+1) : ℝ)).trans (by rw [aPow]; exact Nat.floor_le (by positivity))
  have aSmall (a : ℕ) (ha : a ∈ I) :
      aLo/e < a ∧ a ≤ aHi/e ∧ (e*a).gcd g=e ∧ a.Coprime v := by
    have H := mem_filter.mp ha
    exact ⟨(mem_Ioc.mp H.1).1,(mem_Ioc.mp H.1).2,H.2.1,H.2.2⟩
  have Icap : I ⊆ Icc 1 A := fun a ha =>
    mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (aSmall a ha).1,
      (aSmall a ha).2.1.trans (Nat.div_le_div_right (min_le_right _ _))⟩
  have leftWeight : ∀ a ∈ I, ‖α a‖ ≤ T := by
    intro a ha
    have an : e*a ≤ n := calc
      _ ≤ aHi := by
        rw [Nat.mul_comm]
        exact (Nat.le_div_iff_mul_le e0).mp (aSmall a ha).2.1
      _ ≤ lowCut n := min_le_left _ _
      _ ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le N1 (by norm_num))
    exact (norm_leftBandMoebius_le n (e*a)).trans (divisors _ an)
  have Sdiv : S ≤ r₀/g := Nat.div_le_self (r₀/g) _
  have span : S ≤ v := Sdiv.trans (Nat.div_le_div_right rM)
  have rightWeight : ∀ j ∈ J, ‖β j‖ ≤ T*logBudget n := by
    intro j hj
    have data : j ∈ Ioc 0 (S : ℤ) ∧ IsUnit (j : ZMod v) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    have jTop := (mem_Ioc.mp data.1).2
    have jt : j.toNat ≤ S := by simpa only [Int.toNat_natCast] using Int.toNat_le_toNat jTop
    have bound : h*j.toNat ≤ n := calc
      _ ≤ g*(r₀/g) := Nat.mul_le_mul hG (jt.trans Sdiv)
      _ ≤ r₀ := Nat.mul_div_le _ _
      _ ≤ n := rN
    exact norm_restricted_vaughan_factor_le (vaughanShortCut n) bound Nat.Prime divisors
  have log : 1+Real.log (v : ℝ) ≤ logBudget n := by
    unfold logBudget
    have upper : (v : ℝ) ≤ n := by exact_mod_cast vN
    exact add_le_add (le_refl _) (Real.log_le_log (by exact_mod_cast v0) (by linarith only [upper]))
  have cofFloor : N^x ≤ ((aLo/e : ℕ) : ℝ)+1 := by
    have less : aLo < (aLo/e+1)*e :=
      (Nat.div_lt_iff_lt_mul e0).mp (Nat.lt_succ_self _)
    have rank : (primeHyperbolaFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*(e : ℝ) := by
      have le : primeHyperbolaFactorFloor n k+1 ≤ (aLo/e+1)*e :=
        Nat.succ_le_of_lt ((le_max_right _ _).trans_lt less)
      exact_mod_cast le
    have ground : N^((k : ℝ)/256) ≤ (((aLo/e : ℕ) : ℝ)+1)*(e : ℝ) :=
      (Nat.lt_floor_add_one _).le.trans rank
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos N0 (1/4096 : ℝ))).mp
    calc
      _ = N^((k : ℝ)/256) := by rw [← Real.rpow_add N0]; unfold x; simp
      _ ≤ _ := ground
      _ ≤ _ := mul_le_mul_of_nonneg_left eCap (by positivity)
  have cofactor : S*(aLo/e+1) ≤ r₀/g := Nat.div_mul_le_self _ _
  have product : (S : ℝ)*(v : ℝ)*(g : ℝ)^2 ≤ 2*N^(1+3/8192-x) := by
    have cofactorR : (S : ℝ)*(((aLo/e : ℕ) : ℝ)+1) ≤ ((r₀/g : ℕ) : ℝ) := by exact_mod_cast cofactor
    have divideR : ((r₀/g : ℕ) : ℝ)*(g : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast Nat.div_mul_le_self r₀ g
    have rp : (r₀ : ℝ)*(m : ℝ) ≤ 2*N^(1+3/8192 : ℝ) := by
      apply (show (r₀ : ℝ)*(m : ℝ) ≤ weilNearProductCap n from by exact_mod_cast rProd).trans
      unfold weilNearProductCap
      push_cast
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos N0 x)).mp
    calc
      _ ≤ ((S : ℝ)*(v : ℝ)*(g : ℝ)^2)*(((aLo/e : ℕ) : ℝ)+1) :=
        mul_le_mul_of_nonneg_left cofFloor (by positivity)
      _ = ((S : ℝ)*(((aLo/e : ℕ) : ℝ)+1))*(g : ℝ)*((v : ℝ)*(g : ℝ)) := by ring
      _ ≤ ((r₀/g : ℕ) : ℝ)*(g : ℝ)*((v : ℝ)*(g : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cofactorR gR.le) (by positivity)
      _ ≤ (r₀ : ℝ)*(m : ℝ) := by rw [vProd]; exact mul_le_mul_of_nonneg_right divideR (by positivity)
      _ ≤ _ := rp
      _ = _ := by rw [mul_assoc,← Real.rpow_add N0,sub_add_cancel]
  rw [← vProd]
  exact norm_gated_inverse_ramp_saving_adaptive_row c I Icap (fun a ha => (aSmall a ha).2.2.2)
    α β (fun a => (l₀/g/a : ℕ)) (fun a => (r₀/g/a : ℕ)) span T1 (one_le_logBudget n)
    leftWeight rightWeight (divisors _ vN) log (fun _ => 0) (fun _ => 0) (rightInverseRampPhase (n/g) v)
    (fun a j => by simpa only [sub_zero,c] using right_inverse_ramp_phase_cast (n/g) v a j)
    n1 g0 xLo aCap product vCap adapt gcdCap


end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_adaptive_row -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def weilAdaptiveRightRampRow (n m : ℕ) (lower upper : ℕ → ℕ) : ℂ :=
  ∑ g ∈ weilNearRowDivisors n m, ∑ e ∈ g.divisors, ∑ k ∈ weilAdaptiveRightRampBlocks n m,
    rightInverseRampWindow n m g e k (lower g) (upper g)

def weilAdaptiveRightRampSlice (R : ℕ → Finset RightLowWaveIndex)
    (lower upper : ModerateLowBounds) (n : ℕ) : ℂ :=
  ∑ j ∈ R n, rightLowWaveWeight j *
    weilAdaptiveRightRampRow n (rightLowWaveStep j) (lower n j) (upper n j)

theorem norm_weil_adaptive_right_ramp_row_le {n m : ℕ} {lower upper : ℕ → ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (mSize : (m : ℝ) ≤ (n : ℝ)^(37/64 : ℝ))
    (mTarget : m.gcd n ≤ sparseTargetDivisorCap n)
    (rM : ∀ g, upper g ≤ m) (rProd : ∀ g, (upper g)*m ≤ weilNearProductCap n)
    {T : ℝ} (T1 : 1 ≤ T) (divs : ∀ b ≤ n, (b.divisors.card : ℝ) ≤ T) :
    ‖weilAdaptiveRightRampRow n m lower upper‖ ≤
      (384*T^6*logBudget n^3*(n : ℝ)^(1023/1024 : ℝ))*(1/(m : ℝ)) := by
  let G := weilNearRowDivisors n m
  let B := (12*T^4*logBudget n^3*(n : ℝ)^(1023/1024 : ℝ))/(m : ℝ)
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have mR : (0 : ℝ) < m := by exact_mod_cast m0
  have B0 : 0 ≤ B := by unfold B; positivity
  have Gcard : (#G : ℝ) ≤ T :=
    (show (#G : ℝ) ≤ (n.divisors.card : ℝ) from by
      exact_mod_cast card_filter_le n.divisors (fun g => g ∣ m ∧ g ≤ thinHighGcdCap n)).trans (divs n le_rfl)
  have blockCard : (#(weilAdaptiveRightRampBlocks n m) : ℝ) ≤ 32 := by
    have cap : #(weilAdaptiveRightRampBlocks n m) ≤ #(Icc (32 : ℕ) 63) := card_filter_le _ _
    have h : #(Icc (32 : ℕ) 63) = 32 := by norm_num [Nat.card_Icc]
    rw [h] at cap
    exact_mod_cast cap
  have two (g : ℕ) (hg : g ∈ G) :
      ‖∑ e ∈ g.divisors, ∑ k ∈ weilAdaptiveRightRampBlocks n m, rightInverseRampWindow n m g e k (lower g) (upper g)‖ ≤
        T*(32*B) := by
    obtain ⟨hn,hm,hs⟩ := mem_filter.mp hg
    have gn := (Nat.mem_divisors.mp hn).1
    have g0 := Nat.pos_of_dvd_of_pos gn (m0.trans_le mN)
    have gN := Nat.le_of_dvd (m0.trans_le mN) gn
    have one (e : ℕ) (he : e ∈ g.divisors) :
        ‖∑ k ∈ weilAdaptiveRightRampBlocks n m, rightInverseRampWindow n m g e k (lower g) (upper g)‖ ≤ 32*B := by
      have eg := (Nat.mem_divisors.mp he).1
      have e0 := Nat.pos_of_dvd_of_pos eg g0
      calc
        _ ≤ ∑ k ∈ weilAdaptiveRightRampBlocks n m, ‖rightInverseRampWindow n m g e k (lower g) (upper g)‖ := norm_sum_le _ _
        _ ≤ ∑ _ ∈ weilAdaptiveRightRampBlocks n m, B := by
          refine sum_le_sum fun k hk => ?_
          unfold B
          apply (le_div_iff₀ mR).mpr
          rw [mul_comm]
          exact norm_adaptive_right_inverse_ramp_window_le m0 mN mSize mTarget g0 gn hm hs e0 eg hk
            (rM g) (rProd g) T1 divs
        _ = (#(weilAdaptiveRightRampBlocks n m) : ℝ)*B := by rw [sum_const,nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right blockCard B0
    calc
      _ ≤ ∑ e ∈ g.divisors, ‖∑ k ∈ weilAdaptiveRightRampBlocks n m, rightInverseRampWindow n m g e k (lower g) (upper g)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ g.divisors, 32*B := sum_le_sum one
      _ = (#g.divisors : ℝ)*(32*B) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (divs g gN) (by positivity)
  calc
    _ ≤ ∑ g ∈ G, ‖∑ e ∈ g.divisors, ∑ k ∈ weilAdaptiveRightRampBlocks n m, rightInverseRampWindow n m g e k (lower g) (upper g)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ G, T*(32*B) := sum_le_sum two
    _ = (#G : ℝ)*(T*(32*B)) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ T*(T*(32*B)) := mul_le_mul_of_nonneg_right Gcard (by positivity)
    _ = _ := by unfold B; ring

set_option maxHeartbeats 1200000 in
theorem weil_adaptive_right_ramp_saving
    (R : ℕ → Finset RightLowWaveIndex) (lower upper : ModerateLowBounds)
    (support : ∀ n, ∀ j ∈ R n, j ∈ rightLowWaveItems n ∧
      (rightLowWaveStep j : ℝ) ≤ (n : ℝ)^(37/64 : ℝ) ∧
      (rightLowWaveStep j).gcd n ≤ sparseTargetDivisorCap n)
    (rM : ∀ n, ∀ j ∈ R n, ∀ g, upper n j g ≤ rightLowWaveStep j)
    (rProd : ∀ n, ∀ j ∈ R n, ∀ g, (upper n j g)*(rightLowWaveStep j) ≤ weilNearProductCap n) :
    saving (weilAdaptiveRightRampSlice R lower upper) := by
  apply saving_of_weil_near_growth _ 384 (by norm_num)
  intro n n1 T T1 divs
  let L := logBudget n
  let J := R n
  let B := 384*T^6*L^3*(n : ℝ)^(1023/1024 : ℝ)
  let W := T^3*L
  have subset : J ⊆ rightLowWaveItems n := fun j hj => (support n j hj).1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have W0 : 0 ≤ W := by unfold W; positivity
  have B0 : 0 ≤ B := by unfold B; positivity
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have divN (m : ℕ) (hm : m ≤ n) : (m.divisors.card : ℝ) ≤ T := by
    apply divs m (hm.trans ?_)
    have p : n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
    omega
  have massH : (∑ m ∈ Icc 1 n, 1/(m : ℝ)) ≤ L := calc
    _ = (harmonic n : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    _ ≤ 1+Real.log n := by exact_mod_cast harmonic_le_one_add_log n
    _ ≤ L := by
      unfold L logBudget
      exact add_le_add (le_refl _) (Real.log_le_log (zero_lt_one.trans_le nR) (by linarith))
  have step (j : RightLowWaveIndex) (hj : j ∈ J) : rightLowWaveStep j ∈ Icc 1 n :=
    bilateral_right_low_step_range (subset hj)
  have weighted : (∑ j ∈ J, ‖rightLowWaveWeight j‖*(1/(rightLowWaveStep j : ℝ))) ≤ W*L := by
    refine (sum_norm_mul_le_of_step_mass J rightLowWaveStep rightLowWaveWeight (fun m => 1/(m : ℝ))
      step (fun _ _ => by positivity) ?_).trans (mul_le_mul_of_nonneg_left massH W0)
    intro m hm
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ subset)
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_right_low_step_mass T1 divN m hm)
  have each (j : RightLowWaveIndex) (hj : j ∈ J) :
      ‖weilAdaptiveRightRampRow n (rightLowWaveStep j) (lower n j) (upper n j)‖ ≤ B*(1/(rightLowWaveStep j : ℝ)) := by
    obtain ⟨_,size,gcd⟩ := support n j hj
    obtain ⟨p,q⟩ := mem_Icc.mp (step j hj)
    exact norm_weil_adaptive_right_ramp_row_le p q size gcd (rM n j hj) (rProd n j hj) T1 divN
  unfold weilAdaptiveRightRampSlice
  calc
    _ ≤ ∑ j ∈ J, ‖rightLowWaveWeight j*weilAdaptiveRightRampRow n (rightLowWaveStep j) (lower n j) (upper n j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ‖rightLowWaveWeight j‖*(B*(1/(rightLowWaveStep j : ℝ))) := by
      refine sum_le_sum fun j hj => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (each j hj) (norm_nonneg _)
    _ = B*(∑ j ∈ J, ‖rightLowWaveWeight j‖*(1/(rightLowWaveStep j : ℝ))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ B*(W*L) := mul_le_mul_of_nonneg_left weighted B0
    _ = 384*(n : ℝ)^(1023/1024 : ℝ)*T^9*logBudget n^5 := by unfold B W L; ring
    _ ≤ _ := by
      have power : (n : ℝ)^(1023/1024 : ℝ) ≤ (n : ℝ)^(8191/8192 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le nR (by norm_num)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left power (by norm_num)) (by positivity)) (by positivity)


def weilAdaptiveRightRampFactor (n m a : ℕ) : Prop :=
  ∃ k ∈ weilAdaptiveRightRampBlocks n m, a ∈ primeHyperbolaFactorBlock n k

theorem weil_adaptive_right_ramp_factor_lower {n m a : ℕ}
    (n1 : 1 ≤ n) (h : weilAdaptiveRightRampFactor n m a) :
    primeHyperbolaFactorFloor n 32 < a := by
  obtain ⟨k,hk,ha⟩ := h
  have le := prime_hyperbola_factor_floor_mono n1 (mem_Icc.mp (mem_filter.mp hk).1).1
  exact le.trans_lt ((le_max_right _ _).trans_lt (mem_Ioc.mp ha).1)

def weilAdaptiveRightRampRowItems (n m : ℕ) (lower upper : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (bilateralLeftWaveItems n).filter fun i =>
    let u := leftBilinearStep i
    let g := u.gcd m
    g ∈ weilNearRowDivisors n m ∧ lower g < u ∧ u ≤ upper g ∧
      weilAdaptiveRightRampFactor n m i.1

theorem weil_adaptive_right_ramp_row_eq_selected {n m : ℕ} {lower upper : ℕ → ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (lLeft : ∀ g, leftMediumCap n ≤ lower g) (rUpper : ∀ g, upper g ≤ extendedWideStepCap n) :
    weilAdaptiveRightRampRow n m lower upper =
      ∑ i ∈ weilAdaptiveRightRampRowItems n m lower upper,
        leftPrimeWeight n i * (rightInverseRamp n (leftBilinearStep i) m : ℂ) := by
  let I := weilAdaptiveRightRampRowItems n m lower upper
  let G := weilNearRowDivisors n m
  let K := weilAdaptiveRightRampBlocks n m
  let d (i : ℕ × ℕ) := (leftBilinearStep i).gcd m
  let w (i : ℕ × ℕ) := leftPrimeWeight n i * (rightInverseRamp n (leftBilinearStep i) m : ℂ)
  have n1 : 1 ≤ n := m0.trans_le mN
  have mapsG : ∀ i ∈ I, d i ∈ G := fun _ hi => (mem_filter.mp hi).2.1
  change weilAdaptiveRightRampRow n m lower upper = ∑ i ∈ I, w i
  rw [← sum_fiberwise_of_maps_to mapsG w]
  unfold weilAdaptiveRightRampRow
  refine sum_congr rfl fun g hg => ?_
  let I₁ := I.filter fun i => d i = g
  let aGcd (i : ℕ × ℕ) := i.1.gcd g
  have gData := mem_filter.mp hg
  have gn := (Nat.mem_divisors.mp gData.1).1
  have g0 := Nat.pos_of_dvd_of_pos gn n1
  have gq := gData.2.1
  have mapsE : ∀ i ∈ I₁, aGcd i ∈ g.divisors :=
    fun i _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right i.1 g,g0.ne'⟩
  change (∑ e ∈ g.divisors, ∑ k ∈ K, rightInverseRampWindow n m g e k (lower g) (upper g)) = ∑ i ∈ I₁, w i
  rw [← sum_fiberwise_of_maps_to mapsE w]
  refine sum_congr rfl fun e he => ?_
  let I₂ := I₁.filter fun i => aGcd i=e
  have eg := (Nat.mem_divisors.mp he).1
  have e0 := Nat.pos_of_dvd_of_pos eg g0
  have eqFilter (k : ℕ) (hk : k ∈ K) : moderateLowDividedHyperbolaLeftItems n m g e k (lower g) (upper g) =
      I₂.filter fun i => i.1 ∈ primeHyperbolaFactorBlock n k := by
    ext i
    constructor
    · intro hi
      obtain ⟨left,fac,gg,ee,lo,up⟩ := mem_filter.mp hi
      have dG : d i ∈ G := by
        change (leftBilinearStep i).gcd m ∈ weilNearRowDivisors n m
        rw [gg]
        exact hg
      have rel : (leftBilinearStep i).gcd m=g := gg
      have base : i ∈ I := mem_filter.mpr ⟨left,dG,by rw [rel]; exact lo,by rw [rel]; exact up,⟨k,hk,fac⟩⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨base,gg⟩,ee⟩,fac⟩
    · intro hi
      obtain ⟨hi₂,fac⟩ := mem_filter.mp hi
      obtain ⟨hi₁,ee⟩ := mem_filter.mp hi₂
      obtain ⟨hi₀,gg⟩ := mem_filter.mp hi₁
      obtain ⟨left,_,lo,up,_⟩ := mem_filter.mp hi₀
      have rel : (leftBilinearStep i).gcd m=g := gg
      exact mem_filter.mpr ⟨left,fac,gg,ee,by rwa [rel] at lo,by rwa [rel] at up⟩
  calc
    (∑ k ∈ K, rightInverseRampWindow n m g e k (lower g) (upper g)) =
        ∑ k ∈ K, ∑ i ∈ I₂.filter (fun i => i.1 ∈ primeHyperbolaFactorBlock n k), w i := by
      refine sum_congr rfl fun k hk => ?_
      rw [← eqFilter k hk]
      exact right_inverse_ramp_window_eq_selected m0 mN (lLeft g) (rUpper g) g0 gq e0 eg
    _ = ∑ i ∈ I₂, ∑ k ∈ K, if i.1 ∈ primeHyperbolaFactorBlock n k then w i else 0 := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = ∑ i ∈ I₂, w i := by
      refine sum_congr rfl fun i hi => ?_
      have left : i ∈ bilateralLeftWaveItems n :=
        (mem_filter.mp (mem_filter.mp (mem_filter.mp hi).1).1).1
      have aRange := (mem_product.mp (mem_filter.mp (mem_filter.mp left).1).1).1
      obtain ⟨b,_,unique⟩ := prime_hyperbola_factor_blocks_cover n1 aRange
      have hi₀ : i ∈ I := (mem_filter.mp (mem_filter.mp hi).1).1
      obtain ⟨k,kMem,hk⟩ := (mem_filter.mp hi₀).2.2.2.2
      have enlarge (l : ℕ) (hl : l ∈ K) : l ∈ Icc 16 63 := by
        have data := mem_Icc.mp (mem_filter.mp hl).1
        exact mem_Icc.mpr ⟨(by decide : (16 : ℕ) ≤ 32).trans data.1,data.2⟩
      rw [sum_eq_single_of_mem k kMem]
      · exact ite_eq_left hk
      · intro k' hk' neq
        exact ite_eq_right (fun h => neq ((unique k' ⟨enlarge k' hk',h⟩).trans
          (unique k ⟨enlarge k kMem,hk⟩).symm))


end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_frequency_gcd_mass -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem sum_zmod_mul_le_gcd_mul_sum {m : ℕ} [NeZero m] (c : ZMod m)
    (f : ZMod m → ℝ) (f0 : ∀ a, 0 ≤ f a) :
    (∑ x : ZMod m, f (c*x)) ≤ (m.gcd c.val : ℝ)*(∑ x : ZMod m, f x) := by
  let d := m.gcd c.val
  let p := inverseFrequencyPeriod m c
  let F (w : ZMod m) := (univ : Finset (ZMod m)).filter fun x => c*x=w
  have p0 : 0 < p := inverse_frequency_period_pos c
  have dp : p*d=m := Nat.div_mul_cancel (Nat.gcd_dvd_left m c.val)
  have each (w : ZMod m) : (F w).card ≤ d := by
    refine (card_le_card_of_injOn (fun x : ZMod m => x.val/p)
      (t := range d) (fun x _ => ?_) (fun x hx y hy same => ?_)).trans_eq (card_range d)
    · exact mem_range.mpr ((Nat.div_lt_iff_lt_mul p0).mpr
        (by rw [Nat.mul_comm d p,dp]; exact ZMod.val_lt x))
    · have e : c*x=c*y := ((mem_filter.mp hx).2).trans ((mem_filter.mp hy).2).symm
      have div : (p : ℤ) ∣ (x.val : ℤ)-(y.val : ℤ) := by
        apply inverse_frequency_period_dvd_of_mul_eq_zero c
        rw [Int.cast_sub,Int.cast_natCast,Int.cast_natCast,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,
          sub_mul,mul_comm x c,mul_comm y c,e,sub_self]
      have modEq : y.val ≡ x.val [MOD p] := Nat.modEq_iff_dvd.mpr div
      have vx := Nat.mod_add_div x.val p
      have vy := Nat.mod_add_div y.val p
      change x.val/p=y.val/p at same
      change y.val%p=x.val%p at modEq
      rw [same,← modEq,vy] at vx
      exact ZMod.val_injective m vx.symm
  calc
    _ = ∑ w : ZMod m, ∑ x ∈ F w, f (c*x) :=
      (sum_fiberwise_of_maps_to (fun (_x : ZMod m) (_h : _x ∈ univ) => mem_univ (c*_x)) _).symm
    _ = ∑ w : ZMod m, (F w).card * f w := by
      refine sum_congr rfl fun w _ => ?_
      calc
        _ = ∑ _x ∈ F w, f w := sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]
        _ = _ := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ ∑ w : ZMod m, (d : ℝ)*f w :=
      sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (by exact_mod_cast each w) (f0 w)
    _ = _ := (mul_sum ..).symm

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_double_fourth_core -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical ComplexConjugate

noncomputable section

def reciprocalPairDifference (m : ℕ) (q : ℕ × ℕ) : ZMod m :=
  (q.1 : ZMod m)⁻¹-(q.2 : ZMod m)⁻¹

def reciprocalDifferenceFibres (m : ℕ) (J : Finset ℕ) (z : ZMod m) : Finset (ℕ × ℕ) :=
  (J ×ˢ J).filter (fun q => reciprocalPairDifference m q=z)

def inverseUnweightedFrequency (m : ℕ) [NeZero m] (J : Finset ℕ) : ZMod m → ℂ :=
  inverseFrequencySum m J (fun _ => 1)

theorem reciprocal_difference_energy_eq_moment {m : ℕ} [NeZero m] (J : Finset ℕ) :
    (m : ℝ)*(∑ z : ZMod m, ((reciprocalDifferenceFibres m J z).card : ℝ)^2) =
      ∑ x : ZMod m, ‖inverseUnweightedFrequency m J x‖^4 := by
  let F := inverseUnweightedFrequency m J
  let R := reciprocalDifferenceFibres m J
  let K := reciprocalPairDifference m
  have eq (x : ZMod m) : ((‖F x‖^2 : ℝ) : ℂ) =
      ∑ z : ZMod m, ((R z).card : ℂ)*ZMod.stdAddChar (x*z) := by
    rw [Complex.ofReal_pow,← Complex.mul_conj']
    unfold F inverseUnweightedFrequency inverseFrequencySum
    simp only [one_mul,map_sum,sum_mul_sum,conj_stdAddChar]
    calc
      _ = ∑ q ∈ J ×ˢ J, ZMod.stdAddChar (x*K q) := by
        rw [sum_product]
        refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
        rw [← AddChar.map_add_eq_mul]
        congr 1
        unfold K reciprocalPairDifference
        ring
      _ = _ := by
        rw [← sum_fiberwise_of_maps_to (fun q (_ : q ∈ J ×ˢ J) => mem_univ (K q))]
        refine sum_congr rfl fun z _ => ?_
        calc
          _ = ∑ _q ∈ R z, ZMod.stdAddChar (x*z) :=
            sum_congr rfl fun q hq => by rw [show K q=z from (mem_filter.mp hq).2]
          _ = _ := by simp [nsmul_eq_mul]
  symm
  calc
    _ = ∑ x : ZMod m, ‖∑ z : ZMod m, ((R z).card : ℂ)*ZMod.stdAddChar (x*z)‖^2 := by
      refine sum_congr rfl fun x _ => ?_
      rw [← eq,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
      ring
    _ = _ := by rw [cyclic_weighted_parseval]; simp only [Complex.norm_natCast,R]

set_option maxHeartbeats 900000 in
theorem norm_rectangular_inverse_eighth_power_le {m A S : ℕ} [NeZero m] (c : ZMod m)
    (I J : Finset ℕ) (iCard : I.card ≤ A) (jCard : J.card ≤ S) (α β : ℕ → ℂ)
    {W V : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V)
    (wA : ∀ a ∈ I, ‖α a‖ ≤ W) (wB : ∀ b ∈ J, ‖β b‖ ≤ V) :
    ‖∑ b ∈ J, β b*inverseFrequencySum m I α (c*(b : ZMod m)⁻¹)‖^8 ≤
      (A : ℝ)^4*(S : ℝ)^4*W^8*V^8*(m.gcd c.val : ℝ)*
        ((∑ z : ZMod m, ‖inverseUnweightedFrequency m I z‖^4)*
          (∑ z : ZMod m, ‖inverseUnweightedFrequency m J z‖^4)/(m : ℝ)) := by
  let F := inverseUnweightedFrequency m I
  let K := reciprocalPairDifference m
  let R := reciprocalDifferenceFibres m J
  let H (a : ℕ) := ∑ b ∈ J, β b*ZMod.stdAddChar (c*(a : ZMod m)⁻¹*(b : ZMod m)⁻¹)
  let Y := ∑ a ∈ I, ‖H a‖^2
  let P := ∑ q ∈ J ×ˢ J, ‖F (c*K q)‖
  let Z := ∑ q ∈ J ×ˢ J, ‖F (c*K q)‖^2
  let B := ∑ z : ZMod m, ((R z).card : ℝ)^2
  let C := ∑ z : ZMod m, ‖F z‖^4
  let D := ∑ z : ZMod m, ‖inverseUnweightedFrequency m J z‖^4
  have m0 : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have ACard : (#I : ℝ) ≤ A := by exact_mod_cast iCard
  have SCard : (#J : ℝ) ≤ S := by exact_mod_cast jCard
  have P0 : 0 ≤ P := by unfold P; positivity
  have Z0 : 0 ≤ Z := by unfold Z; positivity
  have B0 : 0 ≤ B := by unfold B; positivity
  have Y0 : 0 ≤ Y := by unfold Y; positivity
  have swap : (∑ b ∈ J, β b*inverseFrequencySum m I α (c*(b : ZMod m)⁻¹)) =
      ∑ a ∈ I, α a*H a := by
    unfold H inverseFrequencySum
    simp only [mul_sum]
    rw [sum_comm (s := J) (t := I)]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [show c*(b : ZMod m)⁻¹*(a : ZMod m)⁻¹=c*(a : ZMod m)⁻¹*(b : ZMod m)⁻¹ by ring]
    ring
  have sq (a : ℕ) : ((‖H a‖^2 : ℝ) : ℂ) =
      ∑ q ∈ J ×ˢ J, β q.1*conj (β q.2)*
        ZMod.stdAddChar (c*K q*(a : ZMod m)⁻¹) := by
    unfold H
    rw [Complex.ofReal_pow,← Complex.mul_conj']
    simp only [map_sum,sum_mul_sum,map_mul,conj_stdAddChar,sum_product]
    refine sum_congr rfl fun b _ => sum_congr rfl fun t _ => ?_
    have phase : c*K (b,t)*(a : ZMod m)⁻¹ =
        c*(a : ZMod m)⁻¹*(b : ZMod m)⁻¹+ -(c*(a : ZMod m)⁻¹*(t : ZMod m)⁻¹) := by
      unfold K reciprocalPairDifference
      dsimp only
      ring
    rw [phase,AddChar.map_add_eq_mul]
    ring
  have ys : (Y : ℂ) = ∑ q ∈ J ×ˢ J, β q.1*conj (β q.2)*F (c*K q) := by
    change Complex.ofRealHom (∑ a ∈ I, ‖H a‖^2) = _
    rw [map_sum]
    change (∑ a ∈ I, ((‖H a‖^2 : ℝ) : ℂ)) = _
    simp only [sq]
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    unfold F inverseUnweightedFrequency inverseFrequencySum
    simp only [one_mul]
    exact (mul_sum ..).symm
  have yBound : Y ≤ V^2*P := by
    calc
      _ = ‖(Y : ℂ)‖ := by rw [Complex.norm_real,Real.norm_of_nonneg Y0]
      _ ≤ ∑ q ∈ J ×ˢ J, ‖β q.1*conj (β q.2)*F (c*K q)‖ := by rw [ys]; exact norm_sum_le _ _
      _ ≤ ∑ q ∈ J ×ˢ J, V^2*‖F (c*K q)‖ := by
        refine sum_le_sum fun q hq => ?_
        obtain ⟨h1,h2⟩ := mem_product.mp hq
        rw [norm_mul,norm_mul,Complex.norm_conj,pow_two]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (wB _ h1) (wB _ h2) (norm_nonneg _) V0) (by positivity)
      _ = _ := by rw [mul_sum]
  have aBound : (∑ a ∈ I, ‖α a‖^2) ≤ (A : ℝ)*W^2 := by
    calc
      _ ≤ ∑ _a ∈ I, W^2 := sum_le_sum fun a ha => pow_le_pow_left₀ (norm_nonneg _) (wA a ha) 2
      _ = (#I : ℝ)*W^2 := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right ACard (by positivity)
  have n2 : ‖∑ a ∈ I, α a*H a‖^2 ≤ ((A : ℝ)*W^2*V^2)*P := by
    have h : ‖∑ a ∈ I, α a*H a‖ ≤ ∑ a ∈ I, ‖α a‖*‖H a‖ := by
      simpa only [norm_mul] using (norm_sum_le I (fun a => α a*H a))
    calc
      _ ≤ (∑ a ∈ I, ‖α a‖*‖H a‖)^2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ ≤ (∑ a ∈ I, ‖α a‖^2)*Y := sum_mul_sq_le_sq_mul_sq I _ _
      _ ≤ ((A : ℝ)*W^2)*(V^2*P) := mul_le_mul aBound yBound Y0 (by positivity)
      _ = _ := by ring
  have p2 : P^2 ≤ (S : ℝ)^2*Z := by
    unfold P Z
    have h := sum_mul_sq_le_sq_mul_sq (J ×ˢ J) (fun _ => (1 : ℝ)) (fun q => ‖F (c*K q)‖)
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,card_product,Nat.cast_mul] at h
    rw [← pow_two] at h
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) SCard 2) Z0)
  have zeq : Z = ∑ z : ZMod m, ((R z).card : ℝ)*‖F (c*z)‖^2 := by
    unfold Z
    rw [← sum_fiberwise_of_maps_to (fun q (_ : q ∈ J ×ˢ J) => mem_univ (K q))]
    refine sum_congr rfl fun z _ => ?_
    calc
      _ = ∑ _q ∈ R z, ‖F (c*z)‖^2 :=
        sum_congr rfl fun q hq => by rw [show K q=z from (mem_filter.mp hq).2]
      _ = _ := by simp [nsmul_eq_mul]
  have z2 : Z^2 ≤ B*((m.gcd c.val : ℝ)*C) := by
    rw [zeq]
    calc
      _ ≤ B*(∑ z : ZMod m, ‖F (c*z)‖^4) := by
        have h := sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod m))
          (fun z => ((R z).card : ℝ)) (fun z => ‖F (c*z)‖^2)
        simpa only [B,← pow_mul,show 2*2=4 by decide] using h
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_zmod_mul_le_gcd_mul_sum c
        (fun z => ‖F z‖^4) (fun _ => by positivity)) B0
  have invB : B = D/(m : ℝ) := (eq_div_iff m0.ne').mpr (by
    rw [mul_comm]
    exact reciprocal_difference_energy_eq_moment J)
  rw [swap]
  calc
    _ = (‖∑ a ∈ I, α a*H a‖^2)^4 := by ring
    _ ≤ (((A : ℝ)*W^2*V^2)*P)^4 := pow_le_pow_left₀ (by positivity) n2 4
    _ = ((A : ℝ)*W^2*V^2)^4*(P^2)^2 := by ring
    _ ≤ ((A : ℝ)*W^2*V^2)^4*(((S : ℝ)^2*Z)^2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) p2 2) (by positivity)
    _ = ((A : ℝ)*W^2*V^2)^4*(S : ℝ)^4*Z^2 := by ring
    _ ≤ ((A : ℝ)*W^2*V^2)^4*(S : ℝ)^4*(B*((m.gcd c.val : ℝ)*C)) :=
      mul_le_mul_of_nonneg_left z2 (by positivity)
    _ = _ := by rw [invB]; ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_double_fourth_scale -/
section

namespace GoldbachTypeII13

noncomputable section

theorem inverse_double_fourth_row_scale {N M A S D G x : ℝ}
    (N1 : 1 ≤ N) (M0 : 0 < M) (A0 : 0 ≤ A) (S0 : 0 ≤ S) (D1 : 1 ≤ D) (G0 : 0 ≤ G)
    (xLo : 127/1024 ≤ x) (xHi : x ≤ 1/4)
    (aCap : A ≤ N^(x+17/4096)) (sCap : S*M*D^2 ≤ 2*N^(1+3/8192-x))
    (mCap : M ≤ N^(37/64 : ℝ)) (gCap : G ≤ N^(1/2048 : ℝ)) :
    (M*D)^8*M*A^6*S^6*G*
        (1+A*Real.sqrt A/Real.sqrt M)*(1+S*Real.sqrt S/Real.sqrt M) ≤
      1024*N^(127/16 : ℝ) := by
  let U := S*M*D^2
  let Z := (M*D)^8*M*A^6*S^6*G
  let P := A*Real.sqrt A/Real.sqrt M
  let Q := S*Real.sqrt S/Real.sqrt M
  have N0 := zero_lt_one.trans_le N1
  have D0 := zero_lt_one.trans_le D1
  have U0 : 0 ≤ U := by unfold U; positivity
  have Z0 : 0 ≤ Z := by unfold Z; positivity
  have dPow (p : ℕ) : 1 ≤ D^p := one_le_pow₀ D1
  have pow_le_rpow (b t : ℝ) (b0 : 0 ≤ b) (h : b ≤ N^t) (p : ℕ) :
      b^p ≤ N^(t*(p : ℝ)) := by
    rw [Real.rpow_mul_natCast N0.le]
    exact pow_le_pow_left₀ b0 h p
  have Ubound (q : ℕ) : U^q ≤ (2 : ℝ)^q*N^((1+3/8192-x)*(q : ℝ)) := by
    rw [Real.rpow_mul_natCast N0.le,← mul_pow]
    exact pow_le_pow_left₀ U0 sCap q
  have g2 : G^2 ≤ N^(1/1024 : ℝ) := by
    have hh := pow_le_rpow G (1/2048) G0 gCap 2
    convert hh using 2 <;> norm_num
  have bound (k p q : ℕ) (qCap : q ≤ 16)
      (h : (37/64)*(k : ℝ)+(x+17/4096)*(p : ℝ)+(1+3/8192-x)*(q : ℝ)+1/1024 ≤ 127/8) :
      M^k*A^p*U^q*G^2 ≤ 65536*N^(127/8 : ℝ) := by
    let mExp := (37/64)*(k : ℝ)
    let aExp := (x+17/4096)*(p : ℝ)
    let uExp := (1+3/8192-x)*(q : ℝ)
    have C : (2 : ℝ)^q ≤ 65536 := by
      have c := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) qCap
      norm_num at c ⊢
      exact c
    calc
      _ ≤ N^mExp*N^aExp*((2 : ℝ)^q*N^uExp)*N^(1/1024 : ℝ) :=
        mul_le_mul (mul_le_mul (mul_le_mul
          (pow_le_rpow M (37/64) M0.le mCap k)
          (pow_le_rpow A (x+17/4096) A0 aCap p) (by positivity) (by positivity))
          (Ubound q) (by positivity) (by positivity)) g2 (by positivity) (by positivity)
      _ = (2 : ℝ)^q*N^(mExp+aExp+uExp+1/1024) := by
        rw [Real.rpow_add N0,Real.rpow_add N0,Real.rpow_add N0]
        ring
      _ ≤ _ := mul_le_mul C (Real.rpow_le_rpow_of_exponent_le N1 h) (by positivity) (by norm_num)
  have root (c : ℝ) (hc : 0 ≤ c) (hs : c^2 ≤ 65536*N^(127/8 : ℝ)) :
      c ≤ 256*N^(127/16 : ℝ) := by
    have eh : (256*N^(127/16 : ℝ))^2 = 65536*N^(127/8 : ℝ) := by
      rw [mul_pow,← Real.rpow_mul_natCast N0.le]
      norm_num
    rw [← eh] at hs
    by_contra! h
    exact (pow_lt_pow_left₀ h (by positivity) (by decide : 2 ≠ 0)).not_ge hs
  have p2 : P^2 = A^3/M := by
    unfold P
    rw [div_pow,mul_pow,Real.sq_sqrt A0,Real.sq_sqrt M0.le]
    ring
  have q2 : Q^2 = S^3/M := by
    unfold Q
    rw [div_pow,mul_pow,Real.sq_sqrt S0,Real.sq_sqrt M0.le]
    ring
  have r00 : Z ≤ 256*N^(127/16 : ℝ) := by
    apply root _ Z0
    calc
      _ ≤ Z^2*D^8 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (dPow 8) (sq_nonneg Z)
      _ = M^6*A^12*U^12*G^2 := by unfold U Z; ring
      _ ≤ _ := bound 6 12 12 (by decide) (by push_cast; linarith)
  have r10 : Z*P ≤ 256*N^(127/16 : ℝ) := by
    apply root _ (by unfold P; positivity)
    calc
      _ ≤ (Z*P)^2*D^8 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (dPow 8) (sq_nonneg (Z*P))
      _ = M^5*A^15*U^12*G^2 := by
        rw [mul_pow,p2]
        unfold U Z
        field_simp [M0.ne'] <;> ring
      _ ≤ _ := bound 5 15 12 (by decide) (by push_cast; linarith only [xHi])
  have r01 : Z*Q ≤ 256*N^(127/16 : ℝ) := by
    apply root _ (by unfold Q; positivity)
    calc
      _ ≤ (Z*Q)^2*D^14 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (dPow 14) (sq_nonneg (Z*Q))
      _ = M^2*A^12*U^15*G^2 := by
        rw [mul_pow,q2]
        unfold U Z
        field_simp [M0.ne'] <;> ring
      _ ≤ _ := bound 2 12 15 (by decide) (by push_cast; linarith only [xLo])
  have r11 : Z*P*Q ≤ 256*N^(127/16 : ℝ) := by
    apply root _ (by unfold P Q; positivity)
    calc
      _ ≤ (Z*P*Q)^2*D^14 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (dPow 14) (sq_nonneg (Z*P*Q))
      _ = M*A^15*U^15*G^2 := by
        rw [mul_pow,mul_pow,p2,q2]
        unfold U Z
        field_simp [M0.ne'] <;> ring
      _ ≤ _ := by
        simpa only [pow_one] using bound 1 15 15 (by decide) (by push_cast; linarith)
  change Z*(1+P)*(1+Q) ≤ _
  calc
    _ = (Z+Z*P)+(Z*Q+Z*P*Q) := by ring
    _ ≤ _ := (add_le_add (add_le_add r00 r10) (add_le_add r01 r11)).trans_eq (by ring)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_reciprocal_double_fourth_bound -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem inverse_unweighted_fourth_moment_simple_le {m A : ℕ} [NeZero m]
    (A0 : 0 < A) (Am : A < m) (I : Finset ℕ) (cap : I ⊆ Icc 1 A) (cop : ∀ a ∈ I, a.Coprime m)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ k ≤ 4*m^3, (k.divisors.card : ℝ) ≤ T) :
    (∑ z : ZMod m, ‖inverseUnweightedFrequency m I z‖^4) ≤
      (m : ℝ)*(A : ℝ)^2*(25*T)*(1+(A : ℝ)*Real.sqrt A/Real.sqrt m) := by
  let M := (m : ℝ)
  let B := (A : ℝ)
  have m0 : 0 < M := by unfold M; exact_mod_cast NeZero.pos m
  have B0 : 0 ≤ B := by unfold B; positivity
  have T0 := zero_le_one.trans T1
  have R0 : 0 ≤ B*Real.sqrt B/Real.sqrt M := by positivity
  have rewrite : B*Real.sqrt (M*B)/M = B*Real.sqrt B/Real.sqrt M := by
    rw [Real.sqrt_mul m0.le]
    field_simp [(Real.sqrt_pos.2 m0).ne',m0.ne']
    rw [Real.sq_sqrt m0.le]
    ring
  have raw := inverse_frequency_fourth_moment_composite_le A0 Am I cap cop (fun _ => 1)
    zero_le_one (fun _ _ => by simp) T1 divisors
  calc
    _ ≤ M*B^2*(1+inverseFibreBudget m A (2*T)) := by
      simpa only [inverseUnweightedFrequency,one_pow,mul_one,M,B] using raw
    _ ≤ M*B^2*((25*T)*(1+B*Real.sqrt B/Real.sqrt M)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold inverseFibreBudget
      change 1+2*(2*T)*(1+6*B*Real.sqrt (M*B)/M) ≤ _
      rw [show 6*B*Real.sqrt (M*B)/M = 6*(B*Real.sqrt (M*B)/M) by ring,rewrite]
      nlinarith only [T1,mul_nonneg T0 R0]
    _ = _ := by unfold M B; ring

set_option maxHeartbeats 1100000 in
theorem norm_rectangular_scaled_inverse_double_fourth {n m A S d : ℕ} [NeZero m]
    (c h : ZMod m) (I J : Finset ℕ) (capI : I ⊆ Icc 1 A) (capJ : J ⊆ Icc 1 S)
    (copI : ∀ a ∈ I, a.Coprime m) (copJ : ∀ a ∈ J, a.Coprime m)
    (A0 : 0 < A) (S0 : 0 < S) (Am : A < m) (Sm : S < m)
    (α β : ℕ → ℂ) {W V T x : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (T1 : 1 ≤ T)
    (aw : ∀ a ∈ I, ‖α a‖ ≤ W) (bw : ∀ b ∈ J, ‖β b‖ ≤ V)
    (n1 : 1 ≤ n) (d1 : 1 ≤ d) (xLo : 127/1024 ≤ x) (xHi : x ≤ 1/4)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+17/4096))
    (productCap : (S : ℝ)*(m : ℝ)*(d : ℝ)^2 ≤ 2*(n : ℝ)^(1+3/8192-x))
    (mCap : (m : ℝ) ≤ (n : ℝ)^(37/64 : ℝ))
    (gCap : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    (divisors : ∀ b ≤ 4*m^3, (b.divisors.card : ℝ) ≤ T) :
    ‖∑ b ∈ J, β b*inverseFrequencySum m I α ((-(h*c))*(b : ZMod m)⁻¹)‖ ≤
      W*V*(8*T*(n : ℝ)^(127/128 : ℝ)*(m.gcd h.val : ℝ)/((m : ℝ)*(d : ℝ))) := by
  let M := (m : ℝ)
  let G := (m.gcd c.val : ℝ)
  let H := (m.gcd h.val : ℝ)
  let N := (n : ℝ)
  let P := 1+(A : ℝ)*Real.sqrt A/Real.sqrt M
  let Q := 1+(S : ℝ)*Real.sqrt S/Real.sqrt M
  let K := N^(127/128 : ℝ)
  let Z := ‖∑ b ∈ J, β b*inverseFrequencySum m I α ((-(h*c))*(b : ZMod m)⁻¹)‖
  have m0 : 0 < M := by unfold M; exact_mod_cast NeZero.pos m
  have d0 : (0 : ℝ) < d := by exact_mod_cast (zero_lt_one.trans_le d1)
  have D1 : (1 : ℝ) ≤ d := by exact_mod_cast d1
  have N1 : 1 ≤ N := by unfold N; exact_mod_cast n1
  have N0 := zero_lt_one.trans_le N1
  have T0 := zero_le_one.trans T1
  have H1 : 1 ≤ H := by unfold H; exact_mod_cast (Nat.gcd_pos_of_pos_left h.val (NeZero.pos m))
  have H0 := zero_le_one.trans H1
  have P0 : 0 ≤ P := by unfold P; positivity
  have Q0 : 0 ≤ Q := by unfold Q; positivity
  have cardI : I.card ≤ A := (card_le_card capI).trans_eq (by simp [Nat.card_Icc])
  have cardJ : J.card ≤ S := (card_le_card capJ).trans_eq (by simp [Nat.card_Icc])
  have base := norm_rectangular_inverse_eighth_power_le (-(h*c)) I J cardI cardJ α β W0 V0 aw bw
  have aMoment := inverse_unweighted_fourth_moment_simple_le A0 Am I capI copI T1 divisors
  have bMoment := inverse_unweighted_fourth_moment_simple_le S0 Sm J capJ copJ T1 divisors
  have gcd : (m.gcd (-(h*c)).val : ℝ) ≤ G*H := by
    unfold G H
    exact_mod_cast ((gcd_fourier_phase_product_le h c).trans_eq (Nat.mul_comm _ _))
  have z8 : Z^8 ≤
      (A : ℝ)^4*(S : ℝ)^4*W^8*V^8*(G*H)*
        ((M*(A : ℝ)^2*(25*T)*P)*(M*(S : ℝ)^2*(25*T)*Q)/M) := by
    refine base.trans ?_
    gcongr
  have numerical := inverse_double_fourth_row_scale N1 m0
    (by positivity : (0 : ℝ) ≤ A) (by positivity : (0 : ℝ) ≤ S) D1
    (by positivity) xLo xHi aCap productCap mCap gCap
  have k8 : K^8 = N^(127/16 : ℝ) := by
    unfold K
    rw [← Real.rpow_mul_natCast N0.le]
    norm_num
  have powerBound : (M*(d : ℝ)*Z)^8 ≤ (8*T*K*H*W*V)^8 := by
    calc
      _ = (M*(d : ℝ))^8*Z^8 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left z8 (by positivity)
      _ = ((M*(d : ℝ))^8*M*(A : ℝ)^6*(S : ℝ)^6*G*P*Q)*
          ((25*T)^2*H*W^8*V^8) := by field_simp [m0.ne'] <;> ring
      _ ≤ (1024*N^(127/16 : ℝ))*((25*T)^2*H*W^8*V^8) :=
        mul_le_mul_of_nonneg_right numerical (by positivity)
      _ = (1024*625:ℝ)*T^2*K^8*H*W^8*V^8 := by rw [k8]; ring
      _ ≤ (8 : ℝ)^8*T^8*K^8*H^8*W^8*V^8 := by
        have tP : T^2 ≤ T^8 := pow_le_pow_right₀ T1 (by decide)
        have hP : H ≤ H^8 := by simpa only [pow_one] using pow_le_pow_right₀ H1 (show 1 ≤ 8 by decide)
        gcongr
        norm_num
      _ = _ := by ring
  have scale : M*(d : ℝ)*Z ≤ 8*T*K*H*W*V := by
    by_contra! bad
    exact (pow_lt_pow_left₀ bad (by positivity) (by decide : 8 ≠ 0)).not_ge powerBound
  change Z ≤ W*V*(8*T*K*H/(M*(d : ℝ)))
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (mul_pos m0 d0)).mpr
  calc
    _ = M*(d : ℝ)*Z := by ring
    _ ≤ _ := scale.trans_eq (by ring)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_gated_rectangular_moment -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

private theorem rectangular_indicator_eq_interval_residue_count {p : ℕ} [NeZero p] {a b j : ℤ}
    (ha : 0 ≤ a) (hb : b ≤ p) (hj : j ∈ Ioc (0 : ℤ) (p : ℤ)) :
    (if a < j ∧ j ≤ b then (1 : ℂ) else 0) =
        (intIntervalResidueCount p a b (j : ZMod p) : ℂ) := by
  have matching : ((Ioc a b).filter fun t : ℤ => (t : ZMod p) = (j : ZMod p)) =
      (Ioc a b).filter (fun t => t = j) := by
    ext t
    simp only [mem_filter]
    refine and_congr_right fun ht => ?_
    refine ⟨fun eq => ?_,fun eq => by rw [eq]⟩
    have tr := mem_Ioc.mp ht
    have tRange : t ∈ Ioc (0 : ℤ) (p : ℤ) :=
      mem_Ioc.mpr ⟨lt_of_le_of_lt ha tr.1,tr.2.trans hb⟩
    exact int_cast_injOn_Ioc_zero tRange hj eq
  unfold intIntervalResidueCount
  rw [matching]
  by_cases inside : j ∈ Ioc a b
  · have eq : ((Ioc a b).filter (fun t => t = j)) = {j} := by
      ext t
      simp only [mem_filter,mem_singleton]
      exact ⟨And.right,fun e => ⟨e.symm ▸ inside,e⟩⟩
    rw [eq]
    simp [(mem_Ioc.mp inside).1,(mem_Ioc.mp inside).2]
  · have eq : ((Ioc a b).filter (fun t => t = j)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact inside ((mem_filter.mp ht).2 ▸ (mem_filter.mp ht).1)
    rw [eq]
    simp only [card_empty,Nat.cast_zero,ite_eq_right (mt mem_Ioc.mpr inside)]

theorem norm_gated_frequency_sum_le_of_rectangular_bound {p S : ℕ} [NeZero p]
    (Sp : S ≤ p) (I : Finset ℕ) (J : Finset ℤ) (Jrange : J ⊆ Ioc 0 (S : ℤ))
    (ψ : ℤ → ZMod p) (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {W V Q : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (Q0 : 0 ≤ Q)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ W) (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (rectangular : ∀ (weight : ℕ → ℂ) (other : ℤ → ℂ) {X Y : ℝ},
      0 ≤ X → 0 ≤ Y → (∀ i ∈ I, ‖weight i‖ ≤ X) → (∀ j ∈ J, ‖other j‖ ≤ Y) →
        ‖∑ j ∈ J, other j*inverseFrequencySum p I weight (ψ j)‖ ≤ X*Y*Q) :
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹))‖ ≤
      (2+Real.log p)*W*V*Q := by
  let H := (univ : Finset (ZMod p)).filter (fun h => h ≠ 0)
  let a (i : ℕ) := max 0 (min (lo i) (S : ℤ))
  let b (i : ℕ) := max (a i) (min (hi i) (S : ℤ))
  let atZero (i : ℕ) : ℂ := ((b i-a i : ℤ) : ℂ)/(p : ℂ)
  let coeff (h : ZMod p) (i : ℕ) := intIntervalFourierCoefficient p (a i) (b i) h
  let βh (h : ZMod p) (j : ℤ) := β j*ZMod.stdAddChar (-(h*(j : ZMod p)))
  let G (h : ZMod p) := ∑ j ∈ J, βh h j*inverseFrequencySum p I (fun i => α i*coeff h i) (ψ j)
  let F := ∑ j ∈ J, β j*inverseFrequencySum p I (fun i => α i*atZero i) (ψ j)
  let d (h : ZMod p) : ℝ := 1/(2*(min h.val (p-h.val) : ℕ) : ℝ)
  have pNat : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have pp : (0 : ℝ) < p := by exact_mod_cast pNat
  have cap : (S : ℤ) ≤ p := by exact_mod_cast Sp
  have ord (i : ℕ) : a i ≤ b i := le_max_left _ _
  have left0 (i : ℕ) : 0 ≤ a i := le_max_left _ _
  have rightcap (i : ℕ) : b i ≤ p := by
    have hc' : a i ≤ (S : ℤ) := max_le (by positivity) (min_le_right _ _)
    exact (max_le hc' (min_le_right _ _)).trans cap
  have jRange {j : ℤ} (hj : j ∈ J) : j ∈ Ioc (0 : ℤ) (p : ℤ) := by
    have data := mem_Ioc.mp (Jrange hj)
    exact mem_Ioc.mpr ⟨data.1,data.2.trans cap⟩
  have indicator (i : ℕ) (j : ℤ) (hj : j ∈ J) :
      (if lo i < j ∧ j ≤ hi i then (1 : ℂ) else 0) =
        atZero i + ∑ h ∈ H, ZMod.stdAddChar (-(h*(j : ZMod p)))*coeff h i := by
    have jS := mem_Ioc.mp (Jrange hj)
    have eq : lo i < j ∧ j ≤ hi i ↔ a i < j ∧ j ≤ b i := by
      dsimp only [a,b]
      simp only [max_lt_iff,min_lt_iff,le_max_iff,le_min_iff]
      omega
    simp only [eq]
    rw [rectangular_indicator_eq_interval_residue_count (left0 i) (rightcap i) (jRange hj),
      int_interval_residue_count_fourier p (ord i)]
  have expand (j : ℤ) (hj : j ∈ J) :
      β j*(∑ i ∈ I, if lo i < j ∧ j ≤ hi i then α i*
        ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹) else 0) =
      β j*inverseFrequencySum p I (fun i => α i*atZero i) (ψ j) +
        ∑ h ∈ H, βh h j*inverseFrequencySum p I (fun i => α i*coeff h i) (ψ j) := by
    let e (i : ℕ) := ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹)
    have split (i : ℕ) :
        (if lo i < j ∧ j ≤ hi i then α i*ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹) else 0) =
          α i*atZero i*e i + ∑ h ∈ H, ZMod.stdAddChar (-(h*(j : ZMod p)))*(α i*coeff h i*e i) := by
      have step :
          (if lo i < j ∧ j ≤ hi i then α i*ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹) else 0) =
            (if lo i < j ∧ j ≤ hi i then (1 : ℂ) else 0)*(α i*e i) := by
        unfold e
        split_ifs <;> simp
      rw [step,indicator i j hj,add_mul,sum_mul]
      congr 1
      · ring
      · exact sum_congr rfl fun _ _ => by ring
    simp_rw [split,sum_add_distrib]
    rw [mul_add,sum_comm (s := I) (t := H)]
    apply congrArg₂ (· + ·)
    · rfl
    · rw [mul_sum]
      refine sum_congr rfl fun h _ => ?_
      unfold βh inverseFrequencySum
      rw [← mul_sum]
      ring
  have exactSum : gatedBilinearSum I J α β lo hi
      (fun i j => ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹)) = F+∑ h ∈ H, G h := by
    unfold gatedBilinearSum
    have e := sum_congr (s₁ := J) rfl (fun j hj => expand j hj)
    rw [e,sum_add_distrib,sum_comm (s := J) (t := H)]
  have az (i : ℕ) : ‖atZero i‖ ≤ 1 := by
    unfold atZero
    rw [norm_div,Complex.norm_natCast,Complex.norm_intCast,abs_of_nonneg]
    · apply (div_le_one pp).mpr
      exact_mod_cast (show b i-a i ≤ (p : ℤ) by linarith only [left0 i,rightcap i])
    · exact_mod_cast sub_nonneg.mpr (ord i)
  have fLe : ‖F‖ ≤ W*V*Q := by
    refine rectangular _ _ W0 V0 ?_ bw
    intro i hiI
    rw [norm_mul]
    exact (mul_le_mul (aw i hiI) (az i) (norm_nonneg _) W0).trans_eq (mul_one _)
  have gLe (h : ZMod p) (hh : h ∈ H) : ‖G h‖ ≤ d h*(W*V*Q) := by
    have h0 := (mem_filter.mp hh).2
    have d0 : 0 ≤ d h := by unfold d; positivity
    have est := rectangular (fun i => α i*coeff h i) (βh h) (mul_nonneg W0 d0) V0
      (by
        intro i hiI
        rw [norm_mul]
        exact mul_le_mul (aw i hiI) (norm_int_interval_fourier_coefficient_le p (a i) (b i) h0)
          (norm_nonneg _) W0)
      (by
        intro j hj
        rw [show ‖βh h j‖ = ‖β j‖ by simp [βh]]
        exact bw j hj)
    change ‖G h‖ ≤ (W*d h)*V*Q at est
    exact est.trans_eq (by ring)
  rw [exactSum]
  calc
    _ ≤ ‖F‖+‖∑ h ∈ H, G h‖ := norm_add_le _ _
    _ ≤ W*V*Q+∑ h ∈ H, d h*(W*V*Q) :=
      add_le_add fLe ((norm_sum_le _ _).trans (sum_le_sum gLe))
    _ ≤ W*V*Q+(1+Real.log p)*(W*V*Q) := by
      rw [← sum_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (sum_inv_min_val_le p) (by positivity))
    _ = _ := by ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_gated_inverse_double_fourth -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

private def natIntEmbedding : ℕ ↪ ℤ := ⟨Int.ofNat,fun _ _ h => Int.ofNat.inj h⟩

private theorem int_interval_mod_units_map_nat (m S : ℕ) :
    intIntervalModUnits m 0 S =
      ((Icc 1 S).filter (fun b => b.Coprime m)).map natIntEmbedding := by
  ext j
  constructor
  · intro hj
    have range := mem_Ioc.mp (mem_filter.mp hj).1
    have pos : 1 ≤ j.toNat := by omega
    have cap : j.toNat ≤ S := by omega
    have ce : (j.toNat : ℤ) = j := Int.toNat_of_nonneg range.1.le
    refine mem_map.mpr ⟨j.toNat,mem_filter.mpr ⟨mem_Icc.mpr ⟨pos,cap⟩,?_⟩,ce⟩
    rw [← ZMod.isUnit_iff_coprime,← Int.cast_natCast,ce]
    exact (mem_filter.mp hj).2
  · intro hj
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hj
    obtain ⟨bounds,cop⟩ := mem_filter.mp hb
    obtain ⟨lo,top⟩ := mem_Icc.mp bounds
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨?_,?_⟩,?_⟩
    · change (0 : ℤ) < b
      exact_mod_cast (zero_lt_one.trans_le lo)
    · change (b : ℤ) ≤ S
      exact_mod_cast top
    · change IsUnit (((b : ℤ) : ZMod m))
      rw [Int.cast_natCast,ZMod.isUnit_iff_coprime]
      exact cop

set_option maxHeartbeats 1400000 in
theorem norm_gated_inverse_ramp_saving_double_fourth {n m A S d : ℕ} [NeZero m] (c : ZMod m)
    (I : Finset ℕ) (capI : I ⊆ Icc 1 A) (copI : ∀ a ∈ I, a.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ) (Am : A < m) (Sm : S < m)
    {T L x : ℝ} (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (leftWeights : ∀ a ∈ I, ‖α a‖ ≤ T)
    (rightWeights : ∀ b ∈ intIntervalModUnits m 0 S, ‖β b‖ ≤ T*L)
    (divs : ∀ r ≤ 4*m^3, (r.divisors.card : ℝ) ≤ T) (log : 1+Real.log m ≤ L)
    (z : ℕ → ℤ → ℤ) (phase : ∀ a b, (z a b : ZMod m) = c*(a : ZMod m)⁻¹*(b : ZMod m)⁻¹)
    (n1 : 1 ≤ n) (d1 : 1 ≤ d) (xLo : 127/1024 ≤ x) (xHi : x ≤ 1/4)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+17/4096))
    (prodCap : (S : ℝ)*(m : ℝ)*(d : ℝ)^2 ≤ 2*(n : ℝ)^(1+3/8192-x))
    (mCap : (m : ℝ) ≤ (n : ℝ)^(37/64 : ℝ))
    (gCap : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ)) :
    (m : ℝ)*(d : ℝ)*‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun a b => (centeredInverseRamp m (z a b-1) : ℂ))‖ ≤
      16*T^4*L^3*(n : ℝ)^(127/128 : ℝ) := by
  let J := intIntervalModUnits m 0 S
  let B := (Icc 1 S).filter (fun b => b.Coprime m)
  let K := (n : ℝ)^(127/128 : ℝ)
  let D := (m : ℝ)*(d : ℝ)
  let E := 16*T^3*L^2*K/D
  have D0 : 0 < D := by
    unfold D
    have m0 : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
    have d0 : (0 : ℝ) < d := by exact_mod_cast (zero_lt_one.trans_le d1)
    positivity
  have E0 : 0 ≤ E := by unfold E; positivity
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans L1
  have jRange : J ⊆ Ioc (0 : ℤ) (S : ℤ) := by
    intro j hj
    have h : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    exact h.1
  have mapJ : J = B.map natIntEmbedding := int_interval_mod_units_map_nat m S
  have rect (h : ZMod m) (w : ℕ → ℂ) (q : ℤ → ℂ) {W V : ℝ}
      (W0 : 0 ≤ W) (V0 : 0 ≤ V) (aw : ∀ a ∈ I, ‖w a‖ ≤ W) (bw : ∀ b ∈ J, ‖q b‖ ≤ V) :
      ‖∑ b ∈ J, q b*inverseFrequencySum m I w ((-(h*c))*(b : ZMod m)⁻¹)‖ ≤
        W*V*(8*T*K*(m.gcd h.val : ℝ)/D) := by
    rw [mapJ,sum_map]
    change ‖∑ b ∈ B, q (b : ℤ)*inverseFrequencySum m I w ((-(h*c))*(((b : ℤ) : ZMod m))⁻¹)‖ ≤ _
    simp only [Int.cast_natCast]
    have original (b : ℕ) (hb : b ∈ B) : (b : ℤ) ∈ J := by
      rw [mapJ]
      exact mem_map.mpr ⟨b,hb,rfl⟩
    by_cases ai : 0 < A
    · by_cases bs : 0 < S
      · exact norm_rectangular_scaled_inverse_double_fourth c h I B capI (filter_subset _ _) copI
          (fun b hb => (mem_filter.mp hb).2) ai bs Am Sm w (fun b => q (b : ℤ)) W0 V0 T1 aw
          (fun b hb => bw _ (original b hb))
          n1 d1 xLo xHi aCap prodCap mCap gCap divs
      · have hS : S=0 := Nat.eq_zero_of_not_pos bs
        have empty : B=∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro b hb
          have bounds := mem_Icc.mp (mem_filter.mp hb).1
          omega
        rw [empty,sum_empty,norm_zero]
        positivity
    · have hA : A=0 := Nat.eq_zero_of_not_pos ai
      have empty : I=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro b hb
        have hv := mem_Icc.mp (capI hb)
        omega
      simp only [empty,inverseFrequencySum,sum_empty,mul_zero,sum_const_zero,norm_zero]
      positivity
  have log2 : 2+Real.log m ≤ 2*L := by linarith only [log,L1]
  have frequency (h : ZMod m) (_ : h ≠ 0) :
      ‖gatedBilinearSum I J α β lo hi (fun a b => ZMod.stdAddChar (-(h*(z a b : ZMod m))))‖ ≤
        0+E*(m.gcd h.val : ℝ) := by
    let ψ (b : ℤ) := (-(h*c))*(b : ZMod m)⁻¹
    have phaseEq (a : ℕ) (b : ℤ) : -(h*(z a b : ZMod m)) = ψ b*(a : ZMod m)⁻¹ := by
      rw [phase]
      unfold ψ
      ring
    simp_rw [phaseEq]
    have estimate := norm_gated_frequency_sum_le_of_rectangular_bound Sm.le I J jRange ψ α β lo hi
      T0 (mul_nonneg T0 L0) (show 0≤8*T*K*(m.gcd h.val : ℝ)/D by positivity)
      leftWeights rightWeights (rect h)
    calc
      _ ≤ (2+Real.log m)*T*(T*L)*(8*T*K*(m.gcd h.val : ℝ)/D) := estimate
      _ ≤ (2*L)*T*(T*L)*(8*T*K*(m.gcd h.val : ℝ)/D) := by gcongr
      _ = _ := by unfold E; ring
  have size : (m.divisors.card : ℝ) ≤ T := by
    apply divs
    have m1 : 1 ≤ m := NeZero.pos m
    have p : m ≤ m^3 := by simpa only [pow_one] using pow_le_pow_right₀ m1 (show 1 ≤ 3 by decide)
    omega
  have log0 : 0 ≤ 1+Real.log (m : ℝ) := by
    have m1 : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.pos m : 1 ≤ m)
    linarith only [Real.log_nonneg m1]
  have bound : ‖gatedBilinearSum I J α β lo hi (fun a b => (centeredInverseRamp m (z a b-1) : ℂ))‖ ≤ T*L*E := by
    apply norm_gated_inverse_ramp_le_of_prefix_bounds (NeZero.pos m) I J α β lo hi z (by positivity)
    intro k _
    have h := norm_gated_interval_residue_le_of_frequency_bounds I J α β lo hi
      (fun a b => (z a b : ZMod m)) (show (0 : ℤ) ≤ (k : ℤ)+1 by positivity) (show (0 : ℝ) ≤ 0 from le_rfl) E0 frequency
    rw [mul_zero,zero_add] at h
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul size log log0 T0) E0)
  exact (mul_le_mul_of_nonneg_left bound D0.le).trans_eq (by
    unfold E
    field_simp [D0.ne'] <;> ring)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_double_fourth_window -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4PairIntegral
open scoped Classical

noncomputable section

set_option maxHeartbeats 1400000 in
theorem norm_inner_low_large_factor_inverse_ramp_window_le {n m g e k l₀ r₀ : ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (mUpper : (m : ℝ) ≤ (n : ℝ)^(37/64 : ℝ))
    (mWide : widerLowFarModulusCap n < m)
    (mTarget : m.gcd n ≤ sparseTargetDivisorCap n)
    (g0 : 0 < g) (gn : g ∣ n) (gm : g ∣ m) (gSmall : g ≤ thinHighGcdCap n)
    (e0 : 0 < e) (eg : e ∣ g) (hk : k ∈ Icc 32 63)
    (rM : r₀ ≤ m) (rProd : r₀*m ≤ weilNearProductCap n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ b ≤ 4*n^3, (b.divisors.card : ℝ) ≤ T) :
    (m : ℝ)*‖rightInverseRampWindow n m g e k l₀ r₀‖ ≤
      16*T^4*logBudget n^3*(n : ℝ)^(127/128 : ℝ) := by
  let N := (n : ℝ)
  let v := m/g
  let h := g/e
  let A := primeHyperbolaFactorFloor n (k+1)/e
  let S := moderateLowDividedHyperbolaCofactorCap n r₀ g e k
  let I := expandedHighDividedHyperbolaFactors n m g e k
  let J := intIntervalModUnits v 0 S
  let aLo := primeHyperbolaFactorLo n k
  let aHi := min (lowCut n) (primeHyperbolaFactorFloor n (k+1))
  let x := (k : ℝ)/256-1/4096
  let α (a : ℕ) : ℂ := leftBandMoebius n (e*a)
  let β (j : ℤ) : ℂ := restrictedVaughanFactor (vaughanShortCut n) Nat.Prime (h*j.toNat)
  let c : ZMod v := (n/g : ℕ)
  have n1 : 1 ≤ n := m0.trans_le mN
  have N1 : 1 ≤ N := by unfold N; exact_mod_cast n1
  have N0 : 0 < N := zero_lt_one.trans_le N1
  have bigOne : 1 ≤ widerLowFarModulusCap n := Nat.le_floor (Real.one_le_rpow N1 (by norm_num))
  have nBig : 1 < N := by unfold N; exact_mod_cast (bigOne.trans_lt mWide).trans_le mN
  have divN (z : ℕ) (hz : z ≤ n) : (z.divisors.card : ℝ) ≤ T := by
    apply divisors z (hz.trans ?_)
    have pp : n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
    omega
  have v0 : 0 < v := Nat.div_pos (Nat.le_of_dvd m0 gm) g0
  let _ : NeZero v := ⟨v0.ne'⟩
  have VG : v*g=m := Nat.div_mul_cancel gm
  have vN : v ≤ n := (Nat.div_le_self _ _).trans mN
  have rN : r₀ ≤ n := rM.trans mN
  have hG : h ≤ g := Nat.div_le_self _ _
  have gR : 0 < (g : ℝ) := by exact_mod_cast g0
  have vProd : (v : ℝ)*(g : ℝ)=(m : ℝ) := by exact_mod_cast VG
  have gCap : (g : ℝ) ≤ N^(1/4096 : ℝ) := by
    exact (by exact_mod_cast gSmall : (g : ℝ) ≤ (thinHighGcdCap n : ℝ)).trans (Nat.floor_le (by positivity))
  have eCap : (e : ℝ) ≤ N^(1/4096 : ℝ) :=
    (show (e : ℝ) ≤ (g : ℝ) by exact_mod_cast Nat.le_of_dvd g0 eg).trans gCap
  have vCap : (v : ℝ) ≤ N^(37/64 : ℝ) :=
    (show (v : ℝ) ≤ (m : ℝ) by exact_mod_cast Nat.div_le_self m g).trans mUpper
  have gcdCap : (v.gcd c.val : ℝ) ≤ N^(1/2048 : ℝ) := by
    have dvd : v.gcd (n/g) ∣ m.gcd n := Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans ⟨g,VG.symm⟩)
      ((Nat.gcd_dvd_right _ _).trans ⟨g,(Nat.div_mul_cancel gn).symm⟩)
    have bound : v.gcd c.val ≤ sparseTargetDivisorCap n := (gcd_val_nat_cast_le_gcd (m := v) (n/g)).trans
      ((Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ m0) dvd).trans mTarget)
    exact (show (v.gcd c.val : ℝ) ≤ sparseTargetDivisorCap n by exact_mod_cast bound).trans
      (Nat.floor_le (by positivity))
  have kLo : (32 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
  have kHi : (k : ℝ) ≤ 63 := by exact_mod_cast (mem_Icc.mp hk).2
  have xLo : 127/1024 ≤ x := by unfold x; linarith only [kLo]
  have xHi : x ≤ 1/4 := by unfold x; linarith only [kHi]
  have aPow : primeHyperbolaFactorFloor n (k+1) = ⌊N^(x+17/4096)⌋₊ := by
    unfold primeHyperbolaFactorFloor x N
    rw [Nat.cast_add,Nat.cast_one]
    congr 2
    ring
  have aCap : (A : ℝ) ≤ N^(x+17/4096) :=
    (by exact_mod_cast Nat.div_le_self (primeHyperbolaFactorFloor n (k+1)) e :
      (A : ℝ) ≤ (primeHyperbolaFactorFloor n (k+1) : ℝ)).trans (by rw [aPow]; exact Nat.floor_le (by positivity))
  have aSmall (a : ℕ) (ha : a ∈ I) :
      aLo/e < a ∧ a ≤ aHi/e ∧ (e*a).gcd g=e ∧ a.Coprime v := by
    have H := mem_filter.mp ha
    exact ⟨(mem_Ioc.mp H.1).1,(mem_Ioc.mp H.1).2,H.2.1,H.2.2⟩
  have Icap : I ⊆ Icc 1 A := fun a ha =>
    mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (aSmall a ha).1,
      (aSmall a ha).2.1.trans (Nat.div_le_div_right (min_le_right _ _))⟩
  have leftWeight : ∀ a ∈ I, ‖α a‖ ≤ T := by
    intro a ha
    have an : e*a ≤ n := calc
      _ ≤ aHi := by
        rw [Nat.mul_comm]
        exact (Nat.le_div_iff_mul_le e0).mp (aSmall a ha).2.1
      _ ≤ lowCut n := min_le_left _ _
      _ ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le N1 (by norm_num))
    exact (norm_leftBandMoebius_le n (e*a)).trans (divN _ an)
  have Sdiv : S ≤ r₀/g := Nat.div_le_self (r₀/g) _
  have span : S ≤ v := Sdiv.trans (Nat.div_le_div_right rM)
  have rightWeight : ∀ j ∈ J, ‖β j‖ ≤ T*logBudget n := by
    intro j hj
    have data : j ∈ Ioc 0 (S : ℤ) ∧ IsUnit (j : ZMod v) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    have jTop := (mem_Ioc.mp data.1).2
    have jt : j.toNat ≤ S := by simpa only [Int.toNat_natCast] using Int.toNat_le_toNat jTop
    have bound : h*j.toNat ≤ n := calc
      _ ≤ g*(r₀/g) := Nat.mul_le_mul hG (jt.trans Sdiv)
      _ ≤ r₀ := Nat.mul_div_le _ _
      _ ≤ n := rN
    exact norm_restricted_vaughan_factor_le (vaughanShortCut n) bound Nat.Prime divN
  have log : 1+Real.log (v : ℝ) ≤ logBudget n := by
    unfold logBudget
    have upper : (v : ℝ) ≤ n := by exact_mod_cast vN
    exact add_le_add (le_refl _) (Real.log_le_log (by exact_mod_cast v0) (by linarith only [upper]))
  have cofFloor : N^x ≤ ((aLo/e : ℕ) : ℝ)+1 := by
    have less : aLo < (aLo/e+1)*e :=
      (Nat.div_lt_iff_lt_mul e0).mp (Nat.lt_succ_self _)
    have rank : (primeHyperbolaFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*(e : ℝ) := by
      have le : primeHyperbolaFactorFloor n k+1 ≤ (aLo/e+1)*e :=
        Nat.succ_le_of_lt ((le_max_right _ _).trans_lt less)
      exact_mod_cast le
    have ground : N^((k : ℝ)/256) ≤ (((aLo/e : ℕ) : ℝ)+1)*(e : ℝ) :=
      (Nat.lt_floor_add_one _).le.trans rank
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos N0 (1/4096 : ℝ))).mp
    calc
      _ = N^((k : ℝ)/256) := by rw [← Real.rpow_add N0]; unfold x; simp
      _ ≤ _ := ground
      _ ≤ _ := mul_le_mul_of_nonneg_left eCap (by positivity)
  have cofactor : S*(aLo/e+1) ≤ r₀/g := Nat.div_mul_le_self _ _
  have product : (S : ℝ)*(v : ℝ)*(g : ℝ)^2 ≤ 2*N^(1+3/8192-x) := by
    have cofactorR : (S : ℝ)*(((aLo/e : ℕ) : ℝ)+1) ≤ ((r₀/g : ℕ) : ℝ) := by exact_mod_cast cofactor
    have divideR : ((r₀/g : ℕ) : ℝ)*(g : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast Nat.div_mul_le_self r₀ g
    have rp : (r₀ : ℝ)*(m : ℝ) ≤ 2*N^(1+3/8192 : ℝ) := by
      apply (show (r₀ : ℝ)*(m : ℝ) ≤ weilNearProductCap n from by exact_mod_cast rProd).trans
      unfold weilNearProductCap
      push_cast
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos N0 x)).mp
    calc
      _ ≤ ((S : ℝ)*(v : ℝ)*(g : ℝ)^2)*(((aLo/e : ℕ) : ℝ)+1) :=
        mul_le_mul_of_nonneg_left cofFloor (by positivity)
      _ = ((S : ℝ)*(((aLo/e : ℕ) : ℝ)+1))*(g : ℝ)*((v : ℝ)*(g : ℝ)) := by ring
      _ ≤ ((r₀/g : ℕ) : ℝ)*(g : ℝ)*((v : ℝ)*(g : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cofactorR gR.le) (by positivity)
      _ ≤ (r₀ : ℝ)*(m : ℝ) := by rw [vProd]; exact mul_le_mul_of_nonneg_right divideR (by positivity)
      _ ≤ _ := rp
      _ = _ := by rw [mul_assoc,← Real.rpow_add N0,sub_add_cancel]
  have eSmall : e ≤ aLo := by
    calc
      _ ≤ g := Nat.le_of_dvd g0 eg
      _ ≤ thinHighGcdCap n := gSmall
      _ ≤ primeHyperbolaFactorFloor n k := by
        apply Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le N1 (by linarith only [kLo]))
      _ ≤ _ := le_max_right _ _
  have sLt : S < v := by
    have q0 : 1 ≤ aLo/e := Nat.div_pos eSmall e0
    have h₂ : S*2 ≤ v := (Nat.mul_le_mul_left S (by omega : 2≤aLo/e+1)).trans
      (cofactor.trans (Nat.div_le_div_right rM))
    omega
  have mLo : N^(535/1024 : ℝ) ≤ (m : ℝ) :=
    (Nat.lt_floor_add_one _).le.trans (by exact_mod_cast Nat.succ_le_of_lt mWide)
  have aLt : A < v := by
    have real : (A : ℝ) < (v : ℝ) := by
      apply (mul_lt_mul_iff_left₀ gR).mp
      calc
        _ ≤ N^(x+17/4096)*N^(1/4096 : ℝ) := mul_le_mul aCap gCap (by positivity) (by positivity)
        _ = N^(x+18/4096) := by rw [← Real.rpow_add N0]; congr 1 <;> ring
        _ < N^(535/1024 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt nBig (by linarith only [xHi])
        _ ≤ (m : ℝ) := mLo
        _ = _ := vProd.symm
    exact_mod_cast real
  have divV (z : ℕ) (hz : z ≤ 4*v^3) : (z.divisors.card : ℝ) ≤ T :=
    divisors z (hz.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left vN 3)))
  rw [← vProd]
  exact norm_gated_inverse_ramp_saving_double_fourth c I Icap (fun a ha => (aSmall a ha).2.2.2)
    α β (fun a => (l₀/g/a : ℕ)) (fun a => (r₀/g/a : ℕ)) aLt sLt T1 (one_le_logBudget n)
    leftWeight rightWeight divV log (rightInverseRampPhase (n/g) v)
    (fun a j => right_inverse_ramp_phase_cast (n/g) v a j)
    n1 g0 xLo xHi aCap product vCap gcdCap

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_double_fourth_row -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale DyadicMixedB4PairIntegral
open scoped Classical

noncomputable section

def weilRemainingNearRightRampBlocks (n m : ℕ) : Finset ℕ :=
  (Icc 32 63).filter (fun k => k ∉ weilAdaptiveRightRampBlocks n m)

def weilRemainingNearRightRampRow (n m : ℕ) (lower upper : ℕ → ℕ) : ℂ :=
  ∑ g ∈ weilNearRowDivisors n m, ∑ e ∈ g.divisors, ∑ k ∈ weilRemainingNearRightRampBlocks n m,
    rightInverseRampWindow n m g e k (lower g) (upper g)

def weilRemainingNearRightRampSlice (R : ℕ → Finset RightLowWaveIndex)
    (lower upper : ModerateLowBounds) (n : ℕ) : ℂ :=
  ∑ j ∈ R n, rightLowWaveWeight j *
    weilRemainingNearRightRampRow n (rightLowWaveStep j) (lower n j) (upper n j)

theorem norm_weil_remaining_near_right_ramp_row_le {n m : ℕ} {lower upper : ℕ → ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (mSize : (m : ℝ) ≤ (n : ℝ)^(37/64 : ℝ))
    (mWide : widerLowFarModulusCap n < m) (mTarget : m.gcd n ≤ sparseTargetDivisorCap n)
    (rM : ∀ g, upper g ≤ m) (rProd : ∀ g, (upper g)*m ≤ weilNearProductCap n)
    {T : ℝ} (T1 : 1 ≤ T) (divs : ∀ b ≤ 4*n^3, (b.divisors.card : ℝ) ≤ T) :
    ‖weilRemainingNearRightRampRow n m lower upper‖ ≤
      (512*T^6*logBudget n^3*(n : ℝ)^(127/128 : ℝ))*(1/(m : ℝ)) := by
  let G := weilNearRowDivisors n m
  let B := (16*T^4*logBudget n^3*(n : ℝ)^(127/128 : ℝ))/(m : ℝ)
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have mR : (0 : ℝ) < m := by exact_mod_cast m0
  have n1 : 1 ≤ n := m0.trans_le mN
  have divN (z : ℕ) (hz : z ≤ n) : (z.divisors.card : ℝ) ≤ T := by
    apply divs z (hz.trans ?_)
    have p : n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
    omega
  have B0 : 0 ≤ B := by unfold B; positivity
  have Gcard : (#G : ℝ) ≤ T :=
    (show (#G : ℝ) ≤ (n.divisors.card : ℝ) from by
      exact_mod_cast card_filter_le n.divisors (fun g => g ∣ m ∧ g ≤ thinHighGcdCap n)).trans (divN n le_rfl)
  have blockCard : (#(weilRemainingNearRightRampBlocks n m) : ℝ) ≤ 32 := by
    have cap : #(weilRemainingNearRightRampBlocks n m) ≤ #(Icc (32 : ℕ) 63) := card_filter_le _ _
    have h : #(Icc (32 : ℕ) 63) = 32 := by norm_num [Nat.card_Icc]
    rw [h] at cap
    exact_mod_cast cap
  have two (g : ℕ) (hg : g ∈ G) :
      ‖∑ e ∈ g.divisors, ∑ k ∈ weilRemainingNearRightRampBlocks n m, rightInverseRampWindow n m g e k (lower g) (upper g)‖ ≤
        T*(32*B) := by
    obtain ⟨hn,hm,hs⟩ := mem_filter.mp hg
    have gn := (Nat.mem_divisors.mp hn).1
    have g0 := Nat.pos_of_dvd_of_pos gn (m0.trans_le mN)
    have gN := Nat.le_of_dvd (m0.trans_le mN) gn
    have one (e : ℕ) (he : e ∈ g.divisors) :
        ‖∑ k ∈ weilRemainingNearRightRampBlocks n m, rightInverseRampWindow n m g e k (lower g) (upper g)‖ ≤ 32*B := by
      have eg := (Nat.mem_divisors.mp he).1
      have e0 := Nat.pos_of_dvd_of_pos eg g0
      calc
        _ ≤ ∑ k ∈ weilRemainingNearRightRampBlocks n m, ‖rightInverseRampWindow n m g e k (lower g) (upper g)‖ := norm_sum_le _ _
        _ ≤ ∑ _ ∈ weilRemainingNearRightRampBlocks n m, B := by
          refine sum_le_sum fun k hk => ?_
          unfold B
          apply (le_div_iff₀ mR).mpr
          rw [mul_comm]
          exact norm_inner_low_large_factor_inverse_ramp_window_le m0 mN mSize mWide mTarget g0 gn hm hs e0 eg (mem_filter.mp hk).1
            (rM g) (rProd g) T1 divs
        _ = (#(weilRemainingNearRightRampBlocks n m) : ℝ)*B := by rw [sum_const,nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right blockCard B0
    calc
      _ ≤ ∑ e ∈ g.divisors, ‖∑ k ∈ weilRemainingNearRightRampBlocks n m, rightInverseRampWindow n m g e k (lower g) (upper g)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ g.divisors, 32*B := sum_le_sum one
      _ = (#g.divisors : ℝ)*(32*B) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (divN g gN) (by positivity)
  calc
    _ ≤ ∑ g ∈ G, ‖∑ e ∈ g.divisors, ∑ k ∈ weilRemainingNearRightRampBlocks n m, rightInverseRampWindow n m g e k (lower g) (upper g)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ G, T*(32*B) := sum_le_sum two
    _ = (#G : ℝ)*(T*(32*B)) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ T*(T*(32*B)) := mul_le_mul_of_nonneg_right Gcard (by positivity)
    _ = _ := by unfold B; ring

set_option maxHeartbeats 1200000 in
theorem weil_remaining_near_right_ramp_saving
    (R : ℕ → Finset RightLowWaveIndex) (lower upper : ModerateLowBounds)
    (support : ∀ n, ∀ j ∈ R n, j ∈ rightLowWaveItems n ∧
      (rightLowWaveStep j : ℝ) ≤ (n : ℝ)^(37/64 : ℝ) ∧
      widerLowFarModulusCap n < rightLowWaveStep j ∧ (rightLowWaveStep j).gcd n ≤ sparseTargetDivisorCap n)
    (rM : ∀ n, ∀ j ∈ R n, ∀ g, upper n j g ≤ rightLowWaveStep j)
    (rProd : ∀ n, ∀ j ∈ R n, ∀ g, (upper n j g)*(rightLowWaveStep j) ≤ weilNearProductCap n) :
    saving (weilRemainingNearRightRampSlice R lower upper) := by
  apply saving_of_weil_near_growth _ 512 (by norm_num)
  intro n n1 T T1 divs
  let L := logBudget n
  let J := R n
  let B := 512*T^6*L^3*(n : ℝ)^(127/128 : ℝ)
  let W := T^3*L
  have subset : J ⊆ rightLowWaveItems n := fun j hj => (support n j hj).1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have W0 : 0 ≤ W := by unfold W; positivity
  have B0 : 0 ≤ B := by unfold B; positivity
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have divN (m : ℕ) (hm : m ≤ n) : (m.divisors.card : ℝ) ≤ T := by
    apply divs m (hm.trans ?_)
    have p : n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
    omega
  have massH : (∑ m ∈ Icc 1 n, 1/(m : ℝ)) ≤ L := calc
    _ = (harmonic n : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    _ ≤ 1+Real.log n := by exact_mod_cast harmonic_le_one_add_log n
    _ ≤ L := by
      unfold L logBudget
      exact add_le_add (le_refl _) (Real.log_le_log (zero_lt_one.trans_le nR) (by linarith))
  have step (j : RightLowWaveIndex) (hj : j ∈ J) : rightLowWaveStep j ∈ Icc 1 n :=
    bilateral_right_low_step_range (subset hj)
  have weighted : (∑ j ∈ J, ‖rightLowWaveWeight j‖*(1/(rightLowWaveStep j : ℝ))) ≤ W*L := by
    refine (sum_norm_mul_le_of_step_mass J rightLowWaveStep rightLowWaveWeight (fun m => 1/(m : ℝ))
      step (fun _ _ => by positivity) ?_).trans (mul_le_mul_of_nonneg_left massH W0)
    intro m hm
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ subset)
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_right_low_step_mass T1 divN m hm)
  have each (j : RightLowWaveIndex) (hj : j ∈ J) :
      ‖weilRemainingNearRightRampRow n (rightLowWaveStep j) (lower n j) (upper n j)‖ ≤ B*(1/(rightLowWaveStep j : ℝ)) := by
    obtain ⟨_,size,wide,gcd⟩ := support n j hj
    obtain ⟨p,q⟩ := mem_Icc.mp (step j hj)
    exact norm_weil_remaining_near_right_ramp_row_le p q size wide gcd (rM n j hj) (rProd n j hj) T1 divs
  unfold weilRemainingNearRightRampSlice
  calc
    _ ≤ ∑ j ∈ J, ‖rightLowWaveWeight j*weilRemainingNearRightRampRow n (rightLowWaveStep j) (lower n j) (upper n j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ‖rightLowWaveWeight j‖*(B*(1/(rightLowWaveStep j : ℝ))) := by
      refine sum_le_sum fun j hj => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (each j hj) (norm_nonneg _)
    _ = B*(∑ j ∈ J, ‖rightLowWaveWeight j‖*(1/(rightLowWaveStep j : ℝ))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ B*(W*L) := mul_le_mul_of_nonneg_left weighted B0
    _ = 512*(n : ℝ)^(127/128 : ℝ)*T^9*logBudget n^5 := by unfold B W L; ring
    _ ≤ _ := by
      have power : (n : ℝ)^(127/128 : ℝ) ≤ (n : ℝ)^(8191/8192 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le nR (by norm_num)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left power (by norm_num)) (by positivity)) (by positivity)


def weilRemainingNearRightRampFactor (n m a : ℕ) : Prop :=
  ∃ k ∈ weilRemainingNearRightRampBlocks n m, a ∈ primeHyperbolaFactorBlock n k

theorem weil_remaining_near_right_ramp_factor_lower {n m a : ℕ}
    (n1 : 1 ≤ n) (h : weilRemainingNearRightRampFactor n m a) :
    primeHyperbolaFactorFloor n 32 < a := by
  obtain ⟨k,hk,ha⟩ := h
  have le := prime_hyperbola_factor_floor_mono n1 (mem_Icc.mp (mem_filter.mp hk).1).1
  exact le.trans_lt ((le_max_right _ _).trans_lt (mem_Ioc.mp ha).1)

def weilRemainingNearRightRampRowItems (n m : ℕ) (lower upper : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (bilateralLeftWaveItems n).filter fun i =>
    let u := leftBilinearStep i
    let g := u.gcd m
    g ∈ weilNearRowDivisors n m ∧ lower g < u ∧ u ≤ upper g ∧
      weilRemainingNearRightRampFactor n m i.1

theorem weil_remaining_near_right_ramp_row_eq_selected {n m : ℕ} {lower upper : ℕ → ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (lLeft : ∀ g, leftMediumCap n ≤ lower g) (rUpper : ∀ g, upper g ≤ extendedWideStepCap n) :
    weilRemainingNearRightRampRow n m lower upper =
      ∑ i ∈ weilRemainingNearRightRampRowItems n m lower upper,
        leftPrimeWeight n i * (rightInverseRamp n (leftBilinearStep i) m : ℂ) := by
  let I := weilRemainingNearRightRampRowItems n m lower upper
  let G := weilNearRowDivisors n m
  let K := weilRemainingNearRightRampBlocks n m
  let d (i : ℕ × ℕ) := (leftBilinearStep i).gcd m
  let w (i : ℕ × ℕ) := leftPrimeWeight n i * (rightInverseRamp n (leftBilinearStep i) m : ℂ)
  have n1 : 1 ≤ n := m0.trans_le mN
  have mapsG : ∀ i ∈ I, d i ∈ G := fun _ hi => (mem_filter.mp hi).2.1
  change weilRemainingNearRightRampRow n m lower upper = ∑ i ∈ I, w i
  rw [← sum_fiberwise_of_maps_to mapsG w]
  unfold weilRemainingNearRightRampRow
  refine sum_congr rfl fun g hg => ?_
  let I₁ := I.filter fun i => d i = g
  let aGcd (i : ℕ × ℕ) := i.1.gcd g
  have gData := mem_filter.mp hg
  have gn := (Nat.mem_divisors.mp gData.1).1
  have g0 := Nat.pos_of_dvd_of_pos gn n1
  have gq := gData.2.1
  have mapsE : ∀ i ∈ I₁, aGcd i ∈ g.divisors :=
    fun i _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right i.1 g,g0.ne'⟩
  change (∑ e ∈ g.divisors, ∑ k ∈ K, rightInverseRampWindow n m g e k (lower g) (upper g)) = ∑ i ∈ I₁, w i
  rw [← sum_fiberwise_of_maps_to mapsE w]
  refine sum_congr rfl fun e he => ?_
  let I₂ := I₁.filter fun i => aGcd i=e
  have eg := (Nat.mem_divisors.mp he).1
  have e0 := Nat.pos_of_dvd_of_pos eg g0
  have eqFilter (k : ℕ) (hk : k ∈ K) : moderateLowDividedHyperbolaLeftItems n m g e k (lower g) (upper g) =
      I₂.filter fun i => i.1 ∈ primeHyperbolaFactorBlock n k := by
    ext i
    constructor
    · intro hi
      obtain ⟨left,fac,gg,ee,lo,up⟩ := mem_filter.mp hi
      have dG : d i ∈ G := by
        change (leftBilinearStep i).gcd m ∈ weilNearRowDivisors n m
        rw [gg]
        exact hg
      have rel : (leftBilinearStep i).gcd m=g := gg
      have base : i ∈ I := mem_filter.mpr ⟨left,dG,by rw [rel]; exact lo,by rw [rel]; exact up,⟨k,hk,fac⟩⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨base,gg⟩,ee⟩,fac⟩
    · intro hi
      obtain ⟨hi₂,fac⟩ := mem_filter.mp hi
      obtain ⟨hi₁,ee⟩ := mem_filter.mp hi₂
      obtain ⟨hi₀,gg⟩ := mem_filter.mp hi₁
      obtain ⟨left,_,lo,up,_⟩ := mem_filter.mp hi₀
      have rel : (leftBilinearStep i).gcd m=g := gg
      exact mem_filter.mpr ⟨left,fac,gg,ee,by rwa [rel] at lo,by rwa [rel] at up⟩
  calc
    (∑ k ∈ K, rightInverseRampWindow n m g e k (lower g) (upper g)) =
        ∑ k ∈ K, ∑ i ∈ I₂.filter (fun i => i.1 ∈ primeHyperbolaFactorBlock n k), w i := by
      refine sum_congr rfl fun k hk => ?_
      rw [← eqFilter k hk]
      exact right_inverse_ramp_window_eq_selected m0 mN (lLeft g) (rUpper g) g0 gq e0 eg
    _ = ∑ i ∈ I₂, ∑ k ∈ K, if i.1 ∈ primeHyperbolaFactorBlock n k then w i else 0 := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = ∑ i ∈ I₂, w i := by
      refine sum_congr rfl fun i hi => ?_
      have left : i ∈ bilateralLeftWaveItems n :=
        (mem_filter.mp (mem_filter.mp (mem_filter.mp hi).1).1).1
      have aRange := (mem_product.mp (mem_filter.mp (mem_filter.mp left).1).1).1
      obtain ⟨b,_,unique⟩ := prime_hyperbola_factor_blocks_cover n1 aRange
      have hi₀ : i ∈ I := (mem_filter.mp (mem_filter.mp hi).1).1
      obtain ⟨k,kMem,hk⟩ := (mem_filter.mp hi₀).2.2.2.2
      have enlarge (l : ℕ) (hl : l ∈ K) : l ∈ Icc 16 63 := by
        have data := mem_Icc.mp (mem_filter.mp hl).1
        exact mem_Icc.mpr ⟨(by decide : (16 : ℕ) ≤ 32).trans data.1,data.2⟩
      rw [sum_eq_single_of_mem k kMem]
      · exact ite_eq_left hk
      · intro k' hk' neq
        exact ite_eq_right (fun h => neq ((unique k' ⟨enlarge k' hk',h⟩).trans
          (unique k ⟨enlarge k kMem,hk⟩).symm))


theorem weil_remaining_near_right_ramp_factor_iff {n v a : ℕ}
    (n1 : 1 ≤ n) (range : a ∈ Ioc (cutoffU n) (lowCut n)) :
    weilRemainingNearRightRampFactor n v a ↔
      primeHyperbolaFactorFloor n 32 < a ∧ ¬weilAdaptiveRightRampFactor n v a := by
  obtain ⟨p,_,unique⟩ := prime_hyperbola_factor_blocks_cover n1 range
  have enlarge {k : ℕ} (hk : k ∈ Icc 32 63) : k ∈ Icc 16 63 :=
    mem_Icc.mpr ⟨(by decide : (16 : ℕ) ≤ 32).trans (mem_Icc.mp hk).1,(mem_Icc.mp hk).2⟩
  constructor
  · rintro ⟨k,hk,hka⟩
    refine ⟨weil_remaining_near_right_ramp_factor_lower n1 ⟨k,hk,hka⟩,?_⟩
    rintro ⟨l,hl,hla⟩
    have eq : l=k := (unique l ⟨enlarge (mem_filter.mp hl).1,hla⟩).trans
      (unique k ⟨enlarge (mem_filter.mp hk).1,hka⟩).symm
    exact (mem_filter.mp hk).2 (eq ▸ hl)
  · rintro ⟨large,absent⟩
    obtain ⟨k,⟨hk,hka⟩,_⟩ := prime_hyperbola_factor_blocks_cover n1 range
    have k32 : 32 ≤ k := by
      by_contra! h
      exact large.not_ge (((mem_Ioc.mp hka).2.trans (min_le_right _ _)).trans
        (prime_hyperbola_factor_floor_mono n1 (Nat.succ_le_of_lt h)))
    exact ⟨k,mem_filter.mpr ⟨mem_Icc.mpr ⟨k32,(mem_Icc.mp hk).2⟩,
      fun kMem => absent ⟨k,kMem,hka⟩⟩,hka⟩

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_near_product_support_mass -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

theorem norm_near_divisibility_supported_pair_sum_le {ι κ : Type*} {n P : ℕ} (D : Finset ℕ)
    (I : Finset ι) (J : Finset κ) (u : ι → ℕ) (v : κ → ℕ)
    (a : ι → ℂ) (b : κ → ℂ) (f : ι → κ → ℂ) {W : ℝ} (W0 : 0 ≤ W)
    (d0 : ∀ d ∈ D, 0 < d) (ui : ∀ i ∈ I, u i ∈ Icc 1 n)
    (vj : ∀ j ∈ J, v j ∈ Icc 1 n)
    (leftMass : ∀ q ∈ Icc 1 n, (∑ i ∈ I.filter (fun i => u i=q), ‖a i‖) ≤ W)
    (rightMass : ∀ q ∈ Icc 1 n, (∑ j ∈ J.filter (fun j => v j=q), ‖b j‖) ≤ W)
    (normF : ∀ i ∈ I, ∀ j ∈ J, ‖f i j‖ ≤ 1)
    (support : ∀ i ∈ I, ∀ j ∈ J, f i j ≠ 0 → u i*v j ≤ P ∧ ∃ d ∈ D, d ∣ u i) :
    ‖∑ i ∈ I, ∑ j ∈ J, a i*b j*f i j‖ ≤
      W^2*(P : ℝ)*(1+Real.log n)*(∑ d ∈ D, 1/(d : ℝ)) := by
  let bad (i : ι) : Prop := ∃ d ∈ D, d ∣ u i
  let F (i : ι) := ‖a i‖*((P : ℝ)/(u i : ℝ))
  have F0 (i : ι) : 0 ≤ F i := by unfold F; positivity
  have perLeft (i : ι) (hi : i ∈ I) :
      ‖∑ j ∈ J, a i*b j*f i j‖ ≤ W*(if bad i then F i else 0) := by
    by_cases hbad : bad i
    · rw [if_pos hbad]
      let J₀ := J.filter fun j => v j ≤ P/u i
      have u0 : 0 < u i := (mem_Icc.mp (ui i hi)).1
      have sub : J₀ ⊆ J := filter_subset _ _
      have zero (j : κ) (hj : j ∈ J) (h : j ∉ J₀) : a i*b j*f i j=0 := by
        by_cases hz : f i j=0
        · simp only [hz,mul_zero]
        · exfalso
          have val := (support i hi j hj hz).1
          rw [Nat.mul_comm] at val
          exact h (mem_filter.mpr ⟨hj,(Nat.le_div_iff_mul_le u0).mpr val⟩)
      have supportEq : (∑ j ∈ J₀, a i*b j*f i j) = ∑ j ∈ J, a i*b j*f i j :=
        sum_subset sub zero
      have mass : (∑ j ∈ J₀, ‖b j‖) ≤ W*((P : ℝ)/(u i : ℝ)) := by
        have range (j : κ) (hj : j ∈ J₀) : v j ∈ Icc 1 (P/u i) :=
          mem_Icc.mpr ⟨(mem_Icc.mp (vj j (sub hj))).1,(mem_filter.mp hj).2⟩
        have weights (q : ℕ) (hq : q ∈ Icc 1 (P/u i)) :
            (∑ j ∈ J₀.filter (fun j => v j=q), ‖b j‖) ≤ W := by
          by_cases hb : q ≤ n
          · exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ sub)
              (fun _ _ _ => norm_nonneg _)).trans (rightMass q (mem_Icc.mpr ⟨(mem_Icc.mp hq).1,hb⟩))
          · have empty : (J₀.filter (fun j => v j=q)) = ∅ := by
              apply eq_empty_iff_forall_notMem.mpr
              intro j hj
              have h := (mem_Icc.mp (vj j (sub (mem_filter.mp hj).1))).2
              rw [(mem_filter.mp hj).2] at h
              exact hb h
            rw [empty,sum_empty]
            exact W0
        have h := divisible_constant_step_mass_le (P/u i) 1 J₀ v b W0 range weights
        simp only [divisibleStepMass,one_dvd,filter_true,mul_one,Nat.cast_one,div_one] at h
        exact h.trans (mul_le_mul_of_nonneg_left Nat.cast_div_le W0)
      rw [← supportEq]
      calc
        _ ≤ ∑ j ∈ J₀, ‖a i*b j*f i j‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ J₀, ‖a i‖*‖b j‖ := by
          refine sum_le_sum fun j hj => ?_
          rw [norm_mul,norm_mul]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (normF i hi j (sub hj))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ‖a i‖*(∑ j ∈ J₀, ‖b j‖) := (mul_sum ..).symm
        _ ≤ ‖a i‖*(W*((P : ℝ)/(u i : ℝ))) :=
          mul_le_mul_of_nonneg_left mass (norm_nonneg _)
        _ = _ := by unfold F; ring
    · rw [if_neg hbad,mul_zero]
      have vanish : (∑ j ∈ J, a i*b j*f i j) = 0 := by
        refine sum_eq_zero fun j hj => ?_
        by_cases hz : f i j=0
        · simp only [hz,mul_zero]
        · exact False.elim (hbad (support i hi j hj hz).2)
      rw [vanish,norm_zero]
  have cover (i : ι) :
      (if bad i then F i else 0) ≤ ∑ d ∈ D, if d ∣ u i then F i else 0 := by
    by_cases h : bad i
    · obtain ⟨d,hd,hu⟩ := h
      rw [if_pos (show bad i from ⟨d,hd,hu⟩)]
      calc
        _ = (if d ∣ u i then F i else 0) := (if_pos hu).symm
        _ ≤ _ := single_le_sum (s := D) (f := fun e : ℕ => if e ∣ u i then F i else 0)
          (fun e _ => by split_ifs <;> positivity) hd
    · rw [if_neg h]
      exact sum_nonneg fun d _ => by split_ifs <;> positivity
  let L := 1+Real.log (n : ℝ)
  calc
    _ ≤ ∑ i ∈ I, ‖∑ j ∈ J, a i*b j*f i j‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ I, W*(if bad i then F i else 0) := sum_le_sum perLeft
    _ = W*(∑ i ∈ I, if bad i then F i else 0) := (mul_sum ..).symm
    _ ≤ W*(∑ i ∈ I,∑ d ∈ D, if d ∣ u i then F i else 0) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => cover i) W0
    _ = W*(∑ d ∈ D, divisibleStepMass d I u a (fun q => (P : ℝ)/q)) := by
      rw [sum_comm]
      simp only [divisibleStepMass,sum_filter,F]
    _ ≤ W*(∑ d ∈ D, W*((P : ℝ)/d*L)) := by
      exact mul_le_mul_of_nonneg_left (sum_le_sum fun d hd =>
        divisible_inverse_step_mass_le P n d (d0 d hd) I u a W0 ui leftMass) W0
    _ = _ := by
      rw [mul_sum,mul_sum]
      exact sum_congr rfl (fun _ _ => by unfold L; ring)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_prime_wider_inner_remainder -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail DyadicMixedB4Scale
open scoped Classical

noncomputable section

def smallModulusAddedBand (n u v : ℕ) : Prop :=
  v ≤ expandedHighModulusCap n ∧ u*v ≤ expandedHyperbolaProductCap n

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_middle_low_extension -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def middleLowMovedBand (lower upper : ℕ → ℕ) (n u v : ℕ) : Prop :=
  u ≤ extendedWideStepCap n ∧ lower n < v ∧ v ≤ upper n ∧ u*v ≤ expandedHyperbolaProductCap n

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_low_medium_prime_remainder -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def lowMiddleBand := middleLowMovedBand expandedHighModulusCap shortLowModulusCap

def lowWiderBand := middleLowMovedBand shortLowModulusCap widerLowFarModulusCap

def remainingExpandedLow (n u v : ℕ) : Prop :=
  ¬smallModulusAddedBand n u v ∧ ¬lowMiddleBand n u v ∧ ¬lowWiderBand n u v

theorem long_right_low_subset (n : ℕ) : longRightLowItems n ⊆ rightLowWaveItems n :=
  (filter_subset _ _).trans (filter_subset _ _)

theorem long_right_low_step_mass {n : ℕ} {T : ℝ} (T1 : 1 ≤ T)
    (d : ∀ z ≤ n, (z.divisors.card : ℝ) ≤ T) (q : ℕ) (hq : q ∈ Icc 1 n) :
    (∑ j ∈ (longRightLowItems n).filter (fun j => rightLowWaveStep j=q), ‖rightLowWaveWeight j‖) ≤ T^3*logBudget n :=
  (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (long_right_low_subset n))
    (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_right_low_step_mass T1 d q hq)

theorem saving_sum_two {f g : ℕ → ℂ} (a : saving f) (b : saving g) :
    saving (fun n => f n+g n) := by
  intro e ep
  obtain ⟨N,hN⟩ := a (e/2) (by positivity)
  obtain ⟨M,hM⟩ := b (e/2) (by positivity)
  exact ⟨max N M,fun n hn even =>
    (norm_add_le _ _).trans (by linarith only [hN n (by omega) even,hM n (by omega) even])⟩

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_square_step_cut -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def stepWithoutLargeSquare (n m : ℕ) : Prop := m ∉ highProperFrequencySupport n

theorem prime_left_mass_of_subset {n : ℕ} {I : Finset (ℕ × ℕ)}
    (subset : I ⊆ bilateralLeftWaveItems n) {T : ℝ} (T1 : 1 ≤ T)
    (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) (q : ℕ) (hq : q ∈ Icc 1 n) :
    (∑ i ∈ I.filter (fun i => leftBilinearStep i=q), ‖leftPrimeWeight n i‖) ≤ T^3*logBudget n :=
  (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ subset) (fun _ _ _ => norm_nonneg _)).trans
    (norm_bilateral_left_restricted_step_mass Nat.Prime (zero_le_one.trans T1) divisors q hq)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_near_left_cut -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

theorem norm_centered_inverse_ramp_le_one {m : ℕ} (m0 : 0 < m) (x : ℤ) :
    ‖(centeredInverseRamp m x : ℂ)‖ ≤ 1 := by
  let M := (m : ℝ)
  let y := ((x%(m : ℤ) : ℤ) : ℝ)
  have M1 : 1 ≤ M := by unfold M; exact_mod_cast m0
  have M0 := zero_lt_one.trans_le M1
  have mi : (0 : ℤ) < m := by exact_mod_cast m0
  have y0 : 0 ≤ y := by unfold y; exact_mod_cast Int.emod_nonneg x mi.ne'
  have ym : y ≤ M := by unfold y M; exact_mod_cast (Int.emod_lt_of_pos x mi).le
  have d0 : 0 ≤ (M-1)/(2*M) := div_nonneg (sub_nonneg.mpr M1) (by positivity)
  have d1 : (M-1)/(2*M) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith only [M1])
  have e0 : 0 ≤ y/M := div_nonneg y0 M0.le
  have e1 : y/M ≤ 1 := (div_le_iff₀ M0).mpr (by simpa only [one_mul] using ym)
  rw [Complex.norm_real,Real.norm_eq_abs]
  apply abs_le.mpr
  change -(1 : ℝ) ≤ (M-1)/(2*M)-y/M ∧ (M-1)/(2*M)-y/M ≤ 1
  constructor <;> linarith only [d0,d1,e0,e1]

private theorem sum_inverse_squares_le_telescoping (A n : ℕ) (A0 : 0 < A) (An : A ≤ n) :
    (∑ h ∈ Ioc A n, 1/(h : ℝ)^2) ≤ 1/(A : ℝ)-1/(n : ℝ) := by
  induction n,An using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have eq : Ioc A (k+1) = insert (k+1) (Ioc A k) := by
      ext x
      simp only [mem_Ioc,mem_insert]
      omega
    have outside : k+1 ∉ Ioc A k := by simp
    have kp : (0 : ℝ) < k := by exact_mod_cast (A0.trans_le hk)
    have interval : 1/((k+1 : ℕ) : ℝ)^2 ≤ 1/(k : ℝ)-1/((k+1 : ℕ) : ℝ) := by
      push_cast
      field_simp
      nlinarith
    rw [eq,sum_insert outside]
    linarith only [ih,interval]

def weilNearLeftKept (n u : ℕ) : Prop :=
  u.gcd n ≤ thinHighLeftDivisorCap n ∧ stepWithoutLargeSquare n u

def weilNearLeftCutDivisors (n : ℕ) : Finset ℕ :=
  (n.divisors.filter (fun d => thinHighLeftDivisorCap n < d)) ∪
    ((Ioc (highProperSquareCut n) n).image fun h => h^2)

theorem weil_near_left_cut_divisor_pos {n d : ℕ} (hd : d ∈ weilNearLeftCutDivisors n) : 0 < d := by
  unfold weilNearLeftCutDivisors at hd
  rcases mem_union.mp hd with hd|hd
  · exact (Nat.zero_le _).trans_lt (mem_filter.mp hd).2
  · obtain ⟨h,hh,rfl⟩ := mem_image.mp hd
    exact pow_pos ((Nat.zero_le _).trans_lt (mem_Ioc.mp hh).1) 2

theorem weil_near_left_cut_has_divisor {n u : ℕ} (n0 : 0 < n) (bad : ¬weilNearLeftKept n u) :
    ∃ d ∈ weilNearLeftCutDivisors n, d ∣ u := by
  by_cases gg : u.gcd n ≤ thinHighLeftDivisorCap n
  · have member : u ∈ highProperFrequencySupport n := by
      by_contra! h
      exact bad ⟨gg,h⟩
    have hdata := (mem_filter.mp member).2
    obtain ⟨h,hh,dvd⟩ := hdata
    exact ⟨h^2,mem_union.mpr (Or.inr (mem_image.mpr ⟨h,hh,rfl⟩)),dvd⟩
  · exact ⟨u.gcd n,mem_union.mpr (Or.inl (mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,n0.ne'⟩,Nat.lt_of_not_ge gg⟩)),Nat.gcd_dvd_left _ _⟩

theorem sum_inv_weil_near_left_cut_divisors_le {n : ℕ} (n1 : 1 ≤ n)
    {T : ℝ} (T1 : 1 ≤ T) (divs : (n.divisors.card : ℝ) ≤ T) :
    (∑ d ∈ weilNearLeftCutDivisors n, 1/(d : ℝ)) ≤ 3*T*(n : ℝ)^(-(1/2048) : ℝ) := by
  let N := (n : ℝ)
  let D := n.divisors.filter (fun d => thinHighLeftDivisorCap n < d)
  let A := highProperSquareCut n
  let S := (Ioc A n).image (fun h => h^2)
  let r (d : ℕ) := 1/(d : ℝ)
  have N1 : 1 ≤ N := by unfold N; exact_mod_cast n1
  have N0 := zero_lt_one.trans_le N1
  have T0 := zero_le_one.trans T1
  have Dcard : (#D : ℝ) ≤ T :=
    (show (#D : ℝ) ≤ n.divisors.card by exact_mod_cast card_filter_le _ _).trans divs
  have each (d : ℕ) (hd : d ∈ D) : r d ≤ N^(-(1/2048) : ℝ) := by
    have larger : N^(1/2048 : ℝ) ≤ (d : ℝ) := (Nat.lt_floor_add_one _).le.trans
      (by change (thinHighLeftDivisorCap n : ℝ)+1 ≤ (d : ℝ); exact_mod_cast Nat.succ_le_of_lt (mem_filter.mp hd).2)
    change 1/(d : ℝ) ≤ N^(-(1/2048) : ℝ)
    rw [Real.rpow_neg N0.le,← one_div]
    exact one_div_le_one_div_of_le (by positivity) larger
  have dBound : (∑ d ∈ D, r d) ≤ T*N^(-(1/2048) : ℝ) := by
    calc
      _ ≤ ∑ _ ∈ D, N^(-(1/2048) : ℝ) := sum_le_sum each
      _ = (#D : ℝ)*N^(-(1/2048) : ℝ) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right Dcard (by positivity)
  have A0 : 0 < A := Nat.le_floor (Real.one_le_rpow N1 (by norm_num))
  have An : A ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le N1 (by norm_num))
  have half : N^(1/768 : ℝ)/2 ≤ (A : ℝ) := floor_half_le (Real.one_le_rpow N1 (by norm_num))
  have sBound : (∑ d ∈ S, r d) ≤ 2*N^(-(1/2048) : ℝ) := by
    have unfoldSum : (∑ d ∈ S, r d) = ∑ h ∈ Ioc A n, 1/(h : ℝ)^2 := by
      unfold S
      rw [sum_image (Nat.pow_left_injective (n := 2) (by decide)).injOn]
      simp only [r,Nat.cast_pow]
    calc
      _ = _ := unfoldSum
      _ ≤ 1/(A : ℝ) := (sum_inverse_squares_le_telescoping A n A0 An).trans
        (sub_le_self _ (by positivity))
      _ ≤ 1/(N^(1/768 : ℝ)/2) := one_div_le_one_div_of_le (by positivity) half
      _ = 2*N^(-(1/768) : ℝ) := by rw [Real.rpow_neg N0.le]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le N1 (by norm_num)) (by norm_num)
  change (∑ d ∈ D ∪ S, r d) ≤ _
  calc
    _ ≤ (∑ d ∈ D, r d)+(∑ d ∈ S, r d) := by
      rw [← sum_union_inter]
      exact le_add_of_nonneg_right (sum_nonneg fun d _ => by unfold r; positivity)
    _ ≤ T*N^(-(1/2048) : ℝ)+2*N^(-(1/2048) : ℝ) := add_le_add dBound sBound
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right T1 (show 0 ≤ N^(-(1/2048) : ℝ) by positivity)
      nlinarith only [h]

def weilNearLeftCutFrom (I : ℕ → Finset (ℕ × ℕ)) (J : ℕ → Finset RightLowWaveIndex)
    (gate : ℕ → (ℕ × ℕ) → RightLowWaveIndex → Prop) (n : ℕ) : ℂ :=
  ∑ i ∈ I n, ∑ j ∈ J n, leftPrimeWeight n i*rightLowWaveWeight j*
    (if gate n i j ∧ ¬weilNearLeftKept n (leftBilinearStep i) then
      (rightInverseRamp n (leftBilinearStep i) (rightLowWaveStep j) : ℂ) else 0)

theorem weil_near_left_cut_saving (I : ℕ → Finset (ℕ × ℕ)) (J : ℕ → Finset RightLowWaveIndex)
    (gate : ℕ → (ℕ × ℕ) → RightLowWaveIndex → Prop)
    (left : ∀ n, I n ⊆ bilateralLeftWaveItems n)
    (right : ∀ n, J n ⊆ rightLowWaveItems n)
    (product : ∀ n i j, gate n i j → leftBilinearStep i*rightLowWaveStep j ≤ weilNearProductCap n) :
    saving (weilNearLeftCutFrom I J gate) := by
  apply saving_of_weil_near_growth _ 6 (by norm_num)
  intro n n1 T T1 divs
  let W := T^3*logBudget n
  let N := (n : ℝ)
  let L := logBudget n
  let u := leftBilinearStep
  let v := rightLowWaveStep
  let f (i : ℕ × ℕ) (j : RightLowWaveIndex) :=
    if gate n i j ∧ ¬weilNearLeftKept n (u i) then (rightInverseRamp n (u i) (v j) : ℂ) else 0
  have nR : 1 ≤ N := by unfold N; exact_mod_cast n1
  have N0 := zero_lt_one.trans_le nR
  have T0 := zero_le_one.trans T1
  have L1 : 1 ≤ L := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have W0 : 0 ≤ W := mul_nonneg (pow_nonneg T0 _) L0
  have divN (m : ℕ) (hm : m ≤ n) : (m.divisors.card : ℝ) ≤ T := by
    apply divs m (hm.trans ?_)
    have p : n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
    omega
  have pair := norm_near_divisibility_supported_pair_sum_le (P := weilNearProductCap n) (weilNearLeftCutDivisors n) (I n) (J n) u v
    (leftPrimeWeight n) rightLowWaveWeight f W0 (fun _ h => weil_near_left_cut_divisor_pos h)
    (fun i hi => bilateral_left_step_range (left n hi)) (fun j hj => bilateral_right_low_step_range (right n hj))
    (prime_left_mass_of_subset (left n) T1 divN) ?_ ?_ ?_
  rotate_left
  · intro q hq
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (right n))
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_right_low_step_mass T1 divN q hq)
  · intro i hi j hj
    unfold f
    split_ifs
    · have pos : 0 < v j := (mem_Icc.mp (bilateral_right_low_step_range (right n hj))).1
      have divPos := Nat.div_pos (Nat.le_of_dvd pos (Nat.gcd_dvd_right (u i) (v j)))
        (Nat.gcd_pos_of_pos_right (u i) pos)
      exact norm_centered_inverse_ramp_le_one divPos _
    · simp
  · intro i hi j hj nz
    unfold f at nz
    split_ifs at nz with h
    · exact ⟨product n i j h.1,weil_near_left_cut_has_divisor n1 h.2⟩
    · exact False.elim (nz rfl)
  have Pcap : (weilNearProductCap n : ℝ) ≤ 2*N^(1+3/8192 : ℝ) := by
    unfold weilNearProductCap
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
  have log : 1+Real.log (n : ℝ) ≤ L := by
    unfold L logBudget
    exact add_le_add (le_refl _) (Real.log_le_log N0 (by linarith))
  have Dcap := sum_inv_weil_near_left_cut_divisors_le n1 T1 (divN n le_rfl)
  calc
    _ ≤ W^2*(weilNearProductCap n : ℝ)*(1+Real.log n)*(∑ d ∈ weilNearLeftCutDivisors n, 1/(d : ℝ)) := pair
    _ ≤ W^2*(2*N^(1+3/8192 : ℝ))*L*(3*T*N^(-(1/2048) : ℝ)) := by
      have log0 : 0 ≤ 1+Real.log (n : ℝ) := add_nonneg zero_le_one (Real.log_nonneg nR)
      gcongr
    _ = 6*T^7*L^3*(N^(1+3/8192 : ℝ)*N^(-(1/2048) : ℝ)) := by unfold W L; ring
    _ = 6*T^7*L^3*N^(8191/8192 : ℝ) := by rw [← Real.rpow_add N0]; congr 2 <;> norm_num
    _ ≤ _ := by
      have pT : T^7 ≤ T^9 := pow_le_pow_right₀ T1 (by decide)
      have pL : L^3 ≤ L^5 := pow_le_pow_right₀ L1 (by decide)
      calc
        _ ≤ 6*T^9*L^5*N^(8191/8192 : ℝ) := by gcongr
        _ = _ := by unfold N L; ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_square_step_remainder -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def retainedLowTargetMask (n u v : ℕ) : Prop :=
  remainingExpandedLow n u v ∧ targetDivisorKept n v

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_long_low_geometry -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

theorem long_right_low_step_le_power {n : ℕ} {j : RightLowWaveIndex}
    (hj : j ∈ longRightLowItems n) : (rightLowWaveStep j : ℝ) ≤ (n : ℝ)^(37/64 : ℝ) := by
  have h := mem_sigma.mp (long_right_low_subset n hj)
  have left : (j.2 : ℝ) ≤ (n : ℝ)^(1/16 : ℝ) :=
    (show (j.2 : ℝ) ≤ cutoffU n by exact_mod_cast (mem_Icc.mp h.2).2.trans (min_le_left _ _)).trans
      (Nat.floor_le (by positivity))
  have right : (j.1 : ℝ) ≤ (n : ℝ)^(33/64 : ℝ) :=
    (show (j.1 : ℝ) ≤ rightLargeCofactorCut n by
      exact_mod_cast (mem_Ioc.mp h.1).2.trans (min_le_right _ _)).trans (Nat.floor_le (by positivity))
  have range := mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))
  have nr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from range.1.trans range.2)
  unfold rightLowWaveStep
  push_cast
  calc
    _ ≤ (n : ℝ)^(1/16 : ℝ)*(n : ℝ)^(33/64 : ℝ) := mul_le_mul left right (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add nr]; norm_num

theorem long_right_low_step_within_expanded {n : ℕ} (hn : 0 < n) {j : RightLowWaveIndex}
    (hj : j ∈ longRightLowItems n) : rightLowWaveStep j ≤ expandedWideStepCap n := by
  apply Nat.le_floor
  exact (long_right_low_step_le_power hj).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))

theorem long_right_low_gcd_eq {n : ℕ} {j : RightLowWaveIndex}
    (hj : j ∈ longRightLowItems n) : (rightLowWaveStep j).gcd n = j.2.gcd n := by
  obtain ⟨prime,nd⟩ := (mem_filter.mp (mem_filter.mp hj).1).2
  exact Nat.Coprime.gcd_mul_right_cancel j.2 ((Nat.Prime.coprime_iff_not_dvd prime).mpr nd)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_near_product_remainder -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def weilNearRightRows (n : ℕ) : Finset RightLowWaveIndex :=
  (longRightLowItems n).filter fun j =>
    let v := rightLowWaveStep j
    widerLowFarModulusCap n < v ∧ v.gcd n ≤ sparseTargetDivisorCap n ∧ v.gcd n ≤ targetDivisorCap n

def weilNearProductLower (n : ℕ) (j : RightLowWaveIndex) (_ : ℕ) : ℕ :=
  let v := rightLowWaveStep j
  max ⌊(n : ℝ)^(27/64 : ℝ)⌋₊
    (max (maximumStep n^2/v) (max (thinHighProductCap n/v) (highFarStripProductCap n/v)))

def weilNearProductUpper (n : ℕ) (j : RightLowWaveIndex) (_ : ℕ) : ℕ :=
  let v := rightLowWaveStep j
  min (extendedWideStepCap n) (min (expandedWideStepCap n) (min v (weilNearProductCap n/v)))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_near_product_mask -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def weilNearExtra (n : ℕ) (i : ℕ × ℕ) (v : ℕ) : Prop :=
  let u := leftBilinearStep i
  widerLowFarModulusCap n < v ∧ u ≤ extendedWideStepCap n ∧ u ≤ v ∧ u*v ≤ weilNearProductCap n ∧
    i.1 ≤ primeHyperbolaFactorFloor n 32

theorem symmetric_low_residue_decomposes {n u v : ℕ} (n0 : 0 < n) (hd : u.gcd v ∣ n) :
    symmetricResidueError n u v 0 =
      rightInverseRamp n u v+rightInverseRamp n v u := by
  unfold symmetricResidueError rightInverseRamp
  dsimp only
  rw [if_pos ⟨hd,by simpa only [Nat.mul_zero] using n0⟩,Nat.gcd_comm v u]
  simp only [Nat.cast_zero,sub_zero]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_adaptive_remainder -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def weilAdaptiveGroupGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  let g := u.gcd v
  g ∈ weilNearRowDivisors n v ∧ weilNearProductLower n j g < u ∧ u ≤ weilNearProductUpper n j g ∧
    weilAdaptiveRightRampFactor n v i.1

def weilAdaptiveRightRampKept (n : ℕ) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ weilNearRightRows n,
    leftPrimeWeight n i*rightLowWaveWeight j*
      (if weilAdaptiveGroupGate n i j ∧ weilNearLeftKept n (leftBilinearStep i) then
        (rightInverseRamp n (leftBilinearStep i) (rightLowWaveStep j) : ℂ) else 0)

private theorem adaptive_near_right_rows_sub_b13m101 (n : ℕ) : weilNearRightRows n ⊆ rightLowWaveItems n :=
  fun _ hj => long_right_low_subset n (mem_filter.mp hj).1

private theorem adaptive_near_upper_mul_le_b13m101 (n : ℕ) {j : RightLowWaveIndex} {g : ℕ} :
    weilNearProductUpper n j g*rightLowWaveStep j ≤ weilNearProductCap n := by
  calc
    _ ≤ (weilNearProductCap n/rightLowWaveStep j)*rightLowWaveStep j :=
      Nat.mul_le_mul_right _ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    _ ≤ _ := Nat.div_mul_le_self _ _

private theorem weil_adaptive_right_ramp_broad_saving :
    saving (weilAdaptiveRightRampSlice weilNearRightRows weilNearProductLower weilNearProductUpper) := by
  apply weil_adaptive_right_ramp_saving
  · intro n j hj
    exact ⟨adaptive_near_right_rows_sub_b13m101 n hj,long_right_low_step_le_power (mem_filter.mp hj).1,
      (mem_filter.mp hj).2.2.1⟩
  · intro n j hj g
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · intro n j hj g
    exact adaptive_near_upper_mul_le_b13m101 n

set_option maxHeartbeats 1200000 in
private theorem weil_adaptive_right_ramp_broad_eq {n : ℕ} :
    weilAdaptiveRightRampSlice weilNearRightRows weilNearProductLower weilNearProductUpper n =
      ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ weilNearRightRows n,
        leftPrimeWeight n i*rightLowWaveWeight j*
        (if weilAdaptiveGroupGate n i j then (rightInverseRamp n (leftBilinearStep i) (rightLowWaveStep j) : ℂ)
          else 0) := by
  unfold weilAdaptiveRightRampSlice
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have ranges := mem_Icc.mp (bilateral_right_low_step_range (adaptive_near_right_rows_sub_b13m101 n hj))
  have n1 : 1 ≤ n := ranges.1.trans ranges.2
  have lower (g : ℕ) : leftMediumCap n ≤ weilNearProductLower n j g :=
    (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n1) (by norm_num))).trans
      (le_max_left _ _)
  rw [weil_adaptive_right_ramp_row_eq_selected (upper := weilNearProductUpper n j) ranges.1 ranges.2 lower (fun _ => min_le_left _ _)]
  have items : weilAdaptiveRightRampRowItems n (rightLowWaveStep j) (weilNearProductLower n j) (weilNearProductUpper n j) =
      (bilateralLeftWaveItems n).filter (fun i => weilAdaptiveGroupGate n i j) := by
    ext i
    simp only [weilAdaptiveRightRampRowItems,mem_filter]
    rfl
  rw [items,sum_filter,mul_sum]
  refine sum_congr rfl fun i hi => ?_
  by_cases h : weilAdaptiveGroupGate n i j
  · simp only [if_pos h]
    rw [← mul_assoc,mul_comm (rightLowWaveWeight j) (leftPrimeWeight n i)]
  · simp only [if_neg h,mul_zero]

theorem weil_adaptive_right_ramp_kept_saving : saving weilAdaptiveRightRampKept := by
  let F := weilAdaptiveRightRampSlice weilNearRightRows weilNearProductLower weilNearProductUpper
  let E := weilNearLeftCutFrom bilateralLeftWaveItems weilNearRightRows weilAdaptiveGroupGate
  have correction : saving E :=
    weil_near_left_cut_saving bilateralLeftWaveItems weilNearRightRows weilAdaptiveGroupGate
      (fun _ _ h => h) adaptive_near_right_rows_sub_b13m101
      (fun n i j h => (Nat.mul_le_mul_right _ h.2.2.1).trans (adaptive_near_upper_mul_le_b13m101 n))
  have balance (n : ℕ) : weilAdaptiveRightRampKept n = F n-E n := by
    unfold F E weilAdaptiveRightRampKept weilNearLeftCutFrom
    rw [weil_adaptive_right_ramp_broad_eq,← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : weilAdaptiveGroupGate n i j <;> by_cases k : weilNearLeftKept n (leftBilinearStep i) <;>
      simp [h,k]
  have negCorrection : saving (fun n => -E n) := by
    intro ε ε0
    obtain ⟨N,hN⟩ := correction ε ε0
    exact ⟨N,fun n hn ev => by simpa only [norm_neg] using hN n hn ev⟩
  have S : saving (fun n => F n + (-E n)) := saving_sum_two weil_adaptive_right_ramp_broad_saving negCorrection
  have h : (fun n => F n + (-E n)) = weilAdaptiveRightRampKept := funext fun n => by
    rw [← sub_eq_add_neg,balance]
  rw [h] at S
  exact S

def weilAdaptiveExtra (n : ℕ) (i : ℕ × ℕ) (v : ℕ) : Prop :=
  let u := leftBilinearStep i
  widerLowFarModulusCap n < v ∧ u ≤ extendedWideStepCap n ∧ u ≤ v ∧ u*v ≤ weilNearProductCap n ∧
    weilAdaptiveRightRampFactor n v i.1

set_option maxHeartbeats 1200000 in
theorem weil_adaptive_product_mask_iff {n : ℕ} {i : ℕ × ℕ} {j : RightLowWaveIndex}
    (hj : j ∈ longRightLowItems n) :
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    (j ∈ weilNearRightRows n ∧ weilAdaptiveGroupGate n i j ∧ weilNearLeftKept n u) ↔
      (u ≤ expandedWideStepCap n ∧ ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧
        farInnerThinGate n u v ∧ retainedLowTargetMask n u v ∧ stepWithoutLargeSquare n u ∧
        weilAdaptiveExtra n i v ∧ u.gcd v ∣ n) := by
  dsimp only
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  have vr := mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))
  have v0 : 0 < v := vr.1
  have n0 : 0 < n := vr.1.trans vr.2
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n0
  have cutoff : thinHighGcdCap n ≤ cutoffU n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have cof : 1 ≤ cofactorCap n := Nat.le_floor (Real.one_le_rpow nR (by norm_num))
  have gCap : thinHighGcdCap n ≤ maximumStep n := cutoff.trans (by
    change cutoffU n ≤ cutoffU n*cofactorCap n
    simpa only [mul_one] using Nat.mul_le_mul_left (cutoffU n) cof)
  have C1 : expandedHighModulusCap n ≤ widerLowFarModulusCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have C2 : shortLowModulusCap n ≤ widerLowFarModulusCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have rest (h : widerLowFarModulusCap n < v) : remainingExpandedLow n u v := by
    refine ⟨?_,?_,?_⟩
    · exact fun small => (not_le_of_gt (C1.trans_lt h)) small.1
    · exact fun mid => (not_le_of_gt (C2.trans_lt h)) mid.2.2.1
    · exact fun wide => (not_le_of_gt h) wide.2.2.1
  have dl : weilNearProductLower n j (u.gcd v) < u ↔
      ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧ maximumStep n^2 < u*v ∧
      thinHighProductCap n < u*v ∧ highFarStripProductCap n < u*v := by
    simp only [weilNearProductLower, v, max_lt_iff, Nat.div_lt_iff_lt_mul v0]
  have du : u ≤ weilNearProductUpper n j (u.gcd v) ↔
      u ≤ extendedWideStepCap n ∧ u ≤ expandedWideStepCap n ∧ u ≤ v ∧ u*v ≤ weilNearProductCap n := by
    simp only [weilNearProductUpper, v, le_min_iff, Nat.le_div_iff_mul_le v0]
  have gg : u.gcd v ∈ weilNearRowDivisors n v ↔ u.gcd v ∣ n ∧ u.gcd v ≤ thinHighGcdCap n := by
    rw [weilNearRowDivisors,mem_filter,Nat.mem_divisors]
    exact ⟨fun h => ⟨h.1.1,h.2.2⟩,
      fun h => ⟨⟨h.1,n0.ne'⟩,Nat.gcd_dvd_right _ _,h.2⟩⟩
  have rightMask : j ∈ weilNearRightRows n ↔
      widerLowFarModulusCap n < v ∧ v.gcd n ≤ sparseTargetDivisorCap n ∧ v.gcd n ≤ targetDivisorCap n := by
    unfold weilNearRightRows
    simp only [mem_filter,hj,true_and]
    rfl
  change (j ∈ weilNearRightRows n ∧
      ((u.gcd v ∈ weilNearRowDivisors n v) ∧
        weilNearProductLower n j (u.gcd v) < u ∧ u ≤ weilNearProductUpper n j (u.gcd v) ∧
        weilAdaptiveRightRampFactor n v i.1) ∧ weilNearLeftKept n u) ↔ _
  rw [dl,du,gg,rightMask]
  simp only [weilNearLeftKept,farInnerThinGate,boundedOuterLeftKeptGate,farInnerGate,prefixStepGate,
    retainedLowTargetMask,targetDivisorKept,weilAdaptiveExtra]
  constructor
  · rintro ⟨⟨wide,sparse,target⟩,⟨⟨dvd,gcd⟩,⟨geom,mp,tp,fp⟩,⟨ext,cap,uv,p⟩,factor⟩,left,square⟩
    exact ⟨cap,geom,⟨⟨⟨⟨mp,gcd.trans gCap⟩,fp⟩,tp,gcd,target⟩,left⟩,⟨rest wide,sparse⟩,square,
      ⟨wide,ext,uv,p,factor⟩,dvd⟩
  · rintro ⟨cap,geom,⟨⟨⟨⟨mp,_⟩,fp⟩,tp,gcd,target⟩,left⟩,⟨_,sparse⟩,square,
      ⟨wide,ext,uv,p,factor⟩,dvd⟩
    exact ⟨⟨wide,sparse,target⟩,⟨⟨dvd,gcd⟩,⟨geom,mp,tp,fp⟩,⟨ext,cap,uv,p⟩,factor⟩,left,square⟩

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_symmetric_exterior_pair -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

def symmetricCountMain (n u v p : ℕ) : ℝ :=
  let d := u.gcd v
  let U := (u/d : ℕ)
  let V := (v/d : ℕ)
  let T := (n/d : ℕ)
  if d ∣ n ∧ v*p<n then
    ((T : ℝ)-(V : ℝ)*p)/((U : ℝ)*V)-1/(2*(U : ℝ))-1/(2*(V : ℝ))
  else 0

theorem symmetric_count_main_eq_unreduced {n u v p : ℕ} (hu : 0 < u) (hv : 0 < v) :
    symmetricCountMain n u v p =
      if u.gcd v ∣ n ∧ v*p<n then
        (u.gcd v : ℝ)*(((n : ℝ)-(v : ℝ)*p)/((u : ℝ)*v)-1/(2*(u : ℝ))-1/(2*(v : ℝ)))
      else 0 := by
  unfold symmetricCountMain
  dsimp only
  split_ifs with h
  · let d := u.gcd v
    let U := u/d
    let V := v/d
    let T := n/d
    have gd : 0 < d := Nat.gcd_pos_of_pos_left _ hu
    have d0 : (0 : ℝ) < d := by exact_mod_cast gd
    have U0 : 0 < U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) gd
    have V0 : 0 < V := Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right u v)) gd
    have uEq : (U : ℝ)*(d : ℝ)=(u : ℝ) := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left u v)
    have vEq : (V : ℝ)*(d : ℝ)=(v : ℝ) := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right u v)
    have nEq : (T : ℝ)*(d : ℝ)=(n : ℝ) := by exact_mod_cast Nat.div_mul_cancel h.1
    have u0 : (0 : ℝ) < U := by exact_mod_cast U0
    have v0 : (0 : ℝ) < V := by exact_mod_cast V0
    change ((T : ℝ)-(V : ℝ)*p)/((U : ℝ)*V)-1/(2*(U : ℝ))-1/(2*(V : ℝ)) =
      (d : ℝ)*(((n : ℝ)-(v : ℝ)*p)/((u : ℝ)*v)-1/(2*(u : ℝ))-1/(2*(v : ℝ)))
    rw [← uEq,← vEq,← nEq]
    field_simp [d0.ne',u0.ne',v0.ne'] <;> ring
  · rfl

theorem full_progression_pair_count_eq_centered_ramps {n u v p : ℕ}
    (hu : 0 < u) (hv : 0 < v) :
    ((progressionPairSolutions n u v 0 (n/u) p (n/v)).card : ℝ) =
      symmetricResidueError n u v p+symmetricCountMain n u v p := by
  let d := u.gcd v
  let U := u/d
  let V := v/d
  let T := n/d
  by_cases h : d ∣ n ∧ v*p<n
  · unfold symmetricResidueError symmetricCountMain
    dsimp only
    rw [if_pos h,if_pos h]
    have count := full_progression_pair_count_eq_symmetric hu hv h.1 h.2
    dsimp only at count
    rw [count]
    have d0 : 0 < d := Nat.gcd_pos_of_pos_left _ hu
    have u0 : 0 < U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) d0
    have v0 : 0 < V := Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right u v)) d0
    have un : (U : ℝ) ≠ 0 := by exact_mod_cast u0.ne'
    have vn : (V : ℝ) ≠ 0 := by exact_mod_cast v0.ne'
    change 1+((T : ℝ)-(V : ℝ)*p)/((U : ℝ)*(V : ℝ))-
      (positiveInverseResidue T U V : ℝ)/(V : ℝ)-
      (((((T : ℤ)*Nat.gcdA V U-(p : ℤ)-1)%(U : ℤ)+1) : ℤ) : ℝ)/(U : ℝ) =
      (centeredInverseRamp V ((T : ℤ)*Nat.gcdA U V-1)+
        centeredInverseRamp U ((T : ℤ)*Nat.gcdA V U-(p : ℤ)-1))+
      (((T : ℝ)-(V : ℝ)*p)/((U : ℝ)*V)-1/(2*(U : ℝ))-1/(2*(V : ℝ)))
    simp only [positiveInverseResidue,centeredInverseRamp,Int.cast_add,Int.cast_one]
    field_simp [un,vn] <;> ring
  · have empty : progressionPairSolutions n u v 0 (n/u) p (n/v) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨bounds,total⟩ := mem_filter.mp ha
      have second := (mem_Ioc.mp (mem_product.mp bounds).2).1
      have h1 : d ∣ n := by
        rw [← total]
        exact Nat.dvd_add ((Nat.gcd_dvd_left u v).trans (dvd_mul_right _ _))
          ((Nat.gcd_dvd_right u v).trans (dvd_mul_right _ _))
      have h2 : v*p<n := by
        rw [← total]
        exact (Nat.mul_lt_mul_of_pos_left second hv).trans_le (Nat.le_add_left _ _)
      exact h ⟨h1,h2⟩
    unfold symmetricResidueError symmetricCountMain
    dsimp only
    have h' : ¬(u.gcd v ∣ n ∧ v*p<n) := h
    simp only [empty,card_empty,Nat.cast_zero,if_neg h',add_zero]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_near_product_exact -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def symmetricLowPairKept (n u v : ℕ) : Prop :=
  u ≤ expandedWideStepCap n ∧ ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧
    farInnerThinGate n u v ∧ retainedLowTargetMask n u v ∧ stepWithoutLargeSquare n u

def weilNearLowInterior (n : ℕ) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ longRightLowItems n,
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    if symmetricLowPairKept n u v then
      leftPrimeWeight n i*rightLowWaveWeight j*
        (if weilNearExtra n i v ∧ u.gcd v ∣ n then (rightInverseRamp n v u : ℂ)
          else (symmetricResidueError n u v 0 : ℂ))
    else 0

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_inverse_ramp_periods -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

private theorem int_interval_mod_units_split (m : ℕ) {a b c : ℤ} (ab : a ≤ b) (bc : b ≤ c) :
    intIntervalModUnits m a c = intIntervalModUnits m a b ∪ intIntervalModUnits m b c := by
  ext j
  simp only [intIntervalModUnits,mem_filter,mem_Ioc,mem_union]
  by_cases h : j ≤ b
  · have aux : j ≤ c := h.trans bc
    simp [h,aux,not_lt_of_ge h]
  · have aux : a < j := ab.trans_lt (lt_of_not_ge h)
    simp [h,aux,lt_of_not_ge h]

private theorem int_interval_mod_units_disjoint (m : ℕ) (a b c : ℤ) :
    Disjoint (intIntervalModUnits m a b) (intIntervalModUnits m b c) := by
  apply disjoint_left.mpr
  intro j h₁ h₂
  have p₁ : j ∈ Ioc a b ∧ IsUnit (j : ZMod m) := by
    simpa only [intIntervalModUnits,mem_filter] using h₁
  have p₂ : j ∈ Ioc b c ∧ IsUnit (j : ZMod m) := by
    simpa only [intIntervalModUnits,mem_filter] using h₂
  exact (not_le_of_gt (mem_Ioc.mp p₂.1).1) (mem_Ioc.mp p₁.1).2

theorem gated_bilinear_sum_split_unit_intervals {ι : Type*} (m : ℕ) (I : Finset ι)
    (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ) (z : ι → ℤ → ℂ) {a b c : ℤ}
    (ab : a ≤ b) (bc : b ≤ c) :
    gatedBilinearSum I (intIntervalModUnits m a c) α β lo hi z =
      gatedBilinearSum I (intIntervalModUnits m a b) α β lo hi z +
        gatedBilinearSum I (intIntervalModUnits m b c) α β lo hi z := by
  unfold gatedBilinearSum
  rw [int_interval_mod_units_split m ab bc,sum_union (int_interval_mod_units_disjoint m a b c)]

private def translateInteger (b : ℤ) : ℤ ↪ ℤ :=
  ⟨fun j => j+b,fun x y h => add_right_cancel h⟩

private theorem int_interval_mod_units_map_translate (m : ℕ) (b S : ℤ) (zero : (b : ZMod m) = 0) :
    (intIntervalModUnits m 0 S).map (translateInteger b) = intIntervalModUnits m b (b+S) := by
  ext x
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := mem_map.mp h
    have H : j ∈ Ioc 0 S ∧ IsUnit (j : ZMod m) := by
      simpa only [intIntervalModUnits,mem_filter] using hj
    change j+b=x at he
    have xcast : (x : ZMod m)=(j : ZMod m) := by rw [← he,Int.cast_add,zero,add_zero]
    have data : x ∈ Ioc b (b+S) ∧ IsUnit (x : ZMod m) :=
      ⟨mem_Ioc.mpr ⟨by have := (mem_Ioc.mp H.1).1; omega,
        by have := (mem_Ioc.mp H.1).2; omega⟩,xcast.symm ▸ H.2⟩
    simpa only [intIntervalModUnits,mem_filter] using data
  · intro h
    have H : x ∈ Ioc b (b+S) ∧ IsUnit (x : ZMod m) := by
      simpa only [intIntervalModUnits,mem_filter] using h
    let j := x-b
    have valid : j ∈ Ioc 0 S := by
      obtain ⟨L,R⟩ := mem_Ioc.mp H.1
      exact mem_Ioc.mpr ⟨by unfold j; omega,by unfold j; omega⟩
    have jc : (j : ZMod m)=(x : ZMod m) := by unfold j; rw [Int.cast_sub,zero,sub_zero]
    have data : j ∈ Ioc 0 S ∧ IsUnit (j : ZMod m) := ⟨valid,jc.symm ▸ H.2⟩
    refine mem_map.mpr ⟨j,?_,?_⟩
    · simpa only [intIntervalModUnits,mem_filter] using data
    · change (x-b)+b=x
      omega

private theorem gated_bilinear_sum_translate {ι : Type*} (m : ℕ) (b S : ℤ) (zero : (b : ZMod m)=0)
    (I : Finset ι) (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ) (z : ι → ℤ → ℂ) :
    gatedBilinearSum I (intIntervalModUnits m b (b+S)) α β lo hi z =
    gatedBilinearSum I (intIntervalModUnits m 0 S) α (fun j => β (j+b))
      (fun i => lo i-b) (fun i => hi i-b) (fun i j => z i (j+b)) := by
  unfold gatedBilinearSum
  rw [← int_interval_mod_units_map_translate m b S zero,sum_map]
  refine sum_congr rfl fun j _ => ?_
  change β (j+b)*_ = β (j+b)*_
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have gate : (lo i<j+b ∧ j+b≤hi i) ↔ (lo i-b<j ∧ j≤hi i-b) := by omega
  change (if lo i<j+b ∧ j+b≤hi i then α i*z i (j+b) else 0) = _
  simp only [gate]

theorem norm_gated_inverse_ramp_le_weil_periods {m A S : ℕ} [NeZero m] (c : ZMod m)
    (I : Finset ℕ) (base : I ⊆ Icc 1 A) (cop : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {T L : ℝ} (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (leftWeights : ∀ i ∈ I, ‖α i‖ ≤ T)
    (rightWeights : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T*L)
    (tau : (m.divisors.card : ℝ) ≤ T) (log : 1+Real.log m ≤ L)
    (s : ℕ → ZMod m) (t : ℤ → ZMod m) (z : ℕ → ℤ → ℤ)
    (phase : ∀ i j, (z i j : ZMod m) = c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹-s i-t j) :
    let Q := min S m
    ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun i j => (centeredInverseRamp m (z i j-1) : ℂ))‖ ≤
      ((S/m : ℕ) + 1 : ℝ)*(3*T^4*L^3*((Q : ℝ)*Real.sqrt A+
        (A : ℝ)*Real.sqrt Q*Real.sqrt (Real.sqrt m*Real.sqrt (m.gcd c.val)))) := by
  dsimp only
  let Q := min S m
  let f (i : ℕ) (j : ℤ) := (centeredInverseRamp m (z i j-1) : ℂ)
  let B (q : ℕ) := 3*T^4*L^3*((q : ℝ)*Real.sqrt A+
    (A : ℝ)*Real.sqrt q*Real.sqrt (Real.sqrt m*Real.sqrt (m.gcd c.val)))
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans L1
  have B0 (q : ℕ) : 0 ≤ B q := by unfold B; positivity
  have m0 : 0 < m := NeZero.pos m
  have oneBlock (k r : ℕ) (leg : r ≤ Q) (top : k*m+r ≤ S) :
      ‖gatedBilinearSum I (intIntervalModUnits m (k*m : ℕ) ((k*m+r : ℕ) : ℤ)) α β lo hi f‖ ≤ B Q := by
    have offset : (((k*m : ℕ) : ℤ) : ZMod m)=0 := by
      simp only [Int.cast_mul,Int.cast_natCast,Nat.cast_mul,ZMod.natCast_self,mul_zero]
    rw [Nat.cast_add,gated_bilinear_sum_translate m ((k*m : ℕ) : ℤ) (r : ℤ) offset]
    have rwgt (j : ℤ) (hj : j ∈ intIntervalModUnits m 0 r) : ‖β (j+(k*m : ℕ))‖ ≤ T*L := by
      have data : j ∈ Ioc 0 (r : ℤ) ∧ IsUnit (j : ZMod m) := by
        simpa only [intIntervalModUnits,mem_filter] using hj
      have upper : (k*m : ℕ)+(r : ℤ) ≤ (S : ℤ) := by exact_mod_cast top
      have low : (0 : ℤ) ≤ (k*m : ℕ) := by positivity
      have oc := mem_Ioc.mp data.1
      have cast : ((j+(k*m : ℕ) : ℤ) : ZMod m) = (j : ZMod m) := by
        rw [Int.cast_add,offset,add_zero]
      have flags : (j+(k*m : ℕ) : ℤ) ∈ Ioc 0 (S : ℤ) ∧ IsUnit ((j+(k*m : ℕ) : ℤ) : ZMod m) :=
        ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,cast.symm ▸ data.2⟩
      exact rightWeights _ (by simpa only [intIntervalModUnits,mem_filter] using flags)
    have ph (i : ℕ) (j : ℤ) : (z i (j+(k*m : ℕ)) : ZMod m) =
        c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹-s i-t (j+(k*m : ℕ)) := by
      rw [phase,Int.cast_add,offset,add_zero]
    have h := norm_gated_inverse_ramp_le_weil_row c I base cop α (fun j => β (j+(k*m : ℕ)))
      (fun i => lo i-((k*m : ℕ) : ℤ)) (fun i => hi i-((k*m : ℕ) : ℤ))
      (leg.trans (min_le_right _ _)) T1 L1 leftWeights rwgt tau log s
      (fun j => t (j+(k*m : ℕ))) (fun i j => z i (j+(k*m : ℕ))) ph
    refine h.trans ?_
    unfold B
    have le : (r : ℝ) ≤ Q := by exact_mod_cast leg
    have sq := Real.sqrt_le_sqrt le
    gcongr
  by_cases small : S ≤ m
  · have w := norm_gated_inverse_ramp_le_weil_row c I base cop α β lo hi small T1 L1
      leftWeights rightWeights tau log s t z phase
    change ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi f‖ ≤
      ((S/m : ℕ)+1 : ℝ)*B Q
    have Qeq : Q=S := min_eq_left small
    rw [Qeq]
    exact w.trans (le_mul_of_one_le_left (B0 S) (le_add_of_nonneg_left (by positivity)))
  · have Qeq : Q=m := min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge small))
    have block (k : ℕ) (ktop : k*m ≤ S) :
        ‖gatedBilinearSum I (intIntervalModUnits m 0 ((k*m : ℕ) : ℤ)) α β lo hi f‖ ≤ (k : ℝ)*B Q := by
      induction k with
      | zero =>
        have empty : intIntervalModUnits m 0 0 = ∅ := by simp [intIntervalModUnits]
        simp [zero_mul,empty,gatedBilinearSum]
      | succ k ih =>
        rw [Nat.succ_mul,Nat.cast_add,gated_bilinear_sum_split_unit_intervals m I α β lo hi f
          (by positivity : (0 : ℤ) ≤ (k*m : ℕ)) (le_add_of_nonneg_right (by positivity : (0 : ℤ) ≤ m))]
        have one := oneBlock k m (by rw [Qeq]) (by simpa only [Nat.succ_mul] using ktop)
        rw [Nat.cast_add] at one
        have before : k*m ≤ S := (Nat.le_add_right _ _).trans (by simpa only [Nat.succ_mul] using ktop)
        calc
          _ ≤ ‖gatedBilinearSum I (intIntervalModUnits m 0 ((k*m : ℕ) : ℤ)) α β lo hi f‖ +
              ‖gatedBilinearSum I (intIntervalModUnits m (k*m : ℕ)
                (((k*m : ℕ) : ℤ)+(m : ℤ))) α β lo hi f‖ := norm_add_le _ _
          _ ≤ (k : ℝ)*B Q+B Q := add_le_add (ih before) one
          _ = _ := by push_cast; ring
    let k := S/m
    let r := S%m
    have exactS : k*m+r=S := by unfold k r; rw [Nat.mul_comm]; exact Nat.div_add_mod S m
    have rQ : r ≤ Q := by rw [Qeq]; exact (Nat.mod_lt _ m0).le
    have leftEnd : k*m ≤ S := (Nat.le_add_right _ _).trans exactS.le
    have lbound := block k leftEnd
    have rbound := oneBlock k r rQ exactS.le
    rw [exactS] at rbound
    have h₁ : (0 : ℤ) ≤ ((k*m : ℕ) : ℤ) := by positivity
    have h₂ : ((k*m : ℕ) : ℤ) ≤ (S : ℤ) := by exact_mod_cast leftEnd
    change ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi f‖ ≤
      ((k : ℝ)+1)*B Q
    rw [gated_bilinear_sum_split_unit_intervals m I α β lo hi f h₁ h₂]
    exact (norm_add_le _ _).trans ((add_le_add lbound rbound).trans_eq (by ring))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_reverse_near_window -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4MoebiusGauss DyadicMixedB4TailScale
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def reverseWeilShortCut (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/24 : ℝ)⌋₊

def reverseWeilFactors (n u g : ℕ) : Finset ℕ :=
  (Icc 1 (cutoffU n/g)).filter fun a =>
    reverseWeilShortCut n < g*a ∧ (g*a).gcd n ≤ sparseTargetDivisorCap n ∧
      (g*a).gcd n ≤ targetDivisorCap n ∧ a.Coprime (u/g)

def reverseWeilPrimeWeight (n : ℕ) (p : ℤ) : ℂ :=
  if p.toNat.Prime ∧ ¬p.toNat ∣ n then (vonMangoldt p.toNat : ℂ) else 0

def reverseWeilLower (n g lo a : ℕ) : ℤ := (max (cutoffU n) (lo/(g*a)) : ℕ)

def reverseWeilUpper (n g hi a : ℕ) : ℤ := (min (min n (rightLargeCofactorCut n)) (hi/(g*a)) : ℕ)

def reverseWeilWindow (n u g lo hi : ℕ) : ℂ :=
  let m := u/g
  let I := reverseWeilFactors n u g
  let J := intIntervalModUnits m 0 (hi/(reverseWeilShortCut n+1) : ℕ)
  gatedBilinearSum I J (fun a => -(μ (g*a) : ℂ)) (reverseWeilPrimeWeight n)
    (reverseWeilLower n g lo) (reverseWeilUpper n g hi)
    (fun a p => (centeredInverseRamp m (rightInverseRampPhase (n/g) m a p-1) : ℂ))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_reverse_near_bridge -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def reverseWeilSelected (n u g lo hi : ℕ) : Finset RightLowWaveIndex :=
  (longRightLowItems n).filter fun j =>
    reverseWeilShortCut n < j.2 ∧ j.2.gcd n ≤ sparseTargetDivisorCap n ∧ j.2.gcd n ≤ targetDivisorCap n ∧
      u.gcd (rightLowWaveStep j)=g ∧ lo < rightLowWaveStep j ∧ rightLowWaveStep j ≤ hi

set_option maxHeartbeats 1800000 in
theorem reverse_weil_window_eq_selected {n u g lo hi : ℕ}
    (u0 : 0 < u) (g0 : 0 < g) (gu : g ∣ u) (gn : g ∣ n)
    (lLower : maximumStep n ≤ lo) (hiN : hi ≤ n) :
    reverseWeilWindow n u g lo hi =
      ∑ j ∈ reverseWeilSelected n u g lo hi,
        rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) u : ℂ) := by
  let m := u/g
  let A := cutoffU n/g
  let S := hi/(reverseWeilShortCut n+1)
  let I := reverseWeilFactors n u g
  let J := intIntervalModUnits m 0 S
  let gate (a : ℕ) (p : ℤ) := reverseWeilLower n g lo a < p ∧ p ≤ reverseWeilUpper n g hi a
  let prime (p : ℤ) := p.toNat.Prime ∧ ¬p.toNat ∣ n
  let P := (J ×ˢ I).filter (fun x => gate x.2 x.1 ∧ prime x.1)
  let liftPoint (x : ℤ × ℕ) : RightLowWaveIndex := ⟨x.1.toNat,g*x.2⟩
  let F (a : ℕ) (p : ℤ) := (centeredInverseRamp m (rightInverseRampPhase (n/g) m a p-1) : ℂ)
  let weight (x : ℤ × ℕ) := rightLowWaveWeight (liftPoint x)*F x.2 x.1
  let value (j : RightLowWaveIndex) := rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) u : ℂ)
  have mg : g*m=u := Nat.mul_div_cancel' gu
  have m0 : 0 < m := Nat.div_pos (Nat.le_of_dvd u0 gu) g0
  have infoI (a : ℕ) (ha : a ∈ I) :
      (1 ≤ a ∧ a ≤ A) ∧ reverseWeilShortCut n < g*a ∧ (g*a).gcd n ≤ sparseTargetDivisorCap n ∧
      (g*a).gcd n ≤ targetDivisorCap n ∧ a.Coprime m :=
    ⟨mem_Icc.mp (mem_filter.mp ha).1,(mem_filter.mp ha).2⟩
  have infoJ (p : ℤ) (hp : p ∈ J) : p ∈ Ioc 0 (S : ℤ) ∧ IsUnit (p : ZMod m) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hp
  have castJ (p : ℤ) (hp : 0 ≤ p) : (p.toNat : ZMod m) = (p : ZMod m) := by
    simpa only [Int.cast_natCast] using congrArg (fun j : ℤ => (j : ZMod m)) (Int.toNat_of_nonneg hp)
  have copJ (p : ℤ) (hp : p ∈ J) : p.toNat.Coprime m :=
    (ZMod.isUnit_iff_coprime _ _).mp ((castJ p (mem_Ioc.mp (infoJ p hp).1).1.le).symm ▸ (infoJ p hp).2)
  have gate_iff (a : ℕ) (a0 : 0 < a) (p : ℤ) (p0 : 0 ≤ p) :
      gate a p ↔ (cutoffU n < p.toNat ∧ p.toNat ≤ min n (rightLargeCofactorCut n)) ∧
        lo < (g*a)*p.toNat ∧ (g*a)*p.toNat ≤ hi := by
    unfold gate reverseWeilLower reverseWeilUpper
    rw [← Int.toNat_of_nonneg p0]
    simp only [Int.ofNat_lt,Int.ofNat_le,Int.toNat_natCast,max_lt_iff,le_min_iff,
      Nat.div_lt_iff_lt_mul (Nat.mul_pos g0 a0),Nat.le_div_iff_mul_le (Nat.mul_pos g0 a0),
      Nat.mul_comm p.toNat (g*a)]
    tauto
  have lift_mem (x : ℤ × ℕ) (hx : x ∈ P) : liftPoint x ∈ reverseWeilSelected n u g lo hi := by
    obtain ⟨hp,ha⟩ := mem_product.mp (mem_filter.mp hx).1
    obtain ⟨hgate,hprime⟩ := (mem_filter.mp hx).2
    obtain ⟨⟨aPos,aTop⟩,aLo,gcdSmall,gcdNormal,ac⟩ := infoI _ ha
    have aCap : g*x.2 ≤ cutoffU n := by
      rw [Nat.mul_comm g]
      exact (Nat.le_div_iff_mul_le g0).mp aTop
    have p0 := (mem_Ioc.mp (infoJ _ hp).1).1
    have pPos : 0 < x.1.toNat := by omega
    obtain ⟨⟨plo,phi⟩,vlo,vhi⟩ := (gate_iff _ aPos _ p0.le).mp hgate
    have uCap : g*x.2 ≤ n/x.1.toNat := (Nat.le_div_iff_mul_le pPos).mpr (vhi.trans hiN)
    have base : liftPoint x ∈ rightLowWaveItems n := mem_sigma.mpr
      ⟨mem_Ioc.mpr ⟨plo,phi⟩,mem_Icc.mpr ⟨Nat.mul_pos g0 aPos,le_min aCap uCap⟩⟩
    have long : liftPoint x ∈ longRightLowItems n := mem_filter.mpr
      ⟨mem_filter.mpr ⟨base,hprime⟩,not_le_of_gt (lLower.trans_lt vlo)⟩
    have cp : (x.2*x.1.toNat).Coprime m := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa only [Nat.cast_mul] using
        ((ZMod.isUnit_iff_coprime _ _).mpr ac).mul ((ZMod.isUnit_iff_coprime _ _).mpr (copJ _ hp))
    have gcd : u.gcd (rightLowWaveStep (liftPoint x))=g := by
      change u.gcd (g*x.2*x.1.toNat) = g
      rw [← mg,mul_assoc,Nat.gcd_mul_left,Nat.gcd_comm m,cp.gcd_eq_one,mul_one]
    exact mem_filter.mpr ⟨long,aLo,gcdSmall,gcdNormal,gcd,vlo,vhi⟩
  have lift_surj (j : RightLowWaveIndex) (hj : j ∈ reverseWeilSelected n u g lo hi) :
      ∃ x ∈ P, liftPoint x=j := by
    obtain ⟨long,aLo,gcdSmall,gcdNormal,gcd,vlo,vhi⟩ := mem_filter.mp hj
    obtain ⟨pPrime,pN⟩ := (mem_filter.mp (mem_filter.mp long).1).2
    obtain ⟨pRange,qRange⟩ := mem_sigma.mp (long_right_low_subset n long)
    have gd : u.gcd (j.1*j.2) ∣ n := by
      rw [Nat.mul_comm j.1]
      exact gcd.symm ▸ gn
    have split := gcd_right_step_dvd_cofactor_when_prime_nondvd pPrime pN gd
    dsimp only at split
    rw [Nat.mul_comm j.1,show u.gcd (j.2*j.1)=g from gcd] at split
    let a := j.2/g
    have eq : g*a=j.2 := Nat.mul_div_cancel' split.1
    have a0 : 0 < a := Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp qRange).1 split.1) g0
    have aTop : a ≤ A := Nat.div_le_div_right ((mem_Icc.mp qRange).2.trans (min_le_left _ _))
    have poly : rightLowWaveStep j=g*(a*j.1) := by
      change j.2*j.1=g*(a*j.1)
      rw [← eq,mul_assoc]
    have gc : (rightLowWaveStep j).gcd u=g := (Nat.gcd_comm _ _).trans gcd
    have cp : (a*j.1).Coprime m := by
      have core : (rightLowWaveStep j/(rightLowWaveStep j).gcd u).Coprime (u/(rightLowWaveStep j).gcd u) :=
        Nat.coprime_div_gcd_div_gcd (gc.symm ▸ g0)
      rw [gc,poly,Nat.mul_div_cancel_left _ g0] at core
      exact core
    have aI : a ∈ I := mem_filter.mpr ⟨mem_Icc.mpr ⟨a0,aTop⟩,
      by rw [eq]; exact aLo,by rw [eq]; exact gcdSmall,by rw [eq]; exact gcdNormal,
      cp.coprime_dvd_left (dvd_mul_right _ _)⟩
    have p0 : 0 < j.1 := pPrime.pos
    have pS : j.1 ≤ S := (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by
      rw [Nat.mul_comm]
      exact (Nat.mul_le_mul_right j.1 aLo).trans vhi)
    have Pdata : (j.1 : ℤ) ∈ Ioc 0 (S : ℤ) ∧ IsUnit ((j.1 : ℤ) : ZMod m) := by
      exact ⟨mem_Ioc.mpr ⟨by exact_mod_cast p0,by exact_mod_cast pS⟩,by
        rw [Int.cast_natCast]
        exact (ZMod.isUnit_iff_coprime _ _).mpr (cp.coprime_dvd_left (dvd_mul_left _ _))⟩
    have pJ : (j.1 : ℤ) ∈ J := by simpa only [J,intIntervalModUnits,mem_filter] using Pdata
    have gateNat : (cutoffU n < j.1 ∧ j.1 ≤ min n (rightLargeCofactorCut n)) ∧
         lo < (g*a)*j.1 ∧ (g*a)*j.1 ≤ hi := by
      rw [eq]
      exact ⟨mem_Ioc.mp pRange,vlo,vhi⟩
    have pGate : gate a (j.1 : ℤ) :=
      (gate_iff a a0 _ (by positivity)).mpr (by simpa only [Int.toNat_natCast] using gateNat)
    have pri : prime (j.1 : ℤ) := by unfold prime; exact_mod_cast (show j.1.Prime ∧ ¬j.1 ∣ n from ⟨pPrime,pN⟩)
    have point : liftPoint ((j.1 : ℤ),a)=j := by
      rcases j with ⟨p,q⟩
      change (⟨Int.toNat (p : ℤ),g*a⟩ : RightLowWaveIndex) = ⟨p,q⟩
      rw [Int.toNat_natCast,eq]
    exact ⟨((j.1 : ℤ),a),mem_filter.mpr ⟨mem_product.mpr ⟨pJ,aI⟩,pGate,pri⟩,point⟩
  have eval (x : ℤ × ℕ) (hx : x ∈ P) : weight x=value (liftPoint x) := by
    have selected := lift_mem x hx
    obtain ⟨hp,ha⟩ := mem_product.mp (mem_filter.mp hx).1
    have cast := castJ _ (mem_Ioc.mp (infoJ _ hp).1).1.le
    have ac := (infoI _ ha).2.2.2.2
    have cp : (x.2*x.1.toNat).Coprime m := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa only [Nat.cast_mul] using
        ((ZMod.isUnit_iff_coprime _ _).mpr ac).mul ((ZMod.isUnit_iff_coprime _ _).mpr (copJ _ hp))
    let _ : NeZero m := ⟨m0.ne'⟩
    have inv : ((x.2 : ZMod m)*(x.1 : ZMod m))⁻¹ = (x.2 : ZMod m)⁻¹*(x.1 : ZMod m)⁻¹ := by
      apply ZMod.inv_eq_of_mul_eq_one
      calc
        _ = ((x.2 : ZMod m)*(x.2 : ZMod m)⁻¹)*((x.1 : ZMod m)*(x.1 : ZMod m)⁻¹) := by ring
        _ = _ := by rw [ZMod.coe_mul_inv_eq_one x.2 ac,ZMod.mul_inv_of_unit _ (infoJ _ hp).2,one_mul]
    have phase : (rightInverseRampPhase (n/g) m x.2 x.1 : ZMod m) =
        ((((n/g : ℕ) : ℤ)*Nat.gcdA (x.2*x.1.toNat) m : ℤ) : ZMod m) := by
      rw [right_inverse_ramp_phase_cast,Int.cast_mul,Int.cast_natCast,
        cast_gcdA_eq_inv_of_coprime cp,Nat.cast_mul,cast,inv]
      ring
    have gcd : (rightLowWaveStep (liftPoint x)).gcd u = g :=
      (Nat.gcd_comm _ _).trans (mem_filter.mp selected).2.2.2.2.1
    have poly : rightLowWaveStep (liftPoint x)=g*(x.2*x.1.toNat) := by
      change g*x.2*x.1.toNat=g*(x.2*x.1.toNat)
      rw [mul_assoc]
    unfold weight value F rightInverseRamp
    rw [gcd]
    dsimp only
    rw [poly,Nat.mul_div_cancel_left _ g0,centered_inverse_ramp_eq_of_cast_eq phase]
  have expand : reverseWeilWindow n u g lo hi = ∑ x ∈ P, weight x := by
    change gatedBilinearSum I J (fun a => -(μ (g*a) : ℂ)) (reverseWeilPrimeWeight n)
      (reverseWeilLower n g lo) (reverseWeilUpper n g hi) F = _
    rw [gated_bilinear_sum_eq_pair_sum]
    unfold P
    rw [sum_filter,sum_product]
    refine sum_congr rfl fun p _ => sum_congr rfl fun a _ => ?_
    change (if gate a p then _ else 0) = (if gate a p ∧ prime p then _ else 0)
    by_cases h : gate a p
    · by_cases hp : prime p
      · simp only [h,hp,true_and,ite_true,weight,liftPoint,rightLowWaveWeight]
        unfold reverseWeilPrimeWeight
        exact congrArg (fun z : ℂ => -(μ (g*a) : ℂ)*z*F a p) (if_pos (show _ from hp))
      · simp [h,hp,reverseWeilPrimeWeight,prime] at *
    · simp only [h,false_and,ite_false]
  rw [expand]
  refine sum_bij (fun x _ => liftPoint x) lift_mem ?_ ?_ eval
  swap
  · intro j hj
    obtain ⟨x,hx,e⟩ := lift_surj j hj
    exact ⟨x,hx,e⟩
  intro x hx y hy e
  have aEq : g*x.2=g*y.2 := by
    have v := congrArg (fun j : RightLowWaveIndex => j.2) e
    exact v
  have pEq : x.1.toNat=y.1.toNat := congrArg Sigma.fst e
  have pos (z : ℤ × ℕ) (hz : z ∈ P) : 0 ≤ z.1 :=
    (mem_Ioc.mp (infoJ _ (mem_product.mp (mem_filter.mp hz).1).1).1).1.le
  exact Prod.ext (by rw [← Int.toNat_of_nonneg (pos x hx),← Int.toNat_of_nonneg (pos y hy),pEq])
    (Nat.eq_of_mul_eq_mul_left g0 aEq)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_reverse_near_saving -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def reverseWeilRow (n u lo hi : ℕ) : ℂ :=
  ∑ g ∈ weilNearRowDivisors n u, reverseWeilWindow n u g lo hi

def reverseWeilRowItems (n u lo hi : ℕ) : Finset RightLowWaveIndex :=
  (longRightLowItems n).filter fun j =>
    reverseWeilShortCut n < j.2 ∧ j.2.gcd n ≤ sparseTargetDivisorCap n ∧ j.2.gcd n ≤ targetDivisorCap n ∧
      u.gcd (rightLowWaveStep j) ∈ weilNearRowDivisors n u ∧ lo < rightLowWaveStep j ∧ rightLowWaveStep j ≤ hi

theorem reverse_weil_row_eq_selected {n u lo hi : ℕ} (u0 : 0 < u) (uN : u ≤ n)
    (loTop : maximumStep n ≤ lo) (hiN : hi ≤ n) :
    reverseWeilRow n u lo hi =
      ∑ j ∈ reverseWeilRowItems n u lo hi,
        rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) u : ℂ) := by
  let G := weilNearRowDivisors n u
  let J := reverseWeilRowItems n u lo hi
  let d (j : RightLowWaveIndex) := u.gcd (rightLowWaveStep j)
  let w (j : RightLowWaveIndex) := rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) u : ℂ)
  have maps : ∀ j ∈ J, d j ∈ G := fun _ hj => (mem_filter.mp hj).2.2.2.2.1
  change (∑ g ∈ G, reverseWeilWindow n u g lo hi) = ∑ j ∈ J, w j
  rw [← sum_fiberwise_of_maps_to maps w]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨hgN,gu,_⟩ := mem_filter.mp hg
  have gn := (Nat.mem_divisors.mp hgN).1
  have g0 := Nat.pos_of_dvd_of_pos gn (u0.trans_le uN)
  rw [reverse_weil_window_eq_selected u0 g0 gu gn loTop hiN]
  congr 1
  ext j
  simp only [reverseWeilSelected,reverseWeilRowItems,J,d,mem_filter]
  constructor
  · rintro ⟨base,short,gcdS,gcdT,heq,l,r⟩
    exact ⟨⟨base,short,gcdS,gcdT,heq.symm ▸ hg,l,r⟩,heq⟩
  · rintro ⟨⟨base,short,gcdS,gcdT,_,l,r⟩,heq⟩
    exact ⟨base,short,gcdS,gcdT,heq,l,r⟩

def reverseWeilSlice (I : ℕ → Finset (ℕ × ℕ)) (lo hi : ℕ → ℕ → ℕ) (n : ℕ) : ℂ :=
  ∑ i ∈ I n, leftPrimeWeight n i *
    reverseWeilRow n (leftBilinearStep i) (lo n (leftBilinearStep i)) (hi n (leftBilinearStep i))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_reverse_near_remainder -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def reverseWeilLeftRows (n : ℕ) : Finset (ℕ × ℕ) :=
  (bilateralLeftWaveItems n).filter fun i =>
    let u := leftBilinearStep i
    ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧ u ≤ ⌊(n : ℝ)^(1/2 : ℝ)⌋₊ ∧
      u ≤ expandedWideStepCap n ∧ u ≤ extendedWideStepCap n ∧
      weilNearLeftKept n u

def reverseWeilStepLower (n u : ℕ) : ℕ :=
  max (maximumStep n) (max (widerLowFarModulusCap n) (max (u-1)
    (max (maximumStep n^2/u) (max (thinHighProductCap n/u) (highFarStripProductCap n/u)))))

def reverseWeilStepUpper (n u : ℕ) : ℕ :=
  min n (weilNearProductCap n/u)

def reverseWeilOriginalCut (n : ℕ) : ℂ :=
  reverseWeilSlice reverseWeilLeftRows reverseWeilStepLower reverseWeilStepUpper n

theorem reverse_weil_original_cut_eq_selected (n : ℕ) :
    reverseWeilOriginalCut n =
      ∑ i ∈ reverseWeilLeftRows n, leftPrimeWeight n i *
        ∑ j ∈ reverseWeilRowItems n (leftBilinearStep i) (reverseWeilStepLower n (leftBilinearStep i))
          (reverseWeilStepUpper n (leftBilinearStep i)),
          rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) (leftBilinearStep i) : ℂ) := by
  unfold reverseWeilOriginalCut reverseWeilSlice
  refine sum_congr rfl fun i hi => ?_
  have bounds := mem_Icc.mp (bilateral_left_step_range (mem_filter.mp hi).1)
  rw [reverse_weil_row_eq_selected (lo := reverseWeilStepLower n (leftBilinearStep i))
    (hi := reverseWeilStepUpper n (leftBilinearStep i)) bounds.1 bounds.2 (le_max_left _ _) (min_le_left _ _)]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_reverse_near_exact -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def reverseWeilExtra (n u v q : ℕ) : Prop :=
  u ≤ ⌊(n : ℝ)^(1/2 : ℝ)⌋₊ ∧ u ≤ extendedWideStepCap n ∧
    widerLowFarModulusCap n < v ∧ u ≤ v ∧ u*v ≤ weilNearProductCap n ∧
    reverseWeilShortCut n < q

set_option maxHeartbeats 1400000 in
theorem reverse_weil_near_product_mask_iff {n : ℕ} {i : ℕ × ℕ} {j : RightLowWaveIndex}
    (hi : i ∈ bilateralLeftWaveItems n) (hj : j ∈ longRightLowItems n) :
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    (i ∈ reverseWeilLeftRows n ∧ j ∈ reverseWeilRowItems n u (reverseWeilStepLower n u) (reverseWeilStepUpper n u)) ↔
      (u ≤ expandedWideStepCap n ∧ ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧
        farInnerThinGate n u v ∧ retainedLowTargetMask n u v ∧ stepWithoutLargeSquare n u ∧
        reverseWeilExtra n u v j.2 ∧ u.gcd v ∣ n) := by
  dsimp only
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  have ur := mem_Icc.mp (bilateral_left_step_range hi)
  have vr := mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))
  have u0 : 0 < u := ur.1
  have n0 : 0 < n := ur.1.trans ur.2
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n0
  have cutoff : thinHighGcdCap n ≤ cutoffU n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have cof : 1 ≤ cofactorCap n := Nat.le_floor (Real.one_le_rpow nR (by norm_num))
  have gCap : thinHighGcdCap n ≤ maximumStep n := cutoff.trans (by
    change cutoffU n ≤ cutoffU n*cofactorCap n
    simpa only [mul_one] using Nat.mul_le_mul_left (cutoffU n) cof)
  have C1 : expandedHighModulusCap n ≤ widerLowFarModulusCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have C2 : shortLowModulusCap n ≤ widerLowFarModulusCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have rest (h : widerLowFarModulusCap n < v) : remainingExpandedLow n u v :=
    ⟨(fun small => (not_le_of_gt (C1.trans_lt h)) small.1),
      (fun mid => (not_le_of_gt (C2.trans_lt h)) mid.2.2.1),
      (fun wide => (not_le_of_gt h) wide.2.2.1)⟩
  have long : maximumStep n < v := Nat.lt_of_not_ge (mem_filter.mp hj).2
  have level : u-1<v ↔ u≤v := by omega
  have dlo : reverseWeilStepLower n u < v ↔
      widerLowFarModulusCap n < v ∧ u ≤ v ∧ maximumStep n^2 < u*v ∧
      thinHighProductCap n < u*v ∧ highFarStripProductCap n < u*v := by
    simp only [reverseWeilStepLower, max_lt_iff, long, true_and, level,
      Nat.div_lt_iff_lt_mul u0, Nat.mul_comm v u]
  have dhi : v ≤ reverseWeilStepUpper n u ↔ u*v ≤ weilNearProductCap n := by
    have vN : v ≤ n := vr.2
    simp only [reverseWeilStepUpper, le_min_iff, vN, true_and, Nat.le_div_iff_mul_le u0, Nat.mul_comm v u]
  have gg : u.gcd v ∈ weilNearRowDivisors n u ↔ u.gcd v ∣ n ∧ u.gcd v ≤ thinHighGcdCap n := by
    rw [weilNearRowDivisors,mem_filter,Nat.mem_divisors]
    exact ⟨fun h => ⟨h.1.1,h.2.2⟩,fun h => ⟨⟨h.1,n0.ne'⟩,Nat.gcd_dvd_left _ _,h.2⟩⟩
  have rowItems : j ∈ reverseWeilRowItems n u (reverseWeilStepLower n u) (reverseWeilStepUpper n u) ↔
      reverseWeilShortCut n < j.2 ∧ v.gcd n ≤ sparseTargetDivisorCap n ∧ v.gcd n ≤ targetDivisorCap n ∧
      (u.gcd v ∣ n ∧ u.gcd v ≤ thinHighGcdCap n) ∧
      (widerLowFarModulusCap n < v ∧ u ≤ v ∧ maximumStep n^2 < u*v ∧ thinHighProductCap n < u*v ∧
        highFarStripProductCap n < u*v) ∧ u*v ≤ weilNearProductCap n := by
    simp only [reverseWeilRowItems,mem_filter,hj,true_and]
    change (reverseWeilShortCut n < j.2 ∧ j.2.gcd n ≤ sparseTargetDivisorCap n ∧
      j.2.gcd n ≤ targetDivisorCap n ∧ u.gcd v ∈ weilNearRowDivisors n u ∧
      reverseWeilStepLower n u < v ∧ v ≤ reverseWeilStepUpper n u) ↔ _
    rw [← long_right_low_gcd_eq hj]
    change (_ ∧ v.gcd n ≤ _ ∧ v.gcd n ≤ _ ∧ _ ∧ _ ∧ _) ↔ _
    rw [gg,dlo,dhi]
  change (i ∈ reverseWeilLeftRows n ∧
    j ∈ reverseWeilRowItems n u (reverseWeilStepLower n u) (reverseWeilStepUpper n u)) ↔ _
  rw [rowItems]
  have lRows : i ∈ reverseWeilLeftRows n ↔
      ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧ u ≤ ⌊(n : ℝ)^(1/2 : ℝ)⌋₊ ∧
      u ≤ expandedWideStepCap n ∧ u ≤ extendedWideStepCap n ∧ weilNearLeftKept n u := by
    simp only [reverseWeilLeftRows,mem_filter,hi,true_and]
    rfl
  rw [lRows]
  simp only [farInnerThinGate,boundedOuterLeftKeptGate,farInnerGate,prefixStepGate,weilNearLeftKept,
    retainedLowTargetMask,targetDivisorKept,reverseWeilExtra]
  constructor
  · rintro ⟨⟨geom,root,extCap,ext,left,sq⟩,short,sparse,target,⟨dvd,gcd⟩,⟨wide,size,mp,tp,fp⟩,top⟩
    exact ⟨extCap,geom,⟨⟨⟨⟨mp,gcd.trans gCap⟩,fp⟩,tp,gcd,target⟩,left⟩,
      ⟨rest wide,sparse⟩,sq,⟨root,ext,wide,size,top,short⟩,dvd⟩
  · rintro ⟨extCap,geom,⟨⟨⟨⟨mp,_⟩,fp⟩,tp,gcd,target⟩,left⟩,⟨_,sparse⟩,sq,
      ⟨root,ext,wide,size,top,short⟩,dvd⟩
    exact ⟨⟨geom,root,extCap,ext,left,sq⟩,short,sparse,target,⟨dvd,gcd⟩,⟨wide,size,mp,tp,fp⟩,top⟩

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_vaughan_convolution -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def coprimeProductItems (m lo hi : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 hi ×ˢ Icc 1 hi).filter fun x =>
    lo < x.1*x.2 ∧ x.1*x.2 ≤ hi ∧ (x.1*x.2).Coprime m

def coprimeWeightedWindow (m lo hi : ℕ) (w : ArithmeticFunction ℝ) (phase : ℕ → ℂ) : ℂ :=
  ∑ p ∈ (Ioc lo hi).filter (fun p => p.Coprime m), (w p : ℂ)*phase p

def coprimeWeightedProductWindow (m lo hi : ℕ) (a b : ArithmeticFunction ℝ) (phase : ℕ → ℂ) : ℂ :=
  ∑ x ∈ coprimeProductItems m lo hi, (a x.1 : ℂ)*(b x.2 : ℂ)*phase (x.1*x.2)

theorem coprime_weighted_convolution_window_eq (m lo hi : ℕ)
    (a b : ArithmeticFunction ℝ) (phase : ℕ → ℂ) :
    coprimeWeightedWindow m lo hi (a*b) phase =
      coprimeWeightedProductWindow m lo hi a b phase := by
  let J := (Ioc lo hi).filter (fun p => p.Coprime m)
  let K := coprimeProductItems m lo hi
  let prod (x : ℕ × ℕ) := x.1*x.2
  let f (x : ℕ × ℕ) := (a x.1 : ℂ)*(b x.2 : ℂ)*phase (prod x)
  have maps (x : ℕ × ℕ) (hx : x ∈ K) : prod x ∈ J := by
    obtain ⟨_,l,r,c⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨l,r⟩,c⟩
  have fibers (p : ℕ) (hp : p ∈ J) : (K.filter (fun x => prod x=p))=p.divisorsAntidiagonal := by
    ext x
    obtain ⟨rng,cop⟩ := mem_filter.mp hp
    obtain ⟨l,r⟩ := mem_Ioc.mp rng
    have p0 : 0 < p := (Nat.zero_le _).trans_lt l
    constructor
    · intro hx
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hx).2,p0.ne'⟩
    · intro hx
      have h := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have a1 : 1 ≤ x.1 := by
        by_contra! bad
        have h0 : x.1=0 := by omega
        rw [h0,zero_mul] at h
        exact p0.ne' h.symm
      have b1 : 1 ≤ x.2 := by
        by_contra! bad
        have h0 : x.2=0 := by omega
        rw [h0,mul_zero] at h
        exact p0.ne' h.symm
      have aTop : x.1 ≤ hi := calc
        _ ≤ x.1*x.2 := by simpa only [mul_one] using Nat.mul_le_mul_left _ b1
        _ ≤ _ := by rw [h]; exact r
      have bTop : x.2 ≤ hi := calc
        _ ≤ x.1*x.2 := by simpa only [one_mul] using Nat.mul_le_mul_right _ a1
        _ ≤ _ := by rw [h]; exact r
      have Kmem : x ∈ K := by
        apply mem_filter.mpr
        exact ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨a1,aTop⟩,mem_Icc.mpr ⟨b1,bTop⟩⟩,
          by rw [h]; exact ⟨l,r,cop⟩⟩
      exact mem_filter.mpr ⟨Kmem,h⟩
  change (∑ p ∈ J, ((a*b) p : ℂ)*phase p) = ∑ x ∈ K, f x
  rw [← sum_fiberwise_of_maps_to maps f]
  refine sum_congr rfl fun p hp => ?_
  rw [fibers p hp,ArithmeticFunction.mul_apply,Complex.ofReal_sum,sum_mul]
  refine sum_congr rfl fun x hx => ?_
  unfold f prod
  rw [Complex.ofReal_mul,(Nat.mem_divisorsAntidiagonal.mp hx).1]

theorem coprime_weighted_vaughan_window_eq (m lo hi P Q : ℕ)
    (qLo : Q ≤ lo) (phase : ℕ → ℂ) :
    let M := (μ : ArithmeticFunction ℝ)
    let u := truncateArithmetic M P
    let v := truncateArithmetic vonMangoldt Q
    coprimeWeightedWindow m lo hi vonMangoldt phase =
      coprimeWeightedProductWindow m lo hi u ArithmeticFunction.log phase -
      coprimeWeightedProductWindow m lo hi (u*v) (ζ : ArithmeticFunction ℝ) phase +
      coprimeWeightedProductWindow m lo hi (M-u) ((vonMangoldt-v)*(ζ : ArithmeticFunction ℝ)) phase := by
  dsimp only
  rw [← coprime_weighted_convolution_window_eq,← coprime_weighted_convolution_window_eq,
    ← coprime_weighted_convolution_window_eq]
  let M := (μ : ArithmeticFunction ℝ)
  let u := truncateArithmetic M P
  let v := truncateArithmetic vonMangoldt Q
  let Z := (ζ : ArithmeticFunction ℝ)
  unfold coprimeWeightedWindow
  rw [← sum_sub_distrib,← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  have pLo : Q < p := qLo.trans_lt (mem_Ioc.mp (mem_filter.mp hp).1).1
  have z : v p=0 := by simp [v,truncateArithmetic,not_le_of_gt pLo]
  have eq : (u*ArithmeticFunction.log) p-((u*v)*Z) p+v p+
      ((M-u)*((vonMangoldt-v)*Z)) p = vonMangoldt p := by
    have h := congrArg (fun q : ArithmeticFunction ℝ => q p) (vaughan_identity_real P Q)
    have sub (f g : ArithmeticFunction ℝ) : (f-g) p=f p-g p := rfl
    simpa only [ArithmeticFunction.add_apply,sub,mul_assoc,u,v,Z,M] using h
  rw [z,add_zero] at eq
  have ev := congrArg Complex.ofReal eq
  push_cast at ev
  change _ = (↑((u*ArithmeticFunction.log) p) : ℂ)*phase p -
    (↑(((u*v)*Z) p) : ℂ)*phase p +
    (↑(((M-u)*((vonMangoldt-v)*Z)) p) : ℂ)*phase p
  rw [← ev]
  ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_vaughan_rows -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open scoped Classical

noncomputable section

theorem coprime_weighted_product_window_eq_rows (m lo hi : ℕ)
    (a b : ArithmeticFunction ℝ) (phase : ℕ → ℂ) :
    coprimeWeightedProductWindow m lo hi a b phase =
      ∑ i ∈ (Icc 1 hi).filter (fun i => i.Coprime m), (a i : ℂ)*
        ∑ j ∈ (Ioc (lo/i) (hi/i)).filter (fun j => j.Coprime m),
          (b j : ℂ)*phase (i*j) := by
  unfold coprimeWeightedProductWindow coprimeProductItems
  rw [sum_filter,sum_product,sum_filter]
  refine sum_congr rfl fun i hiI => ?_
  have i0 : 0 < i := (mem_Icc.mp hiI).1
  by_cases ci : i.Coprime m
  · rw [if_pos ci]
    have row : (Icc 1 hi).filter (fun j => lo < i*j ∧ i*j ≤ hi ∧ (i*j).Coprime m) =
        (Ioc (lo/i) (hi/i)).filter (fun j => j.Coprime m) := by
      ext j
      constructor
      · intro jL
        obtain ⟨inJ,loJ,hiJ,cJ⟩ := mem_filter.mp jL
        have lower : lo/i<j := (Nat.div_lt_iff_lt_mul i0).mpr (by simpa only [Nat.mul_comm j i] using loJ)
        have upper : j≤hi/i := (Nat.le_div_iff_mul_le i0).mpr (by simpa only [Nat.mul_comm j i] using hiJ)
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lower,upper⟩,(Nat.coprime_mul_iff_left.mp cJ).2⟩
      · intro jR
        obtain ⟨win,cJ⟩ := mem_filter.mp jR
        obtain ⟨l,r⟩ := mem_Ioc.mp win
        have enough : 1 ≤ j := (Nat.zero_le _).trans_lt l
        have top : j ≤ hi := r.trans (Nat.div_le_self _ _)
        have lower : lo < i*j := by
          simpa only [Nat.mul_comm j i] using (Nat.div_lt_iff_lt_mul i0).mp l
        have upper : i*j ≤ hi := by
          simpa only [Nat.mul_comm j i] using (Nat.le_div_iff_mul_le i0).mp r
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨enough,top⟩,lower,upper,Nat.coprime_mul_iff_left.mpr ⟨ci,cJ⟩⟩
    rw [← sum_filter,row,mul_sum]
    exact sum_congr rfl fun j _ => mul_assoc _ _ _
  · rw [if_neg ci]
    refine sum_eq_zero fun j _ => ?_
    exact if_neg (fun h => ci (Nat.coprime_mul_iff_left.mp h.2.2).1)

theorem coprime_weighted_product_window_eq_short_rows (m lo hi D : ℕ)
    (a b : ArithmeticFunction ℝ) (phase : ℕ → ℂ) (hSupport : ∀ i : ℕ, D < i → a i = 0) :
    coprimeWeightedProductWindow m lo hi a b phase =
      ∑ i ∈ (Icc 1 (min D hi)).filter (fun i => i.Coprime m), (a i : ℂ)*
        ∑ j ∈ (Ioc (lo/i) (hi/i)).filter (fun j => j.Coprime m),
          (b j : ℂ)*phase (i*j) := by
  rw [coprime_weighted_product_window_eq_rows]
  symm
  apply sum_subset (filter_subset_filter _ (Icc_subset_Icc_right (min_le_right _ _)))
  intro i hiI outside
  have cause : D < i := by
    by_contra! small
    have h := mem_Icc.mp (mem_filter.mp hiI).1
    exact outside (mem_filter.mpr ⟨mem_Icc.mpr ⟨h.1,le_min small h.2⟩,(mem_filter.mp hiI).2⟩)
  rw [hSupport i cause,Complex.ofReal_zero,zero_mul]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_linear_inverse_ramp -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem norm_linear_inverse_ramp_le_weil {m : ℕ} [NeZero m] (c t : ZMod m)
    {L R : ℤ} (span : R-L ≤ m) (z : ℤ → ℤ)
    (phase : ∀ j, (z j : ZMod m) = c*(j : ZMod m)⁻¹-t) :
    ‖∑ j ∈ intIntervalModUnits m L R, (centeredInverseRamp m (z j-1) : ℂ)‖ ≤
      ((m.divisors.card : ℝ)*(1+Real.log m))*
        (weilReciprocalBudget m*Real.sqrt (m.gcd c.val)) := by
  let J := intIntervalModUnits m L R
  let I : Finset Unit := {()}
  let w (_ : Unit) : ℂ := 1
  let β (_ : ℤ) : ℂ := 1
  let lo (_ : Unit) : ℤ := L
  let hi (_ : Unit) : ℤ := R
  let f (j : ℤ) := c*(j : ZMod m)⁻¹-t
  let E := weilReciprocalBudget m*Real.sqrt (m.gcd c.val)
  have m0 : 0 < m := NeZero.pos m
  have e0 : 0 ≤ E := mul_nonneg (weil_reciprocal_budget_nonneg m0) (Real.sqrt_nonneg _)
  have gateSum (F : ℤ → ℂ) :
      gatedBilinearSum I J w β lo hi (fun _ j => F j)=∑ j ∈ J, F j := by
    unfold gatedBilinearSum I w β lo hi
    refine sum_congr rfl fun j hj => ?_
    have data : j ∈ Ioc L R ∧ IsUnit (j : ZMod m) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    simp only [sum_singleton,if_pos (mem_Ioc.mp data.1),one_mul]
  have bound (h : ZMod m) (_ : h ≠ 0) :
      ‖gatedBilinearSum I J w β lo hi (fun _ j => ZMod.stdAddChar (-(h*f j)))‖ ≤
        (0 : ℝ)+E*(m.gcd h.val : ℝ) := by
    rw [gateSum,zero_add]
    have expand :
        (∑ j ∈ J, ZMod.stdAddChar (-(h*f j))) =
          ZMod.stdAddChar (h*t)*(∑ j ∈ J, ZMod.stdAddChar ((-(h*c))*(j : ZMod m)⁻¹)) := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [← AddChar.map_add_eq_mul]
      congr 1
      unfold f
      ring
    rw [expand,norm_mul,norm_stdAddChar_eq_one,one_mul]
    let G := (m.gcd h.val : ℝ)
    have G1 : 1 ≤ G := by
      unfold G
      exact_mod_cast (show 1 ≤ m.gcd h.val from Nat.gcd_pos_of_pos_left _ m0)
    have gcdE : Real.sqrt (m.gcd (-(h*c)).val) ≤ Real.sqrt (m.gcd c.val)*G := by
      have gcd : (m.gcd (-(h*c)).val : ℝ) ≤ (m.gcd c.val : ℝ)*G := by
        unfold G
        exact_mod_cast (gcd_fourier_phase_product_le h c).trans_eq (Nat.mul_comm _ _)
      calc
        _ ≤ Real.sqrt ((m.gcd c.val : ℝ)*G) := Real.sqrt_le_sqrt gcd
        _ = Real.sqrt (m.gcd c.val)*Real.sqrt G := by rw [Real.sqrt_mul (by positivity)]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr G1)) (Real.sqrt_nonneg _)
    calc
      _ ≤ weilReciprocalBudget m*Real.sqrt (m.gcd (-(h*c)).val) :=
        norm_modular_unit_inverse_interval_le_weil (-(h*c)) span
      _ ≤ weilReciprocalBudget m*(Real.sqrt (m.gcd c.val)*G) :=
        mul_le_mul_of_nonneg_left gcdE (weil_reciprocal_budget_nonneg m0)
      _ = _ := by unfold E G; ring
  have log0 : 0 ≤ 1+Real.log (m : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m from m0)))
  have sol := norm_gated_inverse_ramp_le_of_prefix_bounds m0 I J w β lo hi (fun _ j => z j)
    (show 0 ≤ ((m.divisors.card : ℝ)*(1+Real.log m))*E by positivity)
    (fun k _ => by
      have h := norm_gated_interval_residue_le_of_frequency_bounds I J w β lo hi
        (fun _ j => f j) (show (0 : ℤ) ≤ (k : ℤ)+1 by positivity) (D := 0) (E := E) le_rfl e0 bound
      simpa only [phase,f,mul_zero,zero_add] using h)
  rw [gateSum] at sol
  exact sol

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_linear_inverse_periods -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem sum_mod_units_interval_split {m : ℕ} {a b c : ℤ} (ab : a ≤ b) (bc : b ≤ c) (f : ℤ → ℂ) :
    (∑ j ∈ intIntervalModUnits m a c, f j) =
      (∑ j ∈ intIntervalModUnits m a b, f j)+(∑ j ∈ intIntervalModUnits m b c, f j) := by
  have expand {r s : ℤ} (rs : a ≤ r) (sc : s ≤ c) :
      gatedBilinearSum ({()} : Finset Unit) (intIntervalModUnits m r s) (fun _ => 1)
        (fun _ => 1) (fun _ => a) (fun _ => c) (fun _ j => f j) =
      ∑ j ∈ intIntervalModUnits m r s, f j := by
    unfold gatedBilinearSum
    refine sum_congr rfl fun j hj => ?_
    have h : j ∈ Ioc r s ∧ IsUnit (j : ZMod m) := by
      simpa only [intIntervalModUnits,mem_filter] using hj
    have flag : a<j ∧ j≤c :=
      ⟨rs.trans_lt (mem_Ioc.mp h.1).1,(mem_Ioc.mp h.1).2.trans sc⟩
    simp only [sum_singleton,if_pos flag,one_mul]
  have h := gated_bilinear_sum_split_unit_intervals m ({()} : Finset Unit) (fun _ => 1)
    (fun _ => 1) (fun _ => a) (fun _ => c) (fun _ j => f j) ab bc
  rw [expand le_rfl le_rfl,expand le_rfl bc,expand ab le_rfl] at h
  exact h

theorem norm_linear_inverse_ramp_le_weil_periods {m : ℕ} [NeZero m] (c t : ZMod m)
    {L R : ℤ} (ordered : L ≤ R) (z : ℤ → ℤ)
    (phase : ∀ j, (z j : ZMod m) = c*(j : ZMod m)⁻¹-t) :
    ‖∑ j ∈ intIntervalModUnits m L R, (centeredInverseRamp m (z j-1) : ℂ)‖ ≤
      ((((R-L).toNat/m : ℕ) : ℝ)+1)*
        (((m.divisors.card : ℝ)*(1+Real.log m))*(weilReciprocalBudget m*Real.sqrt (m.gcd c.val))) := by
  let H := (R-L).toNat
  let k := H/m
  let r := H%m
  let B := ((m.divisors.card : ℝ)*(1+Real.log m))*(weilReciprocalBudget m*Real.sqrt (m.gcd c.val))
  let f (j : ℤ) := (centeredInverseRamp m (z j-1) : ℂ)
  have m0 : 0 < m := NeZero.pos m
  have intM : (0 : ℤ) ≤ m := by positivity
  have bh (x : ℤ) (w : ℕ) (wm : w ≤ m) :
      ‖∑ j ∈ intIntervalModUnits m x (x+(w : ℤ)), f j‖ ≤ B := by
    apply norm_linear_inverse_ramp_le_weil c t (z := z) (phase := phase)
    rw [add_sub_cancel_left]
    exact_mod_cast wm
  have blocks (a : ℕ) :
      ‖∑ j ∈ intIntervalModUnits m L (L+((a*m : ℕ) : ℤ)), f j‖ ≤ (a : ℝ)*B := by
    induction a with
    | zero =>
      have empty : intIntervalModUnits m L L = ∅ := by simp [intIntervalModUnits]
      simp [empty]
    | succ a ih =>
      let mid := L+((a*m : ℕ) : ℤ)
      have left : L ≤ mid := by unfold mid; exact le_add_of_nonneg_right (by positivity)
      have right : mid ≤ mid+(m : ℤ) := le_add_of_nonneg_right intM
      rw [Nat.succ_mul,Nat.cast_add,← add_assoc]
      rw [sum_mod_units_interval_split left right f]
      exact (norm_add_le _ _).trans ((add_le_add ih (bh mid m le_rfl)).trans_eq (by push_cast; ring))
  have len : k*m+r=H := by unfold k r; rw [Nat.mul_comm]; exact Nat.div_add_mod H m
  let mid := L+((k*m : ℕ) : ℤ)
  have tail : mid+(r : ℤ)=R := by
    have cast := congrArg (fun x : ℕ => (x : ℤ)) len
    push_cast at cast
    change (k : ℤ)*(m : ℤ)+(r : ℤ) = (H : ℤ) at cast
    have Hcast : (H : ℤ)=R-L := Int.toNat_of_nonneg (sub_nonneg.mpr ordered)
    unfold mid
    push_cast
    rw [add_assoc,cast,Hcast,add_sub_cancel]
  have left : L ≤ mid := by unfold mid; exact le_add_of_nonneg_right (by positivity)
  have right : mid ≤ R := by rw [← tail]; exact le_add_of_nonneg_right (by positivity)
  have last := bh mid r (Nat.mod_lt _ m0).le
  rw [tail] at last
  change ‖∑ j ∈ intIntervalModUnits m L R, f j‖ ≤ ((k : ℝ)+1)*B
  rw [sum_mod_units_interval_split left right f]
  exact (norm_add_le _ _).trans ((add_le_add (blocks k) last).trans_eq (by ring))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_log_weighted_reciprocal_prefix -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

private theorem log_wave_step_sum {k r : ℕ} (kr : k ≤ r) :
    (∑ j ∈ Icc k r, logWaveStep r j) = Real.log k := by
  have indices : Icc k r = Ico k (r+1) := by
    ext j
    simp only [mem_Icc,mem_Ico]
    omega
  rw [indices,sum_Ico_eq_sum_range]
  unfold logWaveStep
  have sum := sum_range_sub (fun j => -clippedLog r (k+j)) (r+1-k)
  have stop : k+(r+1-k)=r+1 := Nat.add_sub_of_le (kr.trans (Nat.le_succ _))
  have last : ¬r+1 ≤ r := by omega
  simpa only [neg_sub_neg,Nat.add_assoc,stop,Nat.add_zero,clippedLog,last,kr,ite_true,ite_false,
    neg_zero,zero_sub,neg_neg] using sum

theorem norm_log_weighted_sum_le_of_prefix_bounds (l r : ℕ) (f : ℕ → ℂ) {B : ℝ} (B0 : 0 ≤ B)
    (hPrefix : ∀ j ∈ Ioc l r, ‖∑ k ∈ Ioc l j, f k‖ ≤ B) :
    ‖∑ k ∈ Ioc l r, (Real.log (k : ℝ) : ℂ)*f k‖ ≤ (2*Real.log r)*B := by
  have expand : (∑ k ∈ Ioc l r, (Real.log (k : ℝ) : ℂ)*f k) =
      ∑ j ∈ Ioc l r, (logWaveStep r j : ℂ)*(∑ k ∈ Ioc l j, f k) := by
    symm
    calc
      _ = ∑ j ∈ Ioc l r,∑ k ∈ Ioc l r, if k≤j then (logWaveStep r j : ℂ)*f k else 0 := by
        refine sum_congr rfl fun j hj => ?_
        have changeSet : (Ioc l r).filter (fun k => k≤j)=Ioc l j := by
          ext k
          simp only [mem_filter,mem_Ioc]
          have top := (mem_Ioc.mp hj).2
          omega
        rw [← changeSet,mul_sum,sum_filter]
      _ = ∑ k ∈ Ioc l r,∑ j ∈ Icc k r, (logWaveStep r j : ℂ)*f k := by
        rw [sum_comm]
        refine sum_congr rfl fun k hk => ?_
        have changeSet : (Ioc l r).filter (fun j => k≤j)=Icc k r := by
          ext j
          simp only [mem_filter,mem_Ioc,mem_Icc]
          have lower := (mem_Ioc.mp hk).1
          omega
        rw [← sum_filter,changeSet]
      _ = _ := by
        refine sum_congr rfl fun k hk => ?_
        rw [← sum_mul,← Complex.ofReal_sum,log_wave_step_sum (mem_Ioc.mp hk).2]
  rw [expand]
  calc
    _ ≤ ∑ j ∈ Ioc l r, ‖(logWaveStep r j : ℂ)*(∑ k ∈ Ioc l j, f k)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Ioc l r, ‖(logWaveStep r j : ℂ)‖*B := by
      refine sum_le_sum fun j hj => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hPrefix j hj) (norm_nonneg _)
    _ = (∑ j ∈ Ioc l r, ‖(logWaveStep r j : ℂ)‖)*B := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (log_wave_prefix_weights_le l r) B0

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_nat_inverse_ramp -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

def inverseRampNat {m : ℕ} (c t : ZMod m) (q : ℕ) : ℝ :=
  centeredInverseRamp m ((((c*(q : ZMod m)⁻¹-t).val : ℕ) : ℤ)-1)

def linearWeilRampScale {m : ℕ} (c : ZMod m) (H : ℕ) : ℝ :=
  (((H/m : ℕ) : ℝ)+1)*
    (((m.divisors.card : ℝ)*(1+Real.log m))*(weilReciprocalBudget m*Real.sqrt (m.gcd c.val)))

theorem linear_weil_ramp_scale_nonneg {m : ℕ} [NeZero m] (c : ZMod m) (H : ℕ) :
    0 ≤ linearWeilRampScale c H := by
  have m0 : 0 < m := NeZero.pos m
  have log0 : 0 ≤ 1+Real.log (m : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m from m0)))
  have b := weil_reciprocal_budget_nonneg m0
  unfold linearWeilRampScale
  positivity

theorem linear_weil_ramp_scale_mono {m : ℕ} [NeZero m] (c : ZMod m) : Monotone (linearWeilRampScale c) := by
  intro a b ab
  have m0 : 0 < m := NeZero.pos m
  have log0 : 0 ≤ 1+Real.log (m : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast (show 1 ≤ m from m0)))
  have bb := weil_reciprocal_budget_nonneg m0
  unfold linearWeilRampScale
  exact mul_le_mul_of_nonneg_right (add_le_add (by exact_mod_cast Nat.div_le_div_right ab) (le_refl _)) (by positivity)

theorem norm_nat_interval_inverse_ramp_le {m : ℕ} [NeZero m] (c t : ZMod m)
    {a b : ℕ} (ordered : a ≤ b) :
    ‖∑ j ∈ (Ioc a b).filter (fun j => j.Coprime m), (inverseRampNat c t j : ℂ)‖ ≤
      linearWeilRampScale c (b-a) := by
  let J := (Ioc a b).filter (fun j => j.Coprime m)
  let ℓ : ℕ ↪ ℤ := ⟨fun j => (j : ℤ),fun x y h => by change (x : ℤ) = (y : ℤ) at h; exact_mod_cast h⟩
  let z (q : ℤ) : ℤ := ((c*(q : ZMod m)⁻¹-t).val : ℕ)
  have sets : J.map ℓ=intIntervalModUnits m a b := by
    ext q
    constructor
    · intro h
      obtain ⟨j,hj,eq⟩ := mem_map.mp h
      have data := mem_filter.mp hj
      obtain ⟨al,br⟩ := mem_Ioc.mp data.1
      change (j : ℤ)=q at eq
      have x : q ∈ Ioc (a : ℤ) (b : ℤ) ∧ IsUnit (q : ZMod m) := by
        rw [← eq]
        exact ⟨mem_Ioc.mpr ⟨by exact_mod_cast al,by exact_mod_cast br⟩,by
          rw [Int.cast_natCast]
          exact (ZMod.isUnit_iff_coprime j m).mpr data.2⟩
      simpa only [intIntervalModUnits,mem_filter] using x
    · intro h
      have data : q ∈ Ioc (a : ℤ) (b : ℤ) ∧ IsUnit (q : ZMod m) := by
        simpa only [intIntervalModUnits,mem_filter] using h
      obtain ⟨al,br⟩ := mem_Ioc.mp data.1
      have q0 : 0 ≤ q := (Int.natCast_nonneg a).trans al.le
      have cast : (q.toNat : ℤ)=q := Int.toNat_of_nonneg q0
      refine mem_map.mpr ⟨q.toNat,?_,cast⟩
      have lo : a < q.toNat := by exact_mod_cast (show (a : ℤ) < (q.toNat : ℤ) by rwa [cast])
      have hi : q.toNat ≤ b := by exact_mod_cast (show (q.toNat : ℤ) ≤ (b : ℤ) by rwa [cast])
      have unit : IsUnit (q.toNat : ZMod m) := by
        have same : (q.toNat : ZMod m) = (q : ZMod m) := by
          simpa only [Int.cast_natCast] using congrArg (fun j : ℤ => (j : ZMod m)) cast
        exact same.symm ▸ data.2
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lo,hi⟩,(ZMod.isUnit_iff_coprime _ _).mp unit⟩
  have eq : (∑ j ∈ J, (inverseRampNat c t j : ℂ)) =
      ∑ q ∈ intIntervalModUnits m a b, (centeredInverseRamp m (z q-1) : ℂ) := by
    rw [← sets,sum_map]
    refine sum_congr rfl fun j _ => ?_
    unfold inverseRampNat z
    change _ = (centeredInverseRamp m
      ((((c*((j : ℤ) : ZMod m)⁻¹-t).val : ℕ) : ℤ)-1) : ℂ)
    rw [Int.cast_natCast]
  rw [eq]
  have h := norm_linear_inverse_ramp_le_weil_periods c t
    (show (a : ℤ) ≤ (b : ℤ) by exact_mod_cast ordered) z (fun j => by
      unfold z
      rw [Int.cast_natCast,ZMod.natCast_zmod_val])
  have diff : ((b : ℤ)-(a : ℤ)).toNat=b-a := by
    rw [← Int.ofNat_sub ordered,Int.toNat_natCast]
  rw [diff] at h
  exact h

theorem norm_log_nat_interval_inverse_ramp_le {m : ℕ} [NeZero m] (c t : ZMod m)
    (a b : ℕ) :
    ‖∑ j ∈ (Ioc a b).filter (fun j => j.Coprime m),
        (Real.log (j : ℝ) : ℂ)*(inverseRampNat c t j : ℂ)‖ ≤
      (2*Real.log b)*linearWeilRampScale c (b-a) := by
  let f (j : ℕ) : ℂ := if j.Coprime m then (inverseRampNat c t j : ℂ) else 0
  have eq : (∑ j ∈ (Ioc a b).filter (fun j => j.Coprime m),
      (Real.log (j : ℝ) : ℂ)*(inverseRampNat c t j : ℂ)) =
      ∑ j ∈ Ioc a b, (Real.log (j : ℝ) : ℂ)*f j := by
    rw [sum_filter]
    refine sum_congr rfl fun j _ => ?_
    by_cases d : j.Coprime m <;> simp [f,d]
  rw [eq]
  apply norm_log_weighted_sum_le_of_prefix_bounds a b f (linear_weil_ramp_scale_nonneg c _)
  intro j hj
  have hr := mem_Ioc.mp hj
  have mono : j-a ≤ b-a := Nat.sub_le_sub_right hr.2 _
  have eqj : (∑ k ∈ Ioc a j, f k) =
      ∑ k ∈ (Ioc a j).filter (fun k => k.Coprime m), (inverseRampNat c t k : ℂ) := by
    rw [sum_filter]
  rw [eqj]
  exact (norm_nat_interval_inverse_ramp_le c t hr.1.le).trans (linear_weil_ramp_scale_mono c mono)

theorem inverse_ramp_nat_mul_right {m i j : ℕ} (c t : ZMod m)
    (ic : i.Coprime m) (jc : j.Coprime m) :
    inverseRampNat c t (i*j)=inverseRampNat (c*(i : ZMod m)⁻¹) t j := by
  have inv : ((i : ZMod m)*(j : ZMod m))⁻¹ = (i : ZMod m)⁻¹*(j : ZMod m)⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one
    calc
      _ = ((i : ZMod m)*(i : ZMod m)⁻¹)*((j : ZMod m)*(j : ZMod m)⁻¹) := by ring
      _ = _ := by rw [ZMod.coe_mul_inv_eq_one i ic,ZMod.coe_mul_inv_eq_one j jc,one_mul]
  unfold inverseRampNat
  rw [Nat.cast_mul,inv,mul_assoc]

theorem gcd_val_mul_unit_le {m : ℕ} [NeZero m] (c u : ZMod m) (unit : IsUnit u) :
    m.gcd (c*u).val ≤ m.gcd c.val := by
  have cp : (-u).val.Coprime m := (ZMod.isUnit_iff_coprime _ _).mp (by
    rw [ZMod.natCast_zmod_val]
    exact unit.neg)
  have g : m.gcd (-u).val=1 := by rw [Nat.gcd_comm,cp.gcd_eq_one]
  have h := gcd_fourier_phase_product_le (-u) c
  rw [neg_mul,neg_neg,mul_comm u c,g,one_mul] at h
  exact h

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_vaughan_type_one -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4MoebiusGauss
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

private theorem linear_weil_ramp_scale_mul_inverse_le {m i : ℕ} [NeZero m] (c : ZMod m)
    (cop : i.Coprime m) (H : ℕ) :
    linearWeilRampScale (c*(i : ZMod m)⁻¹) H ≤ linearWeilRampScale c H := by
  have u : IsUnit ((i : ZMod m)⁻¹) := by
    obtain ⟨v,eq⟩ := (ZMod.isUnit_iff_coprime i m).mpr cop
    rw [← eq,ZMod.inv_coe_unit]
    exact Units.isUnit _
  have gc : (m.gcd (c*(i : ZMod m)⁻¹).val : ℝ) ≤ (m.gcd c.val : ℝ) := by
    exact_mod_cast gcd_val_mul_unit_le c ((i : ZMod m)⁻¹) u
  have B0 := weil_reciprocal_budget_nonneg (NeZero.pos m)
  have log0 : 0 ≤ 1+Real.log (m : ℝ) :=
    add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast (NeZero.pos m : 1 ≤ m)))
  unfold linearWeilRampScale
  gcongr

theorem norm_coprime_weighted_product_window_le_short_rows {m lo hi D : ℕ}
    (a b : ArithmeticFunction ℝ) (phase : ℕ → ℂ) {C R : ℝ} (C0 : 0 ≤ C) (R0 : 0 ≤ R)
    (hSupport : ∀ i : ℕ, D < i → a i=0)
    (α : ∀ i≤hi, ‖(a i : ℂ)‖ ≤ C)
    (row : ∀ i ∈ (Icc 1 (min D hi)).filter (fun i => i.Coprime m),
      ‖∑ j ∈ (Ioc (lo/i) (hi/i)).filter (fun j => j.Coprime m),
        (b j : ℂ)*phase (i*j)‖ ≤ R) :
    ‖coprimeWeightedProductWindow m lo hi a b phase‖ ≤ (D : ℝ)*C*R := by
  let I := (Icc 1 (min D hi)).filter (fun i => i.Coprime m)
  let F (i : ℕ) := ∑ j ∈ (Ioc (lo/i) (hi/i)).filter (fun j => j.Coprime m),
    (b j : ℂ)*phase (i*j)
  have iCard : (#I : ℝ) ≤ (D : ℝ) := by
    have n : #I ≤ D := (card_filter_le _ _).trans (by simp [Nat.card_Icc])
    exact_mod_cast n
  rw [coprime_weighted_product_window_eq_short_rows m lo hi D a b phase hSupport]
  change ‖∑ i ∈ I, (a i : ℂ)*F i‖ ≤ _
  calc
    _ ≤ ∑ i ∈ I, ‖(a i : ℂ)*F i‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ I,C*R := by
      refine sum_le_sum fun i hiI => ?_
      rw [norm_mul]
      have ni : i ≤ hi := (mem_Icc.mp (mem_filter.mp hiI).1).2.trans (min_le_right _ _)
      exact mul_le_mul (α i ni) (row i hiI) (norm_nonneg _) C0
    _ = (#I : ℝ)*(C*R) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := (mul_le_mul_of_nonneg_right iCard (mul_nonneg C0 R0)).trans_eq (by ring)

theorem norm_inverse_ramp_log_type_one_le {n m lo hi D : ℕ} [NeZero m] (c t : ZMod m)
    (hin : hi ≤ n) (a : ArithmeticFunction ℝ) {C : ℝ} (C0 : 0 ≤ C)
    (hSupport : ∀ i : ℕ, D < i → a i = 0) (aBound : ∀ i ≤ hi, ‖(a i : ℂ)‖ ≤ C) :
    ‖coprimeWeightedProductWindow m lo hi a ArithmeticFunction.log
        (fun p => (inverseRampNat c t p : ℂ))‖ ≤
      (D : ℝ)*C*(2*logBudget n*linearWeilRampScale c hi) := by
  have L0 := zero_le_one.trans (one_le_logBudget n)
  apply norm_coprime_weighted_product_window_le_short_rows a _ _ C0
    (mul_nonneg (by positivity) (linear_weil_ramp_scale_nonneg c hi)) hSupport aBound
  intro i hiI
  let k := c*(i : ZMod m)⁻¹
  let R := hi/i
  let L := lo/i
  have ci : i.Coprime m := (mem_filter.mp hiI).2
  have eq :
      (∑ j ∈ (Ioc L R).filter (fun j => j.Coprime m), (ArithmeticFunction.log j : ℂ)*
        (inverseRampNat c t (i*j) : ℂ)) =
      ∑ j ∈ (Ioc L R).filter (fun j => j.Coprime m), (Real.log (j : ℝ) : ℂ)*(inverseRampNat k t j : ℂ) := by
    refine sum_congr rfl fun j hj => ?_
    rw [ArithmeticFunction.log_apply,inverse_ramp_nat_mul_right c t ci (mem_filter.mp hj).2]
  change ‖∑ j ∈ (Ioc L R).filter (fun j => j.Coprime m), (ArithmeticFunction.log j : ℂ)*
    (inverseRampNat c t (i*j) : ℂ)‖ ≤ _
  rw [eq]
  have span : R-L ≤ hi := (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
  have log : Real.log (R : ℝ) ≤ logBudget n := by
    by_cases zero : R=0
    · simpa only [zero,Nat.cast_zero,Real.log_zero] using L0
    · exact log_le_logBudget (Nat.pos_of_ne_zero zero) ((Nat.div_le_self _ _).trans hin)
  have sc := (linear_weil_ramp_scale_mono k span).trans (linear_weil_ramp_scale_mul_inverse_le c ci hi)
  exact (norm_log_nat_interval_inverse_ramp_le k t L R).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left log (by norm_num)) sc
      (linear_weil_ramp_scale_nonneg k _) (by positivity))

theorem norm_inverse_ramp_zeta_type_one_le {m lo hi D : ℕ} [NeZero m] (c t : ZMod m)
    (ord : lo ≤ hi) (a : ArithmeticFunction ℝ) {C : ℝ} (C0 : 0 ≤ C)
    (hSupport : ∀ i : ℕ, D < i → a i = 0) (aBound : ∀ i ≤ hi, ‖(a i : ℂ)‖ ≤ C) :
    ‖coprimeWeightedProductWindow m lo hi a (ζ : ArithmeticFunction ℝ)
        (fun p => (inverseRampNat c t p : ℂ))‖ ≤
      (D : ℝ)*C*linearWeilRampScale c hi := by
  apply norm_coprime_weighted_product_window_le_short_rows a _ _
    C0 (linear_weil_ramp_scale_nonneg c hi) hSupport aBound
  intro i hiI
  let k := c*(i : ZMod m)⁻¹
  let R := hi/i
  let L := lo/i
  have ci : i.Coprime m := (mem_filter.mp hiI).2
  have eq :
      (∑ j ∈ (Ioc L R).filter (fun j => j.Coprime m), ((ζ : ArithmeticFunction ℝ) j : ℂ)*
        (inverseRampNat c t (i*j) : ℂ)) =
      ∑ j ∈ (Ioc L R).filter (fun j => j.Coprime m), (inverseRampNat k t j : ℂ) := by
    refine sum_congr rfl fun j hj => ?_
    have pos : 0 < j := (Nat.zero_le _).trans_lt (mem_Ioc.mp (mem_filter.mp hj).1).1
    rw [inverse_ramp_nat_mul_right c t ci (mem_filter.mp hj).2,natCoe_apply,
      zeta_apply_ne pos.ne',Nat.cast_one,Complex.ofReal_one,one_mul]
  change ‖∑ j ∈ (Ioc L R).filter (fun j => j.Coprime m),
    ((ζ : ArithmeticFunction ℝ) j : ℂ)*(inverseRampNat c t (i*j) : ℂ)‖ ≤ _
  rw [eq]
  have span : R-L ≤ hi := (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
  exact (norm_nat_interval_inverse_ramp_le k t (Nat.div_le_div_right ord)).trans
    ((linear_weil_ramp_scale_mono k span).trans (linear_weil_ramp_scale_mul_inverse_le c ci hi))

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_vaughan_short_budget -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4MoebiusGauss
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

theorem norm_inverse_vaughan_short_parts_le {n m lo hi : ℕ} [NeZero m] (c t : ZMod m)
    (n1 : 1 ≤ n) (hin : hi ≤ n) (mN : m ≤ n) (order : lo ≤ hi)
    (hiTop : (hi : ℝ) ≤ (n : ℝ)^(33/64 : ℝ))
    (mLo : (n : ℝ)^(2/5 : ℝ) ≤ (m : ℝ)) (mHi : (m : ℝ) ≤ (n : ℝ)^(1/2 : ℝ))
    (gCap : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (divs : ∀ b ≤ n, (b.divisors.card : ℝ) ≤ T) :
    let P := vaughanShortCut n
    let u := truncateArithmetic (μ : ArithmeticFunction ℝ) P
    let v := truncateArithmetic vonMangoldt P
    let phase := fun p => (inverseRampNat c t p : ℂ)
    ‖coprimeWeightedProductWindow m lo hi u ArithmeticFunction.log phase -
      coprimeWeightedProductWindow m lo hi (u*v) (ζ : ArithmeticFunction ℝ) phase‖ ≤
      18*T^3*logBudget n^3*(n : ℝ)^(2/5 : ℝ) := by
  dsimp only
  let P := vaughanShortCut n
  let u := truncateArithmetic (μ : ArithmeticFunction ℝ) P
  let v := truncateArithmetic vonMangoldt P
  let f (p : ℕ) := (inverseRampNat c t p : ℂ)
  let L := logBudget n
  let N := (n : ℝ)
  let M := (m : ℝ)
  let B := linearWeilRampScale c hi
  have nR : 1 ≤ N := by unfold N; exact_mod_cast n1
  have n0 := zero_lt_one.trans_le nR
  have mR : 0 < M := by unfold M; exact_mod_cast NeZero.pos m
  have T0 := zero_le_one.trans T1
  have L1 : 1 ≤ L := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have B0 : 0 ≤ B := linear_weil_ramp_scale_nonneg c hi
  have um (q : ℕ) : ‖(u q : ℂ)‖ ≤ 1 := by
    change ‖(((if q≤P then (μ q : ℝ) else 0) : ℝ) : ℂ)‖ ≤ 1
    by_cases h : q≤P
    · simpa only [if_pos h,moebiusComplex,Complex.ofReal_intCast] using norm_moebiusComplex_le_one q
    · simp [h]
  have vm (q : ℕ) (qn : q ≤ n) : ‖(v q : ℂ)‖ ≤ L := by
    change ‖(((if q≤P then vonMangoldt q else 0) : ℝ) : ℂ)‖ ≤ L
    by_cases h : q≤P
    · rw [if_pos h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
      by_cases p0 : q=0
      · simp [p0,L0]
      · exact vonMangoldt_le_log.trans (log_le_logBudget (Nat.pos_of_ne_zero p0) qn)
    · simp [h,L0]
  have coeff (q : ℕ) (qn : q ≤ hi) : ‖((u*v) q : ℂ)‖ ≤ T*L := by
    have h := norm_convolution_apply_le (qn.trans hin) u v zero_le_one L0
      (divs q (qn.trans hin)) (fun x _ => um x) vm
    simpa only [one_mul] using h
  have short (q : ℕ) (hq : P < q) : u q=0 := by simp [u,truncateArithmetic,not_le_of_gt hq]
  have long (q : ℕ) (hq : P*P < q) : (u*v) q=0 :=
    truncate_moebius_mangoldt_support (show P*P≤P*P from le_rfl) q hq
  have partLog := norm_inverse_ramp_log_type_one_le (lo := lo) (D := P) c t hin u zero_le_one short
    (fun x _ => um x)
  have partZeta := norm_inverse_ramp_zeta_type_one_le (D := P*P) c t order (u*v)
    (mul_nonneg T0 L0) long coeff
  have gap : (hi : ℝ)/M ≤ N^(1/8 : ℝ) := by
    apply (div_le_iff₀ mR).mpr
    calc
      _ ≤ N^(33/64 : ℝ) := hiTop
      _ ≤ N^(1/8+2/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le nR (by norm_num)
      _ = N^(1/8 : ℝ)*N^(2/5 : ℝ) := Real.rpow_add n0 _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left mLo (by positivity)
  have divGap : (((hi/m : ℕ) : ℝ)+1) ≤ 2*N^(1/8 : ℝ) := by
    have h := (show ((hi/m : ℕ) : ℝ) ≤ (hi : ℝ)/M from Nat.cast_div_le).trans gap
    have h2 : 1 ≤ N^(1/8 : ℝ) := Real.one_le_rpow nR (by norm_num)
    linarith only [h,h2]
  have sqrtPow (p : ℝ) : Real.sqrt (N^p)=N^(p/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul n0.le]
    congr 1
    ring
  have smr : Real.sqrt M ≤ N^(1/4 : ℝ) := by
    calc
      _ ≤ Real.sqrt (N^(1/2 : ℝ)) := Real.sqrt_le_sqrt mHi
      _ = _ := by rw [sqrtPow]; norm_num
  have gr : Real.sqrt (m.gcd c.val) ≤ N^(1/4096 : ℝ) := by
    calc
      _ ≤ Real.sqrt (N^(1/2048 : ℝ)) := Real.sqrt_le_sqrt gCap
      _ = _ := by rw [sqrtPow]; norm_num
  have log : 1+Real.log (m : ℝ) ≤ L := by
    unfold L logBudget
    have mr : (m : ℝ) ≤ n := by exact_mod_cast mN
    exact add_le_add (le_refl _) (Real.log_le_log mR (by linarith only [mr]))
  have log3 : 3+2*Real.log m ≤ 3*L := by linarith only [L1,log]
  have logN : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (NeZero.pos m : 1 ≤ m))
  have D := divs m mN
  have bBound : B ≤ 6*T^2*L^2*N^(1/8+1/4+1/4096 : ℝ) := by
    unfold B linearWeilRampScale weilReciprocalBudget
    calc
      _ ≤ (2*N^(1/8 : ℝ))*(T*L*((3*L*T*N^(1/4 : ℝ))*N^(1/4096 : ℝ))) := by gcongr
      _ = 6*T^2*L^2*(N^(1/8 : ℝ)*N^(1/4 : ℝ)*N^(1/4096 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add n0,← Real.rpow_add n0]
  have smallP : (P : ℝ) ≤ N^(1/96 : ℝ) := Nat.floor_le (by positivity)
  have largeP : (P : ℝ) ≤ N^(1/48 : ℝ) :=
    smallP.trans (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have sqP : (P : ℝ)^2 ≤ N^(1/48 : ℝ) := by
    calc
      _ ≤ (N^(1/96 : ℝ))^2 := pow_le_pow_left₀ (by positivity) smallP 2
      _ = _ := by rw [← Real.rpow_mul_natCast n0.le]; norm_num
  have logCoeff : (P : ℝ)*(2*L) ≤ 2*T*L*N^(1/48 : ℝ) := by
    calc
      _ ≤ N^(1/48 : ℝ)*(2*L) := mul_le_mul_of_nonneg_right largeP (by positivity)
      _ ≤ (T*N^(1/48 : ℝ))*(2*L) := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left (by positivity) T1) (by positivity)
      _ = _ := by ring
  have zetaCoeff : (P : ℝ)^2*T*L ≤ T*L*N^(1/48 : ℝ) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right sqP T0) L0).trans_eq (by ring)
  change ‖coprimeWeightedProductWindow m lo hi u ArithmeticFunction.log f -
    coprimeWeightedProductWindow m lo hi (u*v) (ζ : ArithmeticFunction ℝ) f‖ ≤ _
  calc
    _ ≤ (P : ℝ)*1*(2*L*B)+((P*P : ℕ) : ℝ)*(T*L)*B :=
      (norm_sub_le _ _).trans (add_le_add partLog partZeta)
    _ = ((P : ℝ)*(2*L)+(P : ℝ)^2*T*L)*B := by push_cast; ring
    _ ≤ (3*T*L*N^(1/48 : ℝ))*(6*T^2*L^2*N^(1/8+1/4+1/4096 : ℝ)) := by
      apply mul_le_mul _ bBound B0 (by positivity)
      exact (add_le_add logCoeff zetaCoeff).trans_eq (by ring)
    _ = 18*T^3*L^3*N^(1/48+1/8+1/4+1/4096 : ℝ) := by
      calc
        _ = 18*T^3*L^3*(N^(1/48 : ℝ)*N^(1/8+1/4+1/4096 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add n0]; congr 2 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le nR (by norm_num)) (by positivity)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_vaughan_near_scales -/
section

namespace GoldbachTypeII13

noncomputable section

theorem weil_vaughan_near_scales {n m a s g : ℕ} {P X : ℝ}
    (n1 : 1 ≤ n) (m0 : 0 < m)
    (pLo : (n : ℝ)^(535/1024-1/24 : ℝ) ≤ P)
    (xLo : (n : ℝ)^(1/128 : ℝ) ≤ X) (xHi : X ≤ Real.sqrt P)
    (aTop : (a : ℝ) ≤ 2*X) (sTop : (s : ℝ) ≤ P/X)
    (mLo : (n : ℝ)^(2/5 : ℝ) ≤ (m : ℝ)) (mHi : (m : ℝ) ≤ (n : ℝ)^(3916/8192 : ℝ))
    (gTop : (g : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ)) :
    let q := min s m
    (((s/m : ℕ) : ℝ)+1)*
      ((q : ℝ)*Real.sqrt a+(a : ℝ)*Real.sqrt q*Real.sqrt (Real.sqrt m*Real.sqrt g)) ≤
      8*P*(n : ℝ)^(-(1/2048) : ℝ) := by
  dsimp only
  let N := (n : ℝ)
  let M := (m : ℝ)
  let A := (a : ℝ)
  let S := (s : ℝ)
  let G := (g : ℝ)
  let Q : ℕ := min s m
  let B := Real.sqrt (Real.sqrt M*Real.sqrt G)
  let K := N^(-(1/2048) : ℝ)
  let C := ((s/m : ℕ) : ℝ)+1
  have N1 : 1 ≤ N := by unfold N; exact_mod_cast n1
  have N0 := zero_lt_one.trans_le N1
  have X0 : 0 < X := (Real.rpow_pos_of_pos N0 _).trans_le xLo
  have P0 : 0 < P := (Real.rpow_pos_of_pos N0 _).trans_le pLo
  have M0 : 0 < M := by unfold M; exact_mod_cast m0
  have A0 : 0 ≤ A := by unfold A; positivity
  have S0 : 0 ≤ S := by unfold S; positivity
  have G0 : 0 ≤ G := by unfold G; positivity
  have B0 : 0 ≤ B := Real.sqrt_nonneg _
  have K0 : 0 ≤ K := Real.rpow_nonneg N0.le _
  have rpowPow (t x : ℝ) : (N^t)^x=N^(t*x) := (Real.rpow_mul N0.le t x).symm
  have sqrtPow (t : ℝ) : Real.sqrt (N^t) = N^(t/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul N0.le]
    congr 1
    ring
  have quarter {x : ℝ} (x0 : 0 ≤ x) : Real.sqrt (Real.sqrt x)=x^(1/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul x0]
    norm_num
  have Bval : B=M^(1/4 : ℝ)*G^(1/4 : ℝ) := by
    unfold B
    rw [Real.sqrt_mul (Real.sqrt_nonneg M),quarter M0.le,quarter G0]
  have gCap : G^(1/4 : ℝ) ≤ N^(1/8192 : ℝ) := by
    calc
      _ ≤ (N^(1/2048 : ℝ))^(1/4 : ℝ) := Real.rpow_le_rpow G0 gTop (by norm_num)
      _ = _ := by rw [rpowPow]; norm_num
  have invX : (Real.sqrt X)⁻¹ ≤ K := by
    have low : N^(1/256 : ℝ) ≤ Real.sqrt X := by
      calc
        _ = Real.sqrt (N^(1/128 : ℝ)) := by rw [sqrtPow]; norm_num
        _ ≤ _ := Real.sqrt_le_sqrt xLo
    calc
      _ ≤ (N^(1/256 : ℝ))⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos N0 _) low
      _ = N^(-(1/256) : ℝ) := (Real.rpow_neg N0.le _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le N1 (by norm_num)
  have sqrtA : Real.sqrt A ≤ 2*Real.sqrt X := by
    calc
      _ ≤ Real.sqrt (2*X) := Real.sqrt_le_sqrt aTop
      _ = Real.sqrt 2*Real.sqrt X := Real.sqrt_mul (by norm_num) _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr (by norm_num))) (Real.sqrt_nonneg _)
  have diag : S*Real.sqrt A ≤ 2*P*K := by
    calc
      _ ≤ (P/X)*(2*Real.sqrt X) := mul_le_mul sTop sqrtA (Real.sqrt_nonneg _) (by positivity)
      _ = 2*P*(Real.sqrt X)⁻¹ := by
        have h := Real.sq_sqrt X0.le
        have pos := Real.sqrt_pos.2 X0
        field_simp [X0.ne',pos.ne']
        exact h
      _ ≤ _ := mul_le_mul_of_nonneg_left invX (by positivity)
  have mPow : M^(1/4 : ℝ) ≤ N^((3916/8192)*(1/4) : ℝ) :=
    (Real.rpow_le_rpow M0.le mHi (by norm_num)).trans_eq (rpowPow _ _)
  have pPow : P^(-(1/4) : ℝ) ≤ N^((535/1024-1/24)*(-(1/4)) : ℝ) :=
    (Real.rpow_le_rpow_of_nonpos (by positivity) pLo (by norm_num)).trans_eq (rpowPow _ _)
  have factorSmall : P^(-(1/4) : ℝ)*M^(1/4 : ℝ)*G^(1/4 : ℝ) ≤ K := by
    calc
      _ ≤ N^((535/1024-1/24)*(-(1/4)) : ℝ)*N^((3916/8192)*(1/4) : ℝ)*N^(1/8192 : ℝ) := by gcongr
      _ ≤ _ := by
        rw [← Real.rpow_add N0,← Real.rpow_add N0]
        exact Real.rpow_le_rpow_of_exponent_le N1 (by norm_num)
  have small : A*Real.sqrt S*B ≤ 2*P*K := by
    have rootX : Real.sqrt X ≤ P^(1/4 : ℝ) := (Real.sqrt_le_sqrt xHi).trans_eq (quarter P0.le)
    have rpos := Real.sqrt_pos.2 X0
    have rootProd : X*Real.sqrt (P/X)=Real.sqrt X*Real.sqrt P := by
      rw [Real.sqrt_div P0.le]
      field_simp [rpos.ne']
      exact (Real.sq_sqrt X0.le).symm
    calc
      _ ≤ (2*X)*Real.sqrt (P/X)*B := by gcongr
      _ = 2*Real.sqrt X*Real.sqrt P*B := by
        calc
          _ = 2*(X*Real.sqrt (P/X))*B := by ring
          _ = _ := by rw [rootProd]; ring
      _ ≤ 2*P^(1/4 : ℝ)*Real.sqrt P*B := by gcongr
      _ = (2*P)*(P^(-(1/4) : ℝ)*M^(1/4 : ℝ)*G^(1/4 : ℝ)) := by
        have p : P^(1/4 : ℝ)*Real.sqrt P = P*P^(-(1/4) : ℝ) := by
          rw [Real.sqrt_eq_rpow,← Real.rpow_add P0]
          conv_rhs => lhs; rw [← Real.rpow_one P]
          rw [← Real.rpow_add P0]
          congr 1 <;> norm_num
        rw [Bval]
        calc
          _ = 2*(P^(1/4 : ℝ)*Real.sqrt P)*(M^(1/4 : ℝ)*G^(1/4 : ℝ)) := by ring
          _ = _ := by rw [p]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left factorSmall (by positivity)
  have factorLarge : M^(-(1/4) : ℝ)*G^(1/4 : ℝ) ≤ K := by
    have mp : M^(-(1/4) : ℝ) ≤ N^(-(1/10) : ℝ) := by
      calc
        _ ≤ (N^(2/5 : ℝ))^(-(1/4) : ℝ) := Real.rpow_le_rpow_of_nonpos (by positivity) mLo (by norm_num)
        _ = _ := by rw [rpowPow]; norm_num
    calc
      _ ≤ N^(-(1/10) : ℝ)*N^(1/8192 : ℝ) := mul_le_mul mp gCap (by positivity) (by positivity)
      _ ≤ _ := by rw [← Real.rpow_add N0]; exact Real.rpow_le_rpow_of_exponent_le N1 (by norm_num)
  have large : (S/M)*A*Real.sqrt M*B ≤ 2*P*K := by
    have sa : S*A ≤ 2*P := by
      calc
        _ ≤ (P/X)*(2*X) := mul_le_mul sTop aTop A0 (by positivity)
        _ = _ := by field_simp [X0.ne'] <;> ring
    have mp : Real.sqrt M*M^(1/4 : ℝ)=M*M^(-(1/4) : ℝ) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_add M0]
      conv_rhs => lhs; rw [← Real.rpow_one M]
      rw [← Real.rpow_add M0]
      congr 1 <;> norm_num
    calc
      _ = (S*A)*(M^(-(1/4) : ℝ)*G^(1/4 : ℝ)) := by
        rw [Bval]
        calc
          _ = (S*A)/M*(Real.sqrt M*M^(1/4 : ℝ))*G^(1/4 : ℝ) := by ring
          _ = _ := by rw [mp]; field_simp [M0.ne'] <;> ring
      _ ≤ _ := mul_le_mul sa factorLarge (by positivity) (by positivity)
  have coeff : C ≤ S/M+1 := add_le_add Nat.cast_div_le (le_refl _)
  change C*((Q : ℝ)*Real.sqrt A+A*Real.sqrt Q*B) ≤ 8*P*K
  by_cases h : s ≤ m
  · have Qval : Q=s := min_eq_left h
    have le : S/M ≤ 1 := (div_le_iff₀ M0).mpr (by rw [one_mul]; unfold S M; exact_mod_cast h)
    have cap : C ≤ 2 := coeff.trans (by linarith)
    rw [Qval]
    calc
      _ ≤ 2*(S*Real.sqrt A+A*Real.sqrt S*B) := mul_le_mul_of_nonneg_right cap (by positivity)
      _ ≤ _ := (mul_le_mul_of_nonneg_left (add_le_add diag small) (by norm_num)).trans_eq (by ring)
  · have v : m ≤ s := (Nat.lt_of_not_ge h).le
    have Qval : Q=m := min_eq_right v
    have le : 1 ≤ S/M := (le_div_iff₀ M0).mpr (by rw [one_mul]; unfold S M; exact_mod_cast v)
    have cap : C ≤ 2*(S/M) := coeff.trans (by linarith)
    rw [Qval]
    calc
      _ ≤ 2*(S/M)*(M*Real.sqrt A+A*Real.sqrt M*B) := mul_le_mul_of_nonneg_right cap (by positivity)
      _ = 2*(S*Real.sqrt A+(S/M)*A*Real.sqrt M*B) := by field_simp [M0.ne'] <;> ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (add_le_add diag large) (by norm_num)).trans_eq (by ring)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_vaughan_type_two_box -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical

noncomputable section

theorem norm_inverse_ramp_vaughan_type_two_box {n m A S : ℕ} [NeZero m] (c : ZMod m)
    (I : Finset ℕ) (base : I ⊆ Icc 1 A) (cop : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {T L P X : ℝ} (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (leftWeights : ∀ i ∈ I, ‖α i‖ ≤ T)
    (rightWeights : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T*L)
    (tau : (m.divisors.card : ℝ) ≤ T) (log : 1+Real.log m ≤ L)
    (s : ℕ → ZMod m) (t : ℤ → ZMod m) (z : ℕ → ℤ → ℤ)
    (phase : ∀ i j, (z i j : ZMod m) = c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹-s i-t j)
    (n1 : 1 ≤ n) (pLo : (n : ℝ)^(535/1024-1/24 : ℝ) ≤ P)
    (xLo : (n : ℝ)^(1/128 : ℝ) ≤ X) (xHi : X ≤ Real.sqrt P)
    (aCap : (A : ℝ) ≤ 2*X) (sCap : (S : ℝ) ≤ P/X)
    (mLo : (n : ℝ)^(2/5 : ℝ) ≤ (m : ℝ)) (mHi : (m : ℝ) ≤ (n : ℝ)^(3916/8192 : ℝ))
    (gCap : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ)) :
    ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun i j => (centeredInverseRamp m (z i j-1) : ℂ))‖ ≤
      24*T^4*L^3*P*(n : ℝ)^(-(1/2048) : ℝ) := by
  let Q : ℕ := min S m
  let K := ((Q : ℝ)*Real.sqrt A+
    (A : ℝ)*Real.sqrt Q*Real.sqrt (Real.sqrt m*Real.sqrt (m.gcd c.val)))
  let C := ((S/m : ℕ) : ℝ)+1
  have W0 : 0 ≤ 3*T^4*L^3 := by
    have := zero_le_one.trans T1
    have := zero_le_one.trans L1
    positivity
  calc
    _ ≤ C*(3*T^4*L^3*K) := norm_gated_inverse_ramp_le_weil_periods c I base cop α β lo hi
      T1 L1 leftWeights rightWeights tau log s t z phase
    _ = 3*T^4*L^3*(C*K) := by ring
    _ ≤ 3*T^4*L^3*(8*P*(n : ℝ)^(-(1/2048) : ℝ)) := mul_le_mul_of_nonneg_left
      (weil_vaughan_near_scales n1 (NeZero.pos m) pLo xLo xHi aCap sCap mLo mHi gCap) W0
    _ = _ := by ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_vaughan_type_two_box_bridge -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open scoped Classical

noncomputable section

def inverseTypeTwoBoxLeft (m hi C X : ℕ) : Finset ℕ :=
  (Ico X (2*X)).filter fun a => C < a ∧ a ≤ hi ∧ a.Coprime m

def inverseTypeTwoBoxLower (lo C : ℕ) (strict : Bool) (a : ℕ) : ℤ :=
  (max (lo/a) (max C (if strict then a else a-1)) : ℕ)

def inverseTypeTwoBoxPhase {m : ℕ} (c t : ZMod m) (a : ℕ) (j : ℤ) : ℤ :=
  ((c*(a : ZMod m)⁻¹*(j : ZMod m)⁻¹-t).val : ℕ)

theorem inverse_type_two_box_phase_cast {m : ℕ} [NeZero m] (c t : ZMod m) (a : ℕ) (j : ℤ) :
    (inverseTypeTwoBoxPhase c t a j : ZMod m)=c*(a : ZMod m)⁻¹*(j : ZMod m)⁻¹-t := by
  unfold inverseTypeTwoBoxPhase
  rw [Int.cast_natCast,ZMod.natCast_zmod_val]

def inverseTypeTwoBox {m : ℕ} (c t : ZMod m) (lo hi C X : ℕ) (strict : Bool)
    (a b : ArithmeticFunction ℝ) : ℂ :=
  gatedBilinearSum (inverseTypeTwoBoxLeft m hi C X) (intIntervalModUnits m 0 (hi/X : ℕ))
    (fun x => (a x : ℂ)) (fun j => (b j.toNat : ℂ)) (inverseTypeTwoBoxLower lo C strict) (fun x => (hi/x : ℕ))
    (fun x j => (centeredInverseRamp m (inverseTypeTwoBoxPhase c t x j-1) : ℂ))

def inverseTypeTwoBoxItems (m lo hi C X : ℕ) (strict : Bool) : Finset (ℕ × ℕ) :=
  (coprimeProductItems m lo hi).filter fun x =>
    X ≤ x.1 ∧ x.1 < 2*X ∧ C < x.1 ∧ C < x.2 ∧ (if strict then x.1 < x.2 else x.1 ≤ x.2)

private theorem lower_orientation_iff {a b : ℕ} (a0 : 0 < a) (strict : Bool) :
    (if strict then a else a-1) < b ↔ (if strict then a < b else a ≤ b) := by
  cases strict
  · simp only [Bool.false_eq_true,if_false]
    omega
  · simp

set_option maxHeartbeats 1600000 in
theorem inverse_type_two_box_eq_selected {m lo hi C X : ℕ} [NeZero m]
    (c t : ZMod m) (X0 : 0 < X) (strict : Bool) (a b : ArithmeticFunction ℝ) :
    inverseTypeTwoBox c t lo hi C X strict a b =
      ∑ x ∈ inverseTypeTwoBoxItems m lo hi C X strict,
        (a x.1 : ℂ)*(b x.2 : ℂ)*(inverseRampNat c t (x.1*x.2) : ℂ) := by
  let I := inverseTypeTwoBoxLeft m hi C X
  let J := intIntervalModUnits m 0 (hi/X : ℕ)
  let ok (u : ℕ) (j : ℤ) := inverseTypeTwoBoxLower lo C strict u < j ∧ j ≤ ((hi/u : ℕ) : ℤ)
  let P := (J ×ˢ I).filter fun x => ok x.2 x.1
  let liftPoint (x : ℤ × ℕ) : ℕ × ℕ := (x.2,x.1.toNat)
  let F (u : ℕ) (j : ℤ) := (centeredInverseRamp m (inverseTypeTwoBoxPhase c t u j-1) : ℂ)
  let w (x : ℤ × ℕ) := (a x.2 : ℂ)*(b x.1.toNat : ℂ)*F x.2 x.1
  let value (x : ℕ × ℕ) := (a x.1 : ℂ)*(b x.2 : ℂ)*(inverseRampNat c t (x.1*x.2) : ℂ)
  have infoI (u : ℕ) (hu : u ∈ I) : X ≤ u ∧ u < 2*X ∧ C < u ∧ u ≤ hi ∧ u.Coprime m := by
    obtain ⟨rng,cut,up,cp⟩ := mem_filter.mp hu
    exact ⟨(mem_Ico.mp rng).1,(mem_Ico.mp rng).2,cut,up,cp⟩
  have infoJ (j : ℤ) (hj : j ∈ J) : j ∈ Ioc 0 ((hi/X : ℕ) : ℤ) ∧ IsUnit (j : ZMod m) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hj
  have castJ (j : ℤ) (jr : 0 ≤ j) : (j.toNat : ZMod m) = (j : ZMod m) := by
    simpa only [Int.cast_natCast] using congrArg (fun p : ℤ => (p : ZMod m)) (Int.toNat_of_nonneg jr)
  have copJ (j : ℤ) (hj : j ∈ J) : j.toNat.Coprime m := by
    apply (ZMod.isUnit_iff_coprime _ _).mp
    rw [castJ j (mem_Ioc.mp (infoJ j hj).1).1.le]
    exact (infoJ j hj).2
  have okNat (u : ℕ) (u0 : 0 < u) (j : ℤ) (j0 : 0 ≤ j) :
      ok u j ↔ lo < u*j.toNat ∧ u*j.toNat ≤ hi ∧ C < j.toNat ∧
        (if strict then u < j.toNat else u ≤ j.toNat) := by
    unfold ok inverseTypeTwoBoxLower
    rw [← Int.toNat_of_nonneg j0]
    simp only [Int.ofNat_lt,Int.ofNat_le,Int.toNat_natCast,max_lt_iff,
      Nat.div_lt_iff_lt_mul u0,Nat.le_div_iff_mul_le u0,Nat.mul_comm j.toNat u,
      lower_orientation_iff u0 strict]
    tauto
  have liftMem (x : ℤ × ℕ) (hx : x ∈ P) : liftPoint x ∈ inverseTypeTwoBoxItems m lo hi C X strict := by
    obtain ⟨hj,hu⟩ := mem_product.mp (mem_filter.mp hx).1
    obtain ⟨xl,xr,xC,xHi,xcp⟩ := infoI _ hu
    have j0 := (mem_Ioc.mp (infoJ _ hj).1).1
    have jpos : 0 < x.1.toNat := by omega
    obtain ⟨l,r,short,orient⟩ := (okNat _ (X0.trans_le xl) _ j0.le).mp (mem_filter.mp hx).2
    have jHi : x.1.toNat ≤ hi := by
      have b := (mem_Ioc.mp (infoJ _ hj).1).2
      have h : x.1.toNat ≤ hi/X := by simpa only [Int.toNat_natCast] using Int.toNat_le_toNat b
      exact h.trans (Nat.div_le_self ..)
    have base : liftPoint x ∈ coprimeProductItems m lo hi := mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨X0.trans_le xl,xHi⟩,mem_Icc.mpr ⟨jpos,jHi⟩⟩,
        l,r,Nat.coprime_mul_iff_left.mpr ⟨xcp,copJ _ hj⟩⟩
    exact mem_filter.mpr ⟨base,xl,xr,xC,short,orient⟩
  have liftSurj (y : ℕ × ℕ) (hy : y ∈ inverseTypeTwoBoxItems m lo hi C X strict) :
      ∃ x ∈ P, liftPoint x = y := by
    obtain ⟨base,l,r,shortA,shortB,orient⟩ := mem_filter.mp hy
    obtain ⟨range,prodlo,prodhi,cop⟩ := mem_filter.mp base
    obtain ⟨aR,bR⟩ := mem_product.mp range
    obtain ⟨ac,bc⟩ := Nat.coprime_mul_iff_left.mp cop
    have su : y.1 ∈ I := mem_filter.mpr ⟨mem_Ico.mpr ⟨l,r⟩,shortA,(mem_Icc.mp aR).2,ac⟩
    have bBound : y.2 ≤ hi/X := (Nat.le_div_iff_mul_le X0).mpr
      (by simpa only [Nat.mul_comm y.2 X] using (Nat.mul_le_mul_right y.2 l).trans prodhi)
    have jp : (y.2 : ℤ) ∈ J := by
      have f : (y.2 : ℤ) ∈ Ioc (0 : ℤ) ((hi/X : ℕ) : ℤ) ∧ IsUnit ((y.2 : ℤ) : ZMod m) := by
        refine ⟨mem_Ioc.mpr ⟨by exact_mod_cast (mem_Icc.mp bR).1,by exact_mod_cast bBound⟩,?_⟩
        rw [Int.cast_natCast]
        exact (ZMod.isUnit_iff_coprime _ _).mpr bc
      simpa only [J,intIntervalModUnits,mem_filter] using f
    have flag : ok y.1 (y.2 : ℤ) := (okNat _ (X0.trans_le l) _ (by positivity)).mpr (by
      simpa only [Int.toNat_natCast] using (show _ from And.intro prodlo (And.intro prodhi (And.intro shortB orient))))
    exact ⟨((y.2 : ℤ),y.1),mem_filter.mpr ⟨mem_product.mpr ⟨jp,su⟩,flag⟩,
      Prod.ext rfl (Int.toNat_natCast _)⟩
  have eval (x : ℤ × ℕ) (hx : x ∈ P) : w x=value (liftPoint x) := by
    obtain ⟨hj,hu⟩ := mem_product.mp (mem_filter.mp hx).1
    unfold w value F liftPoint
    rw [inverse_ramp_nat_mul_right c t (infoI _ hu).2.2.2.2 (copJ _ hj)]
    unfold inverseTypeTwoBoxPhase inverseRampNat
    rw [castJ _ (mem_Ioc.mp (infoJ _ hj).1).1.le,mul_assoc]
  have expand : inverseTypeTwoBox c t lo hi C X strict a b=∑ x ∈ P, w x := by
    change gatedBilinearSum I J (fun x => (a x : ℂ)) (fun j => (b j.toNat : ℂ))
      (inverseTypeTwoBoxLower lo C strict) (fun x => (hi/x : ℕ)) F = _
    rw [gated_bilinear_sum_eq_pair_sum]
    unfold P
    rw [sum_filter,sum_product] <;> rfl
  rw [expand]
  refine sum_bij (fun x _ => liftPoint x) liftMem ?_ ?_ eval
  swap
  · intro y hy
    obtain ⟨x,hx,eq⟩ := liftSurj y hy
    exact ⟨x,hx,eq⟩
  intro x hx y hy eq
  have fst : x.2=y.2 := congrArg Prod.fst eq
  have snd : x.1.toNat=y.1.toNat := congrArg Prod.snd eq
  have pos (z : ℤ × ℕ) (hz : z ∈ P) : 0 ≤ z.1 :=
    (mem_Ioc.mp (infoJ _ (mem_product.mp (mem_filter.mp hz).1).1).1).1.le
  exact Prod.ext (by rw [← Int.toNat_of_nonneg (pos x hx),← Int.toNat_of_nonneg (pos y hy),snd]) fst

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_vaughan_type_two_dyadic -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def inverseTypeTwoOrientedItems (m lo hi C : ℕ) (strict : Bool) : Finset (ℕ × ℕ) :=
  (coprimeProductItems m lo hi).filter fun x =>
    C < x.1 ∧ C < x.2 ∧ (if strict then x.1 < x.2 else x.1 ≤ x.2)

def inverseTypeTwoDyadicIndices (n hi : ℕ) : Finset ℕ :=
  (Icc 0 (Nat.log 2 hi)).filter fun k =>
    (n : ℝ)^(1/128 : ℝ) ≤ ((2^k : ℕ) : ℝ) ∧ ((2^k : ℕ) : ℝ) ≤ Real.sqrt hi

theorem norm_inverse_type_two_box_le {n m lo hi C X : ℕ} [NeZero m] (c t : ZMod m)
    (strict : Bool) (a b : ArithmeticFunction ℝ) (n1 : 1 ≤ n) (mN : m ≤ n)
    (pLo : (n : ℝ)^(535/1024-1/24 : ℝ) ≤ (hi : ℝ))
    (xLo : (n : ℝ)^(1/128 : ℝ) ≤ (X : ℝ)) (xHi : (X : ℝ) ≤ Real.sqrt hi)
    (mLo : (n : ℝ)^(2/5 : ℝ) ≤ (m : ℝ)) (mHi : (m : ℝ) ≤ (n : ℝ)^(3916/8192 : ℝ))
    (gCap : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (tau : (m.divisors.card : ℝ) ≤ T)
    (aB : ∀ q≤hi, ‖(a q : ℂ)‖ ≤ T) (bB : ∀ q≤hi, ‖(b q : ℂ)‖ ≤ T) :
    ‖inverseTypeTwoBox c t lo hi C X strict a b‖ ≤
      24*T^4*logBudget n^3*(hi : ℝ)*(n : ℝ)^(-(1/2048) : ℝ) := by
  let I := inverseTypeTwoBoxLeft m hi C X
  let S := hi/X
  have T0 := zero_le_one.trans T1
  have L1 := one_le_logBudget n
  have top : I ⊆ Icc 1 (2*X) := by
    intro u hu
    have range := mem_Ico.mp (mem_filter.mp hu).1
    have X0 : 0 < X := by
      have h := (Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast n1) (1/128 : ℝ)).trans_le xLo
      exact_mod_cast h
    exact mem_Icc.mpr ⟨X0.trans_le range.1,range.2.le⟩
  have cop : ∀ i ∈ I, i.Coprime m := fun _ h => (mem_filter.mp h).2.2.2
  have alpha : ∀ u ∈ I, ‖(a u : ℂ)‖ ≤ T := fun u h => aB u (mem_filter.mp h).2.2.1
  have beta : ∀ j ∈ intIntervalModUnits m 0 S, ‖(b j.toNat : ℂ)‖ ≤ T*logBudget n := by
    intro j hj
    have h : j ∈ Ioc 0 (S : ℤ) ∧ IsUnit (j : ZMod m) := by
      simpa only [intIntervalModUnits,mem_filter] using hj
    have bound : j.toNat ≤ S := by simpa only [Int.toNat_natCast] using Int.toNat_le_toNat (mem_Ioc.mp h.1).2
    exact (bB j.toNat (bound.trans (Nat.div_le_self ..))).trans (le_mul_of_one_le_right T0 L1)
  have log : 1+Real.log (m : ℝ) ≤ logBudget n := by
    unfold logBudget
    have mR : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
    have mTop : (m : ℝ) ≤ n := by exact_mod_cast mN
    exact add_le_add (le_refl _) (Real.log_le_log mR (by linarith only [mTop]))
  exact norm_inverse_ramp_vaughan_type_two_box c I top cop (fun u => (a u : ℂ))
    (fun j => (b j.toNat : ℂ)) (inverseTypeTwoBoxLower lo C strict) (fun u => (hi/u : ℕ))
    T1 L1 alpha beta tau log (fun _ => 0) (fun _ => t) (inverseTypeTwoBoxPhase c t)
    (fun i j => by simpa only [sub_zero] using inverse_type_two_box_phase_cast c t i j)
    n1 pLo xLo xHi (by push_cast; exact le_rfl) Nat.cast_div_le mLo mHi gCap

private theorem dyadic_indices_for_type_two {n m lo hi : ℕ} {strict : Bool}
    (n1 : 1 ≤ n) (huge : (2 : ℝ) ≤ (n : ℝ)^(1/384 : ℝ))
    {x : ℕ × ℕ} (hx : x ∈ inverseTypeTwoOrientedItems m lo hi (vaughanShortCut n) strict) :
    Nat.log 2 x.1 ∈ inverseTypeTwoDyadicIndices n hi := by
  let k := Nat.log 2 x.1
  let X : ℕ := 2^k
  obtain ⟨base,cutA,cutB,ord⟩ := mem_filter.mp hx
  obtain ⟨domain,loP,hiP,cp⟩ := mem_filter.mp base
  have r := mem_Icc.mp (mem_product.mp domain).1
  have Xl : X ≤ x.1 := Nat.pow_log_le_self 2 (show 0 < x.1 from r.1).ne'
  have Xr : x.1 < 2*X := by
    unfold X k
    rw [mul_comm,← pow_succ]
    exact Nat.lt_pow_succ_log_self (by decide) _
  have kRange : k ≤ Nat.log 2 hi := Nat.log_mono_right r.2
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have n0 := zero_lt_one.trans_le nR
  have lower : (n : ℝ)^(1/128 : ℝ) ≤ (X : ℝ) := by
    apply (mul_le_mul_iff_left₀ (show (0 : ℝ)<2 by norm_num)).mp
    calc
      _ ≤ (n : ℝ)^(1/128 : ℝ)*(n : ℝ)^(1/384 : ℝ) :=
        mul_le_mul_of_nonneg_left huge (by positivity)
      _ = (n : ℝ)^(1/96 : ℝ) := by rw [← Real.rpow_add n0]; norm_num
      _ ≤ (vaughanShortCut n : ℝ)+1 := (Nat.lt_floor_add_one _).le
      _ ≤ (x.1 : ℝ) := by exact_mod_cast Nat.succ_le_of_lt cutA
      _ ≤ (X : ℝ)*2 := by
        rw [mul_comm]
        exact_mod_cast Xr.le
  have order : x.1 ≤ x.2 := by
    cases strict
    · exact ord
    · exact (show x.1 < x.2 from by simpa using ord).le
  have limit : X^2 ≤ hi := by
    rw [pow_two]
    exact (Nat.mul_le_mul Xl (Xl.trans order)).trans hiP
  have upper : (X : ℝ) ≤ Real.sqrt hi :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr (by exact_mod_cast limit)
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _,kRange⟩,lower,upper⟩

set_option maxHeartbeats 1400000 in
theorem inverse_type_two_oriented_eq_dyadic {n m lo hi : ℕ} [NeZero m] (c t : ZMod m)
    (strict : Bool) (a b : ArithmeticFunction ℝ) (n1 : 1 ≤ n)
    (huge : (2 : ℝ) ≤ (n : ℝ)^(1/384 : ℝ)) :
    (∑ x ∈ inverseTypeTwoOrientedItems m lo hi (vaughanShortCut n) strict,
        (a x.1 : ℂ)*(b x.2 : ℂ)*(inverseRampNat c t (x.1*x.2) : ℂ)) =
      ∑ k ∈ inverseTypeTwoDyadicIndices n hi,
        inverseTypeTwoBox c t lo hi (vaughanShortCut n) (2^k) strict a b := by
  let J := inverseTypeTwoOrientedItems m lo hi (vaughanShortCut n) strict
  let K := inverseTypeTwoDyadicIndices n hi
  let k (x : ℕ × ℕ) := Nat.log 2 x.1
  let w (x : ℕ × ℕ) := (a x.1 : ℂ)*(b x.2 : ℂ)*(inverseRampNat c t (x.1*x.2) : ℂ)
  have image (x : ℕ × ℕ) (hx : x ∈ J) : k x ∈ K := dyadic_indices_for_type_two n1 huge hx
  change ∑ x ∈ J,w x = ∑ j ∈ K, inverseTypeTwoBox c t lo hi (vaughanShortCut n) (2^j) strict a b
  rw [← sum_fiberwise_of_maps_to image w]
  refine sum_congr rfl fun j _ => ?_
  rw [inverse_type_two_box_eq_selected c t (by positivity : (0 : ℕ) < 2^j) strict a b]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨base,cutA,cutB,ord⟩ := mem_filter.mp (mem_filter.mp hx).1
    have dom := mem_product.mp (mem_filter.mp base).1
    have p : 0 < x.1 := (mem_Icc.mp dom.1).1
    have eq : Nat.log 2 x.1=j := (mem_filter.mp hx).2
    have l := Nat.pow_log_le_self 2 p.ne'
    have r := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) x.1
    rw [eq] at l r
    rw [pow_succ,mul_comm] at r
    exact mem_filter.mpr ⟨base,l,r,cutA,cutB,ord⟩
  · intro hx
    obtain ⟨base,l,r,cutA,cutB,ord⟩ := mem_filter.mp hx
    have h : x.1 < 2^(j+1) := by rw [pow_succ,mul_comm]; exact r
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨base,cutA,cutB,ord⟩,Nat.log_eq_of_pow_le_of_lt_pow l h⟩

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_vaughan_type_two_aggregate -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def inverseTypeTwoOrientedSum {m : ℕ} (c t : ZMod m) (lo hi C : ℕ) (strict : Bool)
    (a b : ArithmeticFunction ℝ) : ℂ :=
  ∑ x ∈ inverseTypeTwoOrientedItems m lo hi C strict,
    (a x.1 : ℂ)*(b x.2 : ℂ)*(inverseRampNat c t (x.1*x.2) : ℂ)

theorem inverse_type_two_split_oriented {m lo hi C : ℕ} (c t : ZMod m)
    (a b : ArithmeticFunction ℝ)
    (aboveA : ∀ x ≤ C, a x=0) (aboveB : ∀ x ≤ C, b x=0) :
    coprimeWeightedProductWindow m lo hi a b (fun p => (inverseRampNat c t p : ℂ)) =
      inverseTypeTwoOrientedSum c t lo hi C false a b + inverseTypeTwoOrientedSum c t lo hi C true b a := by
  let A := coprimeProductItems m lo hi
  let B := A.filter (fun x => C < x.1 ∧ C < x.2)
  let w (x : ℕ × ℕ) := (a x.1 : ℂ)*(b x.2 : ℂ)*(inverseRampNat c t (x.1*x.2) : ℂ)
  have cut : ∑ x ∈ B,w x = ∑ x ∈ A,w x := by
    refine sum_subset (filter_subset _ _) fun x hx outside => ?_
    have bad : ¬(C < x.1 ∧ C < x.2) := fun h => outside (mem_filter.mpr ⟨hx,h⟩)
    by_cases h : C < x.1
    · have e : x.2 ≤ C := le_of_not_gt (fun h₂ => bad ⟨h,h₂⟩)
      simp [w,aboveB _ e]
    · simp [w,aboveA _ (le_of_not_gt h)]
  have first : B.filter (fun x => x.1≤x.2) = inverseTypeTwoOrientedItems m lo hi C false := by
    ext x
    simp only [B,A,inverseTypeTwoOrientedItems,mem_filter,Bool.false_eq_true,if_false]
    tauto
  have swapped :
      (∑ x ∈ B.filter (fun x => ¬x.1≤x.2),w x) =
        inverseTypeTwoOrientedSum c t lo hi C true b a := by
    unfold inverseTypeTwoOrientedSum
    have mem {x : ℕ × ℕ} :
        x ∈ B.filter (fun x => ¬x.1≤x.2) ↔ x.swap ∈ inverseTypeTwoOrientedItems m lo hi C true := by
      simp only [B,A,inverseTypeTwoOrientedItems,coprimeProductItems,mem_filter,mem_product,
        not_le,Prod.fst_swap,Prod.snd_swap,eq_self,if_true]
      rw [Nat.mul_comm x.2 x.1]
      tauto
    refine sum_bij (fun x _ => x.swap) (fun _ h => mem.mp h) ?_ ?_ ?_
    · intro x hx y hy eq
      exact Prod.swap_injective eq
    · intro x hx
      exact ⟨x.swap,mem.mpr (by simpa only [Prod.swap_swap] using hx),Prod.swap_swap x⟩
    · intro x _
      unfold w
      rw [Prod.fst_swap,Prod.snd_swap,Nat.mul_comm x.2 x.1,mul_comm (b x.2 : ℂ) (a x.1 : ℂ)]
  unfold coprimeWeightedProductWindow
  change ∑ x ∈ A,w x = _
  rw [← cut,← sum_filter_add_sum_filter_not B (fun x => x.1≤x.2) w,first,swapped]
  rfl

theorem norm_inverse_type_two_oriented_sum_le {n m lo hi : ℕ} [NeZero m] (c t : ZMod m)
    (strict : Bool) (a b : ArithmeticFunction ℝ) (n2 : 2 ≤ n) (hin : hi ≤ n) (mN : m ≤ n)
    (huge : (2 : ℝ) ≤ (n : ℝ)^(1/384 : ℝ))
    (pLo : (n : ℝ)^(535/1024-1/24 : ℝ) ≤ (hi : ℝ))
    (mLo : (n : ℝ)^(2/5 : ℝ) ≤ (m : ℝ)) (mHi : (m : ℝ) ≤ (n : ℝ)^(3916/8192 : ℝ))
    (gCap : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (tau : (m.divisors.card : ℝ) ≤ T)
    (aB : ∀ q≤hi, ‖(a q : ℂ)‖ ≤ T) (bB : ∀ q≤hi, ‖(b q : ℂ)‖ ≤ T) :
    ‖inverseTypeTwoOrientedSum c t lo hi (vaughanShortCut n) strict a b‖ ≤
      120*T^4*logBudget n^4*(hi : ℝ)*(n : ℝ)^(-(1/2048) : ℝ) := by
  let K := inverseTypeTwoDyadicIndices n hi
  let L := logBudget n
  let B := 24*T^4*L^3*(hi : ℝ)*(n : ℝ)^(-(1/2048) : ℝ)
  have n1 : 1 ≤ n := (by decide : 1 ≤ (2 : ℕ)).trans n2
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have B0 : 0 ≤ B := by unfold B; positivity
  have card : (#K : ℝ) ≤ 5*L := by
    have h : #K ≤ Nat.log 2 hi +1 := (card_filter_le _ _).trans (by simp [Nat.card_Icc])
    have hx : (#K : ℝ) ≤ (Nat.log 2 hi : ℝ)+1 := by exact_mod_cast h
    exact hx.trans (natLog_succ_le n2 hin)
  unfold inverseTypeTwoOrientedSum
  rw [inverse_type_two_oriented_eq_dyadic c t strict a b n1 huge]
  change ‖∑ k ∈ K, inverseTypeTwoBox c t lo hi (vaughanShortCut n) (2^k) strict a b‖ ≤ _
  calc
    _ ≤ ∑ k ∈ K, ‖inverseTypeTwoBox c t lo hi (vaughanShortCut n) (2^k) strict a b‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ K,B := by
      refine sum_le_sum fun k hk => ?_
      have scale := (mem_filter.mp hk).2
      exact norm_inverse_type_two_box_le c t strict a b n1 mN pLo scale.1 scale.2 mLo mHi gCap T1 tau aB bB
    _ = (#K : ℝ)*B := by rw [sum_const,nsmul_eq_mul]
    _ ≤ (5*L)*B := mul_le_mul_of_nonneg_right card B0
    _ = _ := by unfold B L; ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_vaughan_mangoldt -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4MoebiusGauss
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

theorem norm_inverse_ramp_mangoldt_near_le {n m lo hi : ℕ} [NeZero m] (c t : ZMod m)
    (n2 : 2 ≤ n) (hin : hi ≤ n) (mN : m ≤ n) (order : lo ≤ hi)
    (cut : vaughanShortCut n ≤ lo) (huge : (2 : ℝ) ≤ (n : ℝ)^(1/384 : ℝ))
    (pLo : (n : ℝ)^(535/1024-1/24 : ℝ) ≤ (hi : ℝ))
    (hiTop : (hi : ℝ) ≤ (n : ℝ)^(33/64 : ℝ))
    (mLo : (n : ℝ)^(2/5 : ℝ) ≤ (m : ℝ)) (mHi : (m : ℝ) ≤ (n : ℝ)^(3916/8192 : ℝ))
    (gCap : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (divs : ∀ b ≤ n, (b.divisors.card : ℝ) ≤ T) :
    ‖coprimeWeightedWindow m lo hi vonMangoldt (fun p => (inverseRampNat c t p : ℂ))‖ ≤
      258*T^4*logBudget n^8*(hi : ℝ)*(n : ℝ)^(-(1/2048) : ℝ) := by
  let P := vaughanShortCut n
  let M := (μ : ArithmeticFunction ℝ)
  let u := truncateArithmetic M P
  let v := truncateArithmetic vonMangoldt P
  let Z := (ζ : ArithmeticFunction ℝ)
  let a := M-u
  let b := (vonMangoldt-v)*Z
  let f (p : ℕ) := (inverseRampNat c t p : ℂ)
  let L := logBudget n
  let N := (n : ℝ)
  let W := T*L
  let H := (hi : ℝ)*N^(-(1/2048) : ℝ)
  have n1 : 1 ≤ n := (by decide : 1 ≤ (2 : ℕ)).trans n2
  have nR : 1 ≤ N := by unfold N; exact_mod_cast n1
  have n0 := zero_lt_one.trans_le nR
  have T0 := zero_le_one.trans T1
  have L1 := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have W1 : 1 ≤ W := one_le_mul_of_one_le_of_one_le T1 L1
  have H0 : 0 ≤ H := by unfold H; positivity
  have mTop : (m : ℝ) ≤ N^(1/2 : ℝ) :=
    mHi.trans (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have zNorm (j : ℕ) : ‖(Z j : ℂ)‖ ≤ 1 := by
    unfold Z
    rw [natCoe_apply,zeta_apply]
    split_ifs <;> norm_num
  have supA (j : ℕ) (hj : j ≤ P) : a j=0 := by
    change M j-(if j≤P then M j else 0)=0
    simp only [if_pos hj,sub_self]
  have supB (j : ℕ) (hj : j ≤ P) : b j=0 := by
    unfold b Z
    rw [coe_mul_zeta_apply]
    refine sum_eq_zero fun k hk => ?_
    obtain ⟨dvd,nonzero⟩ := Nat.mem_divisors.mp hk
    have lt : k ≤ P := (Nat.le_of_dvd (Nat.pos_of_ne_zero nonzero) dvd).trans hj
    change vonMangoldt k-(if k≤P then vonMangoldt k else 0)=0
    simp only [if_pos lt,sub_self]
  have aBound (j : ℕ) (_ : j ≤ hi) : ‖(a j : ℂ)‖ ≤ W := by
    by_cases small : j ≤ P
    · rw [supA j small,Complex.ofReal_zero,norm_zero]
      exact zero_le_one.trans W1
    · change ‖((M j-(if j≤P then M j else 0) : ℝ) : ℂ)‖ ≤ W
      rw [if_neg small,sub_zero]
      exact (norm_moebiusComplex_le_one j).trans W1
  have vBound (j : ℕ) (hj : j ≤ n) : ‖((vonMangoldt-v) j : ℂ)‖ ≤ L := by
    change ‖((vonMangoldt j-(if j≤P then vonMangoldt j else 0) : ℝ) : ℂ)‖ ≤ L
    by_cases small : j ≤ P
    · rw [if_pos small,sub_self,Complex.ofReal_zero,norm_zero]
      exact L0
    · rw [if_neg small,sub_zero,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
      exact vonMangoldt_le_log.trans (log_le_logBudget ((Nat.zero_le _).trans_lt (Nat.lt_of_not_ge small)) hj)
  have bBound (j : ℕ) (hj : j ≤ hi) : ‖(b j : ℂ)‖ ≤ W := by
    have h := norm_convolution_apply_le (hj.trans hin) (vonMangoldt-v) Z L0 zero_le_one
      (divs j (hj.trans hin)) vBound (fun k _ => zNorm k)
    simpa only [b,W,mul_one] using h
  have tau : (m.divisors.card : ℝ) ≤ W := (divs m mN).trans (le_mul_of_one_le_right T0 L1)
  have oriA := norm_inverse_type_two_oriented_sum_le c t (lo := lo) false a b n2 hin mN huge
    pLo mLo mHi gCap W1 tau aBound bBound
  have oriB := norm_inverse_type_two_oriented_sum_le c t (lo := lo) true b a n2 hin mN huge
    pLo mLo mHi gCap W1 tau bBound aBound
  have typeII : ‖coprimeWeightedProductWindow m lo hi a b f‖ ≤ 240*T^4*L^8*H := by
    rw [inverse_type_two_split_oriented c t a b supA supB]
    exact (norm_add_le _ _).trans ((add_le_add oriA oriB).trans_eq (by unfold W H L N; ring))
  have typeI :
      ‖coprimeWeightedProductWindow m lo hi u ArithmeticFunction.log f-
        coprimeWeightedProductWindow m lo hi (u*v) Z f‖ ≤ 18*T^3*L^3*N^(2/5 : ℝ) :=
    norm_inverse_vaughan_short_parts_le c t n1 hin mN order hiTop mLo mTop gCap T1 divs
  have comparison : N^(2/5 : ℝ) ≤ H := by
    calc
      _ = N^(2/5+1/2048 : ℝ)*N^(-(1/2048) : ℝ) := by rw [← Real.rpow_add n0]; congr 1 <;> norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le nR (by norm_num)).trans pLo) (by positivity)
  have larger : 18*T^3*L^3*N^(2/5 : ℝ) ≤ 18*T^4*L^8*H := by
    have pT : T^3 ≤ T^4 := pow_le_pow_right₀ T1 (by decide)
    have pL : L^3 ≤ L^8 := pow_le_pow_right₀ L1 (by decide)
    exact mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left pT (by norm_num)) pL (by positivity) (by positivity))
      comparison (by positivity) (by positivity)
  rw [coprime_weighted_vaughan_window_eq m lo hi P P cut f]
  calc
    _ ≤ 18*T^4*L^8*H+240*T^4*L^8*H :=
      (norm_add_le _ _).trans (add_le_add (typeI.trans larger) typeII)
    _ = _ := by unfold H L N; ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inverse_vaughan_prime -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def primeInverseRampWindow {m : ℕ} (n lo hi : ℕ) (c t : ZMod m) : ℂ :=
  ∑ p ∈ ((Ioc lo hi).filter (fun p => p.Coprime m)).filter (fun p => p.Prime ∧ ¬p ∣ n),
    (vonMangoldt p : ℂ)*(inverseRampNat c t p : ℂ)

theorem norm_mangoldt_sub_prime_inverse_ramp_le {n m lo hi : ℕ} [NeZero m] (c t : ZMod m)
    (n0 : 0 < n) (hin : hi ≤ n) :
    ‖coprimeWeightedWindow m lo hi vonMangoldt (fun p => (inverseRampNat c t p : ℂ)) -
      primeInverseRampWindow n lo hi c t‖ ≤
      logBudget n*((hi.sqrt : ℝ)*(Nat.log 2 hi : ℝ)+(n.divisors.card : ℝ)) := by
  let J := (Ioc lo hi).filter (fun p => p.Coprime m)
  let good (p : ℕ) := p.Prime ∧ ¬p ∣ n
  let bad := properPrimePowersUpTo hi ∪ n.divisors
  let K := J.filter (fun p => p ∈ bad)
  let F (p : ℕ) := (vonMangoldt p : ℂ)*(inverseRampNat c t p : ℂ)
  let w (p : ℕ) := if good p then 0 else F p
  have diff :
      coprimeWeightedWindow m lo hi vonMangoldt (fun p => (inverseRampNat c t p : ℂ)) -
      primeInverseRampWindow n lo hi c t = ∑ p ∈ J, w p := by
    change (∑ p ∈ J,F p)-(∑ p ∈ J.filter good,F p) = _
    rw [sum_filter (s := J) good,← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    by_cases h : good p <;> simp [w,h]
  have clip : (∑ p ∈ K,w p) = ∑ p ∈ J,w p := by
    apply sum_subset (filter_subset _ _)
    intro p hp hnot
    have miss : p ∉ bad := fun h => hnot (mem_filter.mpr ⟨hp,h⟩)
    have range := mem_Ioc.mp (mem_filter.mp hp).1
    have p0 := (Nat.zero_le _).trans_lt range.1
    have nD : ¬p∣n := fun h => miss (mem_union.mpr (Or.inr (Nat.mem_divisors.mpr ⟨h,n0.ne'⟩)))
    by_cases pr : p.Prime
    · exact if_pos (show good p from ⟨pr,nD⟩)
    · have non : ¬IsPrimePow p := fun h =>
        miss (mem_union.mpr (Or.inl (mem_filter.mpr ⟨mem_Icc.mpr ⟨p0,range.2⟩,pr,h⟩)))
      simp [w,good,pr,F,vonMangoldt_eq_zero_iff.mpr non]
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have W (p : ℕ) (hp : p ∈ K) : ‖w p‖ ≤ logBudget n := by
    have range := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1
    have p0 := (Nat.zero_le _).trans_lt range.1
    have vm : ‖(vonMangoldt p : ℂ)‖ ≤ logBudget n := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
      exact vonMangoldt_le_log.trans (log_le_logBudget p0 (range.2.trans hin))
    have ph : ‖(inverseRampNat c t p : ℂ)‖ ≤ 1 :=
      norm_centered_inverse_ramp_le_one (NeZero.pos m) _
    unfold w F
    split_ifs
    · simpa only [norm_zero] using L0
    · rw [norm_mul]
      simpa only [mul_one] using mul_le_mul vm ph (norm_nonneg _) L0
  have d : (#K : ℝ) ≤ (hi.sqrt : ℝ)*(Nat.log 2 hi : ℝ)+(n.divisors.card : ℝ) := by
    have subset : K ⊆ bad := fun _ h => (mem_filter.mp h).2
    have card := (card_le_card subset).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_proper_prime_powers_up_to_le hi) _))
    exact_mod_cast card
  rw [diff,← clip]
  calc
    _ ≤ ∑ p ∈ K, ‖w p‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ K,logBudget n := sum_le_sum W
    _ = (#K : ℝ)*logBudget n := by rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := (mul_le_mul_of_nonneg_right d L0).trans_eq (mul_comm _ _)

theorem norm_prime_inverse_ramp_near_le {n m lo hi : ℕ} [NeZero m] (c t : ZMod m)
    (n2 : 2 ≤ n) (hin : hi ≤ n) (mN : m ≤ n) (order : lo ≤ hi)
    (cut : vaughanShortCut n ≤ lo) (huge : (2 : ℝ) ≤ (n : ℝ)^(1/384 : ℝ))
    (pLo : (n : ℝ)^(535/1024-1/24 : ℝ) ≤ (hi : ℝ))
    (hiTop : (hi : ℝ) ≤ (n : ℝ)^(33/64 : ℝ))
    (mLo : (n : ℝ)^(2/5 : ℝ) ≤ (m : ℝ)) (mHi : (m : ℝ) ≤ (n : ℝ)^(3916/8192 : ℝ))
    (gCap : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (divs : ∀ q ≤ n, (q.divisors.card : ℝ) ≤ T) :
    ‖primeInverseRampWindow n lo hi c t‖ ≤
      264*T^4*logBudget n^8*(hi : ℝ)*(n : ℝ)^(-(1/2048) : ℝ) := by
  let N := (n : ℝ)
  let L := logBudget n
  let H := (hi : ℝ)*N^(-(1/2048) : ℝ)
  have n1 : 1 ≤ n := (by decide : 1 ≤ (2 : ℕ)).trans n2
  have nR : 1 ≤ N := by unfold N; exact_mod_cast n1
  have n0 := zero_lt_one.trans_le nR
  have L1 : 1 ≤ L := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have T0 := zero_le_one.trans T1
  have H1 : 1 ≤ H := by
    have weight : N^(1/2048 : ℝ) ≤ (hi : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le nR (by norm_num)).trans pLo
    calc
      _ = N^(1/2048 : ℝ)*N^(-(1/2048) : ℝ) := by rw [← Real.rpow_add n0,add_neg_cancel,Real.rpow_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_right weight (by positivity)
  have root : (hi.sqrt : ℝ) ≤ H := by
    calc
      _ ≤ Real.sqrt hi := (Real.le_sqrt (by positivity) (by positivity)).mpr (by
        rw [pow_two]
        exact_mod_cast Nat.sqrt_le hi)
      _ ≤ Real.sqrt (N^(33/64 : ℝ)) := Real.sqrt_le_sqrt hiTop
      _ = N^(33/128 : ℝ) := by rw [Real.sqrt_eq_rpow,← Real.rpow_mul n0.le]; norm_num
      _ = N^(33/128+1/2048 : ℝ)*N^(-(1/2048) : ℝ) := by
        rw [← Real.rpow_add n0]; congr 1 <;> norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le nR (by norm_num)).trans pLo) (by positivity)
  have log : (Nat.log 2 hi : ℝ) ≤ 5*L := by
    have h := natLog_succ_le n2 hin
    linarith only [h]
  have cutBound : L*((hi.sqrt : ℝ)*(Nat.log 2 hi : ℝ)+(n.divisors.card : ℝ)) ≤ 6*T^4*L^8*H := by
    have pL : L^2 ≤ L^8 := pow_le_pow_right₀ L1 (by decide)
    have pT : T ≤ T^4 := by simpa only [pow_one] using pow_le_pow_right₀ T1 (show 1 ≤ 4 by decide)
    calc
      _ ≤ L*(H*(5*L)+T) := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul root log (by positivity) (by positivity)) (divs n le_rfl)) L0
      _ ≤ L*((T*H)*(5*L)+(T*H)*L) := by
        have le : H ≤ T*H := le_mul_of_one_le_left (zero_le_one.trans H1) T1
        have tt : T ≤ (T*H)*L := (le_mul_of_one_le_right T0 H1).trans
          (le_mul_of_one_le_right (by positivity) L1)
        exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right le (by positivity)) tt) L0
      _ = 6*T*L^2*H := by ring
      _ ≤ _ := by gcongr
  have small := norm_inverse_ramp_mangoldt_near_le c t n2 hin mN order cut huge pLo
    hiTop mLo mHi gCap T1 divs
  have loss := (norm_mangoldt_sub_prime_inverse_ramp_le (lo := lo) c t n1 hin).trans cutBound
  let F := coprimeWeightedWindow m lo hi vonMangoldt (fun p => (inverseRampNat c t p : ℂ))
  let G := primeInverseRampWindow n lo hi c t
  change ‖G‖ ≤ _
  calc
    _ = ‖F-(F-G)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖F‖+‖F-G‖ := norm_sub_le _ _
    _ ≤ 258*T^4*L^8*H+6*T^4*L^8*H := add_le_add (by unfold F H L N; simpa [mul_assoc] using small) loss
    _ = _ := by unfold H L N; ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_small_short_window -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4MoebiusGauss
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def smallReverseWeilFactors (n u g : ℕ) : Finset ℕ :=
  (Icc 1 (min (cutoffU n) (reverseWeilShortCut n))).filter fun q =>
    g ∣ q ∧ (q/g).Coprime (u/g) ∧ q.gcd n ≤ sparseTargetDivisorCap n ∧ q.gcd n ≤ targetDivisorCap n

def smallReverseWeilPrimeLower (n lo q : ℕ) : ℕ := max (cutoffU n) (lo/q)

def smallReverseWeilPrimeUpper (n hi q : ℕ) : ℕ := min (min n (rightLargeCofactorCut n)) (hi/q)

def smallReverseWeilWindow (n u g lo hi : ℕ) : ℂ :=
  let m := u/g
  let c : ZMod m := (n/g : ℕ)
  ∑ q ∈ smallReverseWeilFactors n u g, -(μ q : ℂ)*
    primeInverseRampWindow n (smallReverseWeilPrimeLower n lo q) (smallReverseWeilPrimeUpper n hi q)
      (c*((q/g : ℕ) : ZMod m)⁻¹) 0

set_option maxHeartbeats 1400000 in
theorem norm_small_reverse_weil_window_le {n u g lo hi : ℕ}
    (n2 : 2 ≤ n) (u0 : 0 < u) (uN : u ≤ n) (uLo : ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u)
    (target : u.gcd n ≤ thinHighLeftDivisorCap n)
    (g0 : 0 < g) (gu : g ∣ u) (gn : g ∣ n) (gSmall : g ≤ thinHighGcdCap n)
    (loV : widerLowFarModulusCap n ≤ lo) (prod : hi*u ≤ weilNearProductCap n)
    (large : (2 : ℝ) ≤ (n : ℝ)^(1/384 : ℝ))
    (large₂ : (2 : ℝ) ≤ (n : ℝ)^(1/8192 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (divs : ∀ q ≤ n, (q.divisors.card : ℝ) ≤ T) :
    (u : ℝ)*‖smallReverseWeilWindow n u g lo hi‖ ≤
      528*T^4*logBudget n^9*(n : ℝ)^(8191/8192 : ℝ) := by
  let N := (n : ℝ)
  let L := logBudget n
  let m := u/g
  let c : ZMod m := (n/g : ℕ)
  let I := smallReverseWeilFactors n u g
  let B := 528*T^4*L^8*N^(8191/8192 : ℝ)
  let row (q : ℕ) := primeInverseRampWindow n (smallReverseWeilPrimeLower n lo q)
    (smallReverseWeilPrimeUpper n hi q) (c*((q/g : ℕ) : ZMod m)⁻¹) 0
  have n1 : 1 ≤ n := (by decide : 1 ≤ (2 : ℕ)).trans n2
  have N1 : 1 ≤ N := by unfold N; exact_mod_cast n1
  have N0 := zero_lt_one.trans_le N1
  have m0 : 0 < m := Nat.div_pos (Nat.le_of_dvd u0 gu) g0
  let _ : NeZero m := ⟨m0.ne'⟩
  have mg : m*g=u := Nat.div_mul_cancel gu
  have mgR : (m : ℝ)*(g : ℝ)=(u : ℝ) := by exact_mod_cast mg
  have uR : (0 : ℝ) < u := by exact_mod_cast u0
  have gR : (0 : ℝ) < g := by exact_mod_cast g0
  have mN : m ≤ n := (Nat.div_le_self _ _).trans uN
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have B0 : 0 ≤ B := by unfold B; positivity
  have gCap : (g : ℝ) ≤ N^(1/4096 : ℝ) :=
    (show (g : ℝ) ≤ thinHighGcdCap n by exact_mod_cast gSmall).trans (Nat.floor_le (by positivity))
  have mLo : N^(2/5 : ℝ) ≤ (m : ℝ) := by
    apply (mul_le_mul_iff_left₀ gR).mp
    calc
      _ ≤ N^(2/5 : ℝ)*N^(1/4096 : ℝ) := mul_le_mul_of_nonneg_left gCap (by positivity)
      _ = N^(2/5+1/4096 : ℝ) := (Real.rpow_add N0 _ _).symm
      _ ≤ N^(27/64 : ℝ) := Real.rpow_le_rpow_of_exponent_le N1 (by norm_num)
      _ ≤ (u : ℝ) := (Nat.lt_floor_add_one _).le.trans (by exact_mod_cast Nat.succ_le_of_lt uLo)
      _ = _ := mgR.symm
  have baseTarget : m.gcd c.val ≤ thinHighLeftDivisorCap n := by
    have dvd : m.gcd (n/g) ∣ u.gcd n := Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans ⟨g,mg.symm⟩)
      ((Nat.gcd_dvd_right _ _).trans ⟨g,(Nat.div_mul_cancel gn).symm⟩)
    exact (gcd_val_nat_cast_le_gcd (m := m) (n/g)).trans
      ((Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ u0) dvd).trans target)
  have prodTop : (hi : ℝ)*(u : ℝ) ≤ 2*N^(1+3/8192 : ℝ) := by
    apply (show (hi : ℝ)*(u : ℝ) ≤ weilNearProductCap n by exact_mod_cast prod).trans
    unfold weilNearProductCap
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
  have bound (q : ℕ) (hq : q ∈ I) : ‖row q‖ ≤ (B/(u : ℝ))*(1/(q : ℝ)) := by
    let l := smallReverseWeilPrimeLower n lo q
    let r := smallReverseWeilPrimeUpper n hi q
    let a : ZMod m := ((q/g : ℕ) : ZMod m)
    let C := c*a⁻¹
    have memQ := mem_Icc.mp (mem_filter.mp hq).1
    have q0 : 0 < q := memQ.1
    have qR : (0 : ℝ) < q := by exact_mod_cast q0
    have smallQ : (q : ℝ) ≤ N^(1/24 : ℝ) :=
      (show (q : ℝ) ≤ reverseWeilShortCut n by exact_mod_cast memQ.2.trans (min_le_right _ _)).trans
      (Nat.floor_le (by positivity))
    have cof : (q/g).Coprime m := (mem_filter.mp hq).2.2.1
    have unit : IsUnit a⁻¹ := by
      obtain ⟨v,eq⟩ := (ZMod.isUnit_iff_coprime (q/g) m).mpr cof
      unfold a
      rw [← eq,ZMod.inv_coe_unit]
      exact Units.isUnit _
    have targetC : (m.gcd C.val : ℝ) ≤ N^(1/2048 : ℝ) :=
      (show (m.gcd C.val : ℝ) ≤ thinHighLeftDivisorCap n by
        exact_mod_cast (gcd_val_mul_unit_le c a⁻¹ unit).trans baseTarget).trans
      (Nat.floor_le (by positivity))
    have rN : r ≤ n := (min_le_left _ _).trans (min_le_left _ _)
    have rCut : r ≤ rightLargeCofactorCut n := (min_le_left _ _).trans (min_le_right _ _)
    have rTop : (r : ℝ) ≤ N^(33/64 : ℝ) :=
      (show (r : ℝ) ≤ rightLargeCofactorCut n by exact_mod_cast rCut).trans
        (Nat.floor_le (by positivity))
    have cut : vaughanShortCut n ≤ l :=
      (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le N1 (by norm_num))).trans (le_max_left _ _)
    by_cases ord : l < r
    · have lo_lt : lo < q*r := by
        have h : lo/q < r := (le_max_right _ _).trans_lt ord
        simpa only [Nat.mul_comm r q] using (Nat.div_lt_iff_lt_mul q0).mp h
      have vLo : N^(535/1024 : ℝ) ≤ (q*r : ℕ) := by
        apply (Nat.lt_floor_add_one _).le.trans
        exact_mod_cast Nat.succ_le_of_lt (loV.trans_lt lo_lt)
      have qr : q*r ≤ hi := by
        have h := (Nat.le_div_iff_mul_le q0).mp (show r≤hi/q from min_le_right _ _)
        simpa only [Nat.mul_comm r q] using h
      have pLo : N^(535/1024-1/24 : ℝ) ≤ (r : ℝ) := by
        have scaled : N^(535/1024 : ℝ) ≤ (q : ℝ)*(r : ℝ) := by exact_mod_cast vLo
        apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos N0 (1/24 : ℝ))).mp
        calc
          _ = N^(535/1024 : ℝ) := by rw [← Real.rpow_add N0]; congr 1 <;> ring
          _ ≤ (q : ℝ)*(r : ℝ) := scaled
          _ ≤ _ := mul_le_mul_of_nonneg_right smallQ (by positivity)
      have triple : (u : ℝ)*(q : ℝ)*(r : ℝ) ≤ 2*N^(1+3/8192 : ℝ) := by
        have h : (q : ℝ)*(r : ℝ) ≤ hi := by exact_mod_cast qr
        calc
          _ = ((q : ℝ)*(r : ℝ))*(u : ℝ) := by ring
          _ ≤ (hi : ℝ)*(u : ℝ) := mul_le_mul_of_nonneg_right h uR.le
          _ ≤ _ := prodTop
      have uHi : (u : ℝ) ≤ N^(3916/8192 : ℝ) := by
        apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos N0 (535/1024 : ℝ))).mp
        calc
          _ ≤ (u : ℝ)*(((q*r : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left vLo uR.le
          _ ≤ 2*N^(1+3/8192 : ℝ) := by push_cast; rw [← mul_assoc]; exact triple
          _ ≤ N^(1/8192 : ℝ)*N^(1+3/8192 : ℝ) := mul_le_mul_of_nonneg_right large₂ (by positivity)
          _ = _ := by rw [← Real.rpow_add N0,← Real.rpow_add N0]; congr 1 <;> norm_num
      have mHi : (m : ℝ) ≤ N^(3916/8192 : ℝ) :=
        (show (m : ℝ) ≤ u by exact_mod_cast Nat.div_le_self u g).trans uHi
      have estimate := norm_prime_inverse_ramp_near_le C 0 n2 rN mN ord.le cut large pLo rTop mLo mHi targetC T1 divs
      have last : (r : ℝ)*N^(-(1/2048) : ℝ) ≤
          (2*N^(8191/8192 : ℝ))/(u : ℝ)/(q : ℝ) := by
        apply (le_div_iff₀ qR).mpr
        apply (le_div_iff₀ uR).mpr
        calc
          _ = ((u : ℝ)*(q : ℝ)*(r : ℝ))*N^(-(1/2048) : ℝ) := by ring
          _ ≤ (2*N^(1+3/8192 : ℝ))*N^(-(1/2048) : ℝ) :=
            mul_le_mul_of_nonneg_right triple (by positivity)
          _ = _ := by rw [mul_assoc,← Real.rpow_add N0]; congr 1 <;> norm_num
      calc
        _ ≤ 264*T^4*L^8*((r : ℝ)*N^(-(1/2048) : ℝ)) := by simpa only [mul_assoc] using estimate
        _ ≤ 264*T^4*L^8*((2*N^(8191/8192 : ℝ))/(u : ℝ)/(q : ℝ)) :=
          mul_le_mul_of_nonneg_left last (by positivity)
        _ = _ := by unfold B; ring
    · have empty : Ioc l r = ∅ := Ioc_eq_empty ord
      have eq0 : row q=0 := by
        change primeInverseRampWindow n l r C 0=0
        simp [primeInverseRampWindow,empty]
      rw [eq0,norm_zero]
      positivity
  have support : I ⊆ Icc 1 n := by
    intro q hq
    have r := mem_Icc.mp (mem_filter.mp hq).1
    exact mem_Icc.mpr ⟨r.1,r.2.trans ((min_le_left _ _).trans
      (Nat.floor_le_of_le (Real.rpow_le_self_of_one_le N1 (by norm_num))))⟩
  have harmonicBound : (∑ q ∈ I, 1/(q : ℝ)) ≤ L := by
    refine (sum_le_sum_of_subset_of_nonneg support (fun _ _ _ => by positivity)).trans ?_
    calc
      _ = (harmonic n : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
      _ ≤ 1+Real.log n := by exact_mod_cast harmonic_le_one_add_log n
      _ ≤ _ := by
        unfold L logBudget
        exact add_le_add (le_refl _) (Real.log_le_log N0 (by linarith))
  have sumBound : ‖∑ q ∈ I, -(μ q : ℂ)*row q‖ ≤ B/(u : ℝ)*L := by
    calc
      _ ≤ ∑ q ∈ I, ‖-(μ q : ℂ)*row q‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ I, (B/(u : ℝ))*(1/(q : ℝ)) := by
        refine sum_le_sum fun q hq => ?_
        rw [norm_mul,norm_neg]
        simpa only [one_mul,moebiusComplex] using mul_le_mul (norm_moebiusComplex_le_one q)
          (bound q hq) (norm_nonneg _) zero_le_one
      _ = (B/(u : ℝ))*(∑ q ∈ I,1/(q : ℝ)) := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left harmonicBound (by positivity)
  change (u : ℝ)*‖∑ q ∈ I, -(μ q : ℂ)*row q‖ ≤ _
  exact (mul_le_mul_of_nonneg_left sumBound uR.le).trans_eq (by
    unfold B L N
    field_simp [uR.ne'] <;> ring)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_small_short_bridge -/
section

namespace GoldbachTypeII13

open Finset ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def smallReverseWeilSelected (n u g lo hi : ℕ) : Finset RightLowWaveIndex :=
  (longRightLowItems n).filter fun j =>
    j.2 ≤ reverseWeilShortCut n ∧ j.2.gcd n ≤ sparseTargetDivisorCap n ∧ j.2.gcd n ≤ targetDivisorCap n ∧
      u.gcd (rightLowWaveStep j)=g ∧ lo < rightLowWaveStep j ∧ rightLowWaveStep j ≤ hi

set_option maxHeartbeats 1800000 in
theorem small_reverse_weil_window_eq_selected {n u g lo hi : ℕ}
    (u0 : 0 < u) (g0 : 0 < g) (gu : g ∣ u) (gn : g ∣ n)
    (lLower : maximumStep n ≤ lo) (hiN : hi ≤ n) :
    smallReverseWeilWindow n u g lo hi =
      ∑ j ∈ smallReverseWeilSelected n u g lo hi,
        rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) u : ℂ) := by
  let m := u/g
  let c : ZMod m := (n/g : ℕ)
  let Q := smallReverseWeilFactors n u g
  let J (q : ℕ) :=
    ((Ioc (smallReverseWeilPrimeLower n lo q) (smallReverseWeilPrimeUpper n hi q)).filter
      (fun p => p.Coprime m)).filter (fun p => p.Prime ∧ ¬p∣n)
  let P := Q.sigma J
  let liftPoint (x : Σ _ : ℕ, ℕ) : RightLowWaveIndex := ⟨x.2,x.1⟩
  let F (q p : ℕ) := (inverseRampNat (c*((q/g : ℕ) : ZMod m)⁻¹) 0 p : ℂ)
  let w (x : Σ _ : ℕ, ℕ) := rightLowWaveWeight (liftPoint x)*F x.1 x.2
  let value (j : RightLowWaveIndex) := rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) u : ℂ)
  have mg : g*m=u := Nat.mul_div_cancel' gu
  have m0 : 0 < m := Nat.div_pos (Nat.le_of_dvd u0 gu) g0
  have dataQ (q : ℕ) (hq : q ∈ Q) :
      (1 ≤ q ∧ q ≤ min (cutoffU n) (reverseWeilShortCut n)) ∧
        g ∣ q ∧ (q/g).Coprime m ∧ q.gcd n ≤ sparseTargetDivisorCap n ∧ q.gcd n ≤ targetDivisorCap n := by
    exact ⟨mem_Icc.mp (mem_filter.mp hq).1,(mem_filter.mp hq).2⟩
  have dataJ (q p : ℕ) (hp : p ∈ J q) :
      smallReverseWeilPrimeLower n lo q < p ∧ p ≤ smallReverseWeilPrimeUpper n hi q ∧
        p.Coprime m ∧ p.Prime ∧ ¬p∣n := by
    obtain ⟨interval,co⟩ := mem_filter.mp (mem_filter.mp hp).1
    exact ⟨(mem_Ioc.mp interval).1,(mem_Ioc.mp interval).2,co,(mem_filter.mp hp).2⟩
  have liftMem (x : Σ _ : ℕ, ℕ) (hx : x ∈ P) : liftPoint x ∈ smallReverseWeilSelected n u g lo hi := by
    obtain ⟨hq,hp⟩ := mem_sigma.mp hx
    obtain ⟨⟨q0,qHi⟩,dvdq,qa,qSparse,qTarget⟩ := dataQ _ hq
    obtain ⟨pl,pr,pc,prime,nd⟩ := dataJ _ _ hp
    have gQ : g*(x.1/g)=x.1 := Nat.mul_div_cancel' dvdq
    have poly : rightLowWaveStep (liftPoint x)=g*((x.1/g)*x.2) := by
      change x.1*x.2=g*((x.1/g)*x.2)
      rw [← mul_assoc,gQ]
    have l : lo < rightLowWaveStep (liftPoint x) := by
      change lo < x.1*x.2
      have h : lo/x.1 < x.2 := (le_max_right _ _).trans_lt pl
      simpa only [Nat.mul_comm x.2 x.1] using (Nat.div_lt_iff_lt_mul q0).mp h
    have r : rightLowWaveStep (liftPoint x) ≤ hi := by
      change x.1*x.2 ≤ hi
      have h : x.2 ≤ hi/x.1 := pr.trans (min_le_right _ _)
      simpa only [Nat.mul_comm x.2 x.1] using (Nat.le_div_iff_mul_le q0).mp h
    have base : liftPoint x ∈ rightLowWaveItems n := by
      refine mem_sigma.mpr ⟨mem_Ioc.mpr ⟨(le_max_left _ _).trans_lt pl,pr.trans (min_le_left _ _)⟩,
        mem_Icc.mpr ⟨q0,le_min (qHi.trans (min_le_left _ _)) ?_⟩⟩
      exact (Nat.le_div_iff_mul_le prime.pos).mpr (r.trans hiN)
    have long : liftPoint x ∈ longRightLowItems n := mem_filter.mpr
      ⟨mem_filter.mpr ⟨base,prime,nd⟩,not_le_of_gt (lLower.trans_lt l)⟩
    have cp : ((x.1/g)*x.2).Coprime m := Nat.coprime_mul_iff_left.mpr ⟨qa,pc⟩
    have gcd : u.gcd (rightLowWaveStep (liftPoint x))=g := by
      rw [poly,← mg,Nat.gcd_mul_left,Nat.gcd_comm m,cp.gcd_eq_one,mul_one]
    exact mem_filter.mpr ⟨long,qHi.trans (min_le_right _ _),qSparse,qTarget,gcd,l,r⟩
  have liftSurj (j : RightLowWaveIndex) (hj : j ∈ smallReverseWeilSelected n u g lo hi) :
       ∃ x ∈ P, liftPoint x=j := by
    obtain ⟨long,qCap,qSparse,qTarget,gcd,lower,upper⟩ := mem_filter.mp hj
    obtain ⟨prime,nd⟩ := (mem_filter.mp (mem_filter.mp long).1).2
    obtain ⟨pRange,qRange⟩ := mem_sigma.mp (long_right_low_subset n long)
    have gd : u.gcd (j.1*j.2) ∣ n := by
      rw [Nat.mul_comm j.1]
      exact gcd.symm ▸ gn
    have split := gcd_right_step_dvd_cofactor_when_prime_nondvd prime nd gd
    dsimp only at split
    rw [Nat.mul_comm j.1,show u.gcd (j.2*j.1)=g from gcd] at split
    have gQ : g*(j.2/g)=j.2 := Nat.mul_div_cancel' split.1
    have poly : rightLowWaveStep j=g*((j.2/g)*j.1) := by
      change j.2*j.1=g*((j.2/g)*j.1)
      rw [← mul_assoc,gQ]
    have gc : (rightLowWaveStep j).gcd u=g := (Nat.gcd_comm _ _).trans gcd
    have cp : ((j.2/g)*j.1).Coprime m := by
      have core : (rightLowWaveStep j/(rightLowWaveStep j).gcd u).Coprime (u/(rightLowWaveStep j).gcd u) :=
        Nat.coprime_div_gcd_div_gcd (gc.symm ▸ g0)
      rw [gc,poly,Nat.mul_div_cancel_left _ g0] at core
      exact core
    obtain ⟨qa,pc⟩ := Nat.coprime_mul_iff_left.mp cp
    have q0 := (mem_Icc.mp qRange).1
    have hQ : j.2 ∈ Q := mem_filter.mpr
      ⟨mem_Icc.mpr ⟨q0,le_min ((mem_Icc.mp qRange).2.trans (min_le_left _ _)) qCap⟩,
        split.1,qa,qSparse,qTarget⟩
    have l : smallReverseWeilPrimeLower n lo j.2 < j.1 := by
      apply max_lt (mem_Ioc.mp pRange).1
      apply (Nat.div_lt_iff_lt_mul (show 0 < j.2 from q0)).mpr
      rw [Nat.mul_comm]
      exact lower
    have r : j.1 ≤ smallReverseWeilPrimeUpper n hi j.2 := by
      refine le_min (mem_Ioc.mp pRange).2 ((Nat.le_div_iff_mul_le (show 0 < j.2 from q0)).mpr ?_)
      rw [Nat.mul_comm]
      exact upper
    have hp : j.1 ∈ J j.2 := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨l,r⟩,pc⟩,prime,nd⟩
    exact ⟨⟨j.2,j.1⟩,mem_sigma.mpr ⟨hQ,hp⟩,by cases j; rfl⟩
  have eval (x : Σ _ : ℕ, ℕ) (hx : x ∈ P) : w x=value (liftPoint x) := by
    obtain ⟨hq,hp⟩ := mem_sigma.mp hx
    have qa := (dataQ _ hq).2.2.1
    have pc := (dataJ _ _ hp).2.2.1
    have gcd : (rightLowWaveStep (liftPoint x)).gcd u=g := (Nat.gcd_comm _ _).trans
      (mem_filter.mp (liftMem x hx)).2.2.2.2.1
    have poly : rightLowWaveStep (liftPoint x)=g*((x.1/g)*x.2) := by
      change x.1*x.2=g*((x.1/g)*x.2)
      rw [← mul_assoc,Nat.mul_div_cancel' (dataQ _ hq).2.1]
    let _ : NeZero m := ⟨m0.ne'⟩
    have cp : ((x.1/g)*x.2).Coprime m := Nat.coprime_mul_iff_left.mpr ⟨qa,pc⟩
    have part : inverseRampNat (c*((x.1/g : ℕ) : ZMod m)⁻¹) 0 x.2 =
        rightInverseRamp n (rightLowWaveStep (liftPoint x)) u := by
      rw [← inverse_ramp_nat_mul_right c 0 qa pc]
      unfold inverseRampNat rightInverseRamp
      rw [gcd]
      dsimp only
      rw [poly,Nat.mul_div_cancel_left _ g0]
      apply centered_inverse_ramp_eq_of_cast_eq
      rw [Int.cast_natCast,ZMod.natCast_zmod_val,sub_zero,Int.cast_mul,Int.cast_natCast,cast_gcdA_eq_inv_of_coprime cp]
    unfold w value F
    rw [part]
  have expansion : smallReverseWeilWindow n u g lo hi = ∑ x ∈ P,w x := by
    change (∑ q ∈ Q, -(μ q : ℂ)*(∑ p ∈ J q, (vonMangoldt p : ℂ)*F q p)) = _
    unfold P
    rw [sum_sigma]
    refine sum_congr rfl fun q _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun p _ => ?_
    unfold w liftPoint rightLowWaveWeight
    exact (mul_assoc ..).symm
  rw [expansion]
  refine sum_bij (fun x _ => liftPoint x) liftMem ?_ ?_ eval
  swap
  · intro j hj
    obtain ⟨x,hx,e⟩ := liftSurj j hj
    exact ⟨x,hx,e⟩
  intro x hx y hy e
  have pEq : x.2=y.2 := congrArg Sigma.fst e
  have qEq : x.1=y.1 := congrArg (fun j : RightLowWaveIndex => j.2) e
  exact Sigma.ext qEq (heq_of_eq pEq)

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_small_short_row -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def smallReverseWeilRow (n u lo hi : ℕ) : ℂ :=
  ∑ g ∈ weilNearRowDivisors n u, smallReverseWeilWindow n u g lo hi

def smallReverseWeilRowItems (n u lo hi : ℕ) : Finset RightLowWaveIndex :=
  (longRightLowItems n).filter fun j =>
    j.2 ≤ reverseWeilShortCut n ∧ j.2.gcd n ≤ sparseTargetDivisorCap n ∧ j.2.gcd n ≤ targetDivisorCap n ∧
      u.gcd (rightLowWaveStep j) ∈ weilNearRowDivisors n u ∧ lo < rightLowWaveStep j ∧ rightLowWaveStep j ≤ hi

theorem small_reverse_weil_row_eq_selected {n u lo hi : ℕ} (u0 : 0 < u) (uN : u ≤ n)
    (loTop : maximumStep n ≤ lo) (hiN : hi ≤ n) :
    smallReverseWeilRow n u lo hi =
      ∑ j ∈ smallReverseWeilRowItems n u lo hi,
        rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) u : ℂ) := by
  let G := weilNearRowDivisors n u
  let J := smallReverseWeilRowItems n u lo hi
  let d (j : RightLowWaveIndex) := u.gcd (rightLowWaveStep j)
  let w (j : RightLowWaveIndex) := rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) u : ℂ)
  have maps : ∀ j ∈ J, d j ∈ G := fun _ hj => (mem_filter.mp hj).2.2.2.2.1
  change (∑ g ∈ G, smallReverseWeilWindow n u g lo hi) = ∑ j ∈ J, w j
  rw [← sum_fiberwise_of_maps_to maps w]
  refine sum_congr rfl fun g hg => ?_
  obtain ⟨hgN,gu,_⟩ := mem_filter.mp hg
  have gn := (Nat.mem_divisors.mp hgN).1
  have g0 := Nat.pos_of_dvd_of_pos gn (u0.trans_le uN)
  rw [small_reverse_weil_window_eq_selected u0 g0 gu gn loTop hiN]
  congr 1
  ext j
  simp only [smallReverseWeilSelected,smallReverseWeilRowItems,J,d,mem_filter]
  constructor
  · rintro ⟨base,short,gcdS,gcdT,heq,l,r⟩
    exact ⟨⟨base,short,gcdS,gcdT,heq.symm ▸ hg,l,r⟩,heq⟩
  · rintro ⟨⟨base,short,gcdS,gcdT,_,l,r⟩,heq⟩
    exact ⟨base,short,gcdS,gcdT,heq,l,r⟩

theorem norm_small_reverse_weil_row_le {n u lo hi : ℕ}
    (n2 : 2 ≤ n) (u0 : 0 < u) (uN : u ≤ n) (uLo : ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u)
    (target : u.gcd n ≤ thinHighLeftDivisorCap n)
    (loV : widerLowFarModulusCap n ≤ lo) (prod : hi*u ≤ weilNearProductCap n)
    (large : (2 : ℝ) ≤ (n : ℝ)^(1/384 : ℝ))
    (large₂ : (2 : ℝ) ≤ (n : ℝ)^(1/8192 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (divs : ∀ b ≤ n, (b.divisors.card : ℝ) ≤ T) :
    ‖smallReverseWeilRow n u lo hi‖ ≤
      (528*T^5*logBudget n^9*(n : ℝ)^(8191/8192 : ℝ))*(1/(u : ℝ)) := by
  let G := weilNearRowDivisors n u
  let B := (528*T^4*logBudget n^9*(n : ℝ)^(8191/8192 : ℝ))/(u : ℝ)
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have uR : (0 : ℝ) < u := by exact_mod_cast u0
  have B0 : 0 ≤ B := by unfold B; positivity
  have Gcard : (#G : ℝ) ≤ T :=
    (show (#G : ℝ) ≤ (n.divisors.card : ℝ) from by
      exact_mod_cast card_filter_le n.divisors (fun g => g ∣ u ∧ g ≤ thinHighGcdCap n)).trans (divs n le_rfl)
  have each (g : ℕ) (hg : g ∈ G) : ‖smallReverseWeilWindow n u g lo hi‖ ≤ B := by
    obtain ⟨hn,gu,gs⟩ := mem_filter.mp hg
    have gn := (Nat.mem_divisors.mp hn).1
    have g0 := Nat.pos_of_dvd_of_pos gn (u0.trans_le uN)
    unfold B
    apply (le_div_iff₀ uR).mpr
    rw [mul_comm]
    exact norm_small_reverse_weil_window_le n2 u0 uN uLo target g0 gu gn gs loV prod large large₂ T1 divs
  calc
    _ ≤ ∑ g ∈ G, ‖smallReverseWeilWindow n u g lo hi‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ G,B := sum_le_sum each
    _ = (#G : ℝ)*B := by rw [sum_const,nsmul_eq_mul]
    _ ≤ T*B := mul_le_mul_of_nonneg_right Gcard B0
    _ = _ := by unfold B; ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_small_short_remainder -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

theorem saving_of_eventual_inverse_prime_growth (f : ℕ → ℂ) (K : ℝ) (K0 : 0 ≤ K)
    (bound : ∀ᶠ n : ℕ in atTop, ∀ T : ℝ, 1 ≤ T →
      (∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) →
      ‖f n‖ ≤ K*(n : ℝ)^(8191/8192 : ℝ)*T^8*logBudget n^11) : saving f := by
  intro ε ε0
  obtain ⟨D,D1,dBound⟩ := divisor_envelope_at_power 262144 (by decide)
  let C := K*D^8
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-(13/262144) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 13/262144)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(13/262144) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have eventual : ∀ᶠ n : ℕ in atTop, ‖f n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le_power (1/262144) (by norm_num),
      scaled.eventually_lt_const ε0,bound] with n n1 logn slim h
    have n0 : (0 : ℝ) < n := by exact_mod_cast n1
    have D0 := zero_le_one.trans D1
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/262144 : ℝ)
    let T := D*X
    have X1 : 1 ≤ X := Real.one_le_rpow (by exact_mod_cast n1) (by norm_num)
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1 X1
    have ex : (n : ℝ)^(8191/8192 : ℝ)*X^19 = (n : ℝ)^(-(13/262144) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast n0.le,← Real.rpow_add n0,← Real.rpow_add_one n0.ne']
      congr 1
      norm_num
    calc
      _ ≤ K*(n : ℝ)^(8191/8192 : ℝ)*T^8*logBudget n^11 := h T T1 (dBound n)
      _ ≤ K*(n : ℝ)^(8191/8192 : ℝ)*T^8*X^11 := by gcongr
      _ = C*((n : ℝ)^(8191/8192 : ℝ)*X^19) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(13/262144) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right slim.le n0.le
  obtain ⟨N,h⟩ := eventually_atTop.mp eventual
  exact ⟨N,fun n hn _ => h n hn⟩

def smallReverseWeilOriginalCut (n : ℕ) : ℂ :=
  ∑ i ∈ reverseWeilLeftRows n,
    let u := leftBilinearStep i
    leftPrimeWeight n i*smallReverseWeilRow n u (reverseWeilStepLower n u) (reverseWeilStepUpper n u)

theorem small_reverse_weil_original_cut_eq_selected (n : ℕ) :
    smallReverseWeilOriginalCut n =
      ∑ i ∈ reverseWeilLeftRows n, leftPrimeWeight n i *
        ∑ j ∈ smallReverseWeilRowItems n (leftBilinearStep i) (reverseWeilStepLower n (leftBilinearStep i))
          (reverseWeilStepUpper n (leftBilinearStep i)),
          rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) (leftBilinearStep i) : ℂ) := by
  unfold smallReverseWeilOriginalCut
  refine sum_congr rfl fun i hi => ?_
  have bounds := mem_Icc.mp (bilateral_left_step_range (mem_filter.mp hi).1)
  dsimp only
  rw [small_reverse_weil_row_eq_selected (lo := reverseWeilStepLower n (leftBilinearStep i))
    (hi := reverseWeilStepUpper n (leftBilinearStep i)) bounds.1 bounds.2 (le_max_left _ _) (min_le_left _ _)]

theorem small_reverse_weil_original_cut_saving : saving smallReverseWeilOriginalCut := by
  apply saving_of_eventual_inverse_prime_growth _ 528 (by norm_num)
  have huge : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (n : ℝ)^(1/384 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/384)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  have huge₂ : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (n : ℝ)^(1/8192 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/8192)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (2 : ℕ), huge, huge₂] with n n2 large large₂
  intro T T1 divs
  let I := reverseWeilLeftRows n
  let u := leftBilinearStep
  let L := logBudget n
  let W := T^3*L
  let B := 528*T^5*L^9*(n : ℝ)^(8191/8192 : ℝ)
  have n1 : 1 ≤ n := (by decide : 1 ≤ (2 : ℕ)).trans n2
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have B0 : 0 ≤ B := by unfold B; positivity
  have W0 : 0 ≤ W := by unfold W; positivity
  have base : I ⊆ bilateralLeftWaveItems n := filter_subset _ _
  have boundH : (∑ m ∈ Icc 1 n, 1/(m : ℝ)) ≤ L := calc
    _ = (harmonic n : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    _ ≤ 1+Real.log n := by exact_mod_cast harmonic_le_one_add_log n
    _ ≤ L := by
      unfold L logBudget
      exact add_le_add (le_refl _) (Real.log_le_log (zero_lt_one.trans_le nR) (by linarith))
  have steps (i : ℕ × ℕ) (hi : i ∈ I) : u i ∈ Icc 1 n :=
    bilateral_left_step_range (base hi)
  have weighted : (∑ i ∈ I, ‖leftPrimeWeight n i‖*(1/(u i : ℝ))) ≤ W*L :=
    (sum_norm_mul_le_of_step_mass I u (leftPrimeWeight n) (fun m => 1/(m : ℝ)) steps
      (fun _ _ => by positivity) (prime_left_mass_of_subset base T1 divs)).trans
      (mul_le_mul_of_nonneg_left boundH W0)
  have each (i : ℕ × ℕ) (hi : i ∈ I) :
      ‖smallReverseWeilRow n (u i) (reverseWeilStepLower n (u i)) (reverseWeilStepUpper n (u i))‖ ≤
       B*(1/(u i : ℝ)) := by
    have r := mem_Icc.mp (steps i hi)
    have f := (mem_filter.mp hi).2
    have lo : widerLowFarModulusCap n ≤ reverseWeilStepLower n (u i) := (le_max_left _ _).trans (le_max_right _ _)
    have prod : reverseWeilStepUpper n (u i)*(u i) ≤ weilNearProductCap n :=
      (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
    exact norm_small_reverse_weil_row_le n2 r.1 r.2 f.1 f.2.2.2.2.1 lo prod large large₂ T1 divs
  unfold smallReverseWeilOriginalCut
  change ‖∑ i ∈ I, leftPrimeWeight n i*smallReverseWeilRow n (u i)
    (reverseWeilStepLower n (u i)) (reverseWeilStepUpper n (u i))‖ ≤ _
  calc
    _ ≤ ∑ i ∈ I, ‖leftPrimeWeight n i*smallReverseWeilRow n (u i)
      (reverseWeilStepLower n (u i)) (reverseWeilStepUpper n (u i))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ I, ‖leftPrimeWeight n i‖*(B*(1/(u i : ℝ))) := by
      refine sum_le_sum fun i hi => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (each i hi) (norm_nonneg _)
    _ = B*(∑ i ∈ I, ‖leftPrimeWeight n i‖*(1/(u i : ℝ))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ B*(W*L) := mul_le_mul_of_nonneg_left weighted B0
    _ = _ := by unfold B W L; ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_full_reverse_mask -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def reverseWeilFullRowItems (n u lo hi : ℕ) : Finset RightLowWaveIndex :=
  (longRightLowItems n).filter fun j =>
    j.2.gcd n ≤ sparseTargetDivisorCap n ∧ j.2.gcd n ≤ targetDivisorCap n ∧
      u.gcd (rightLowWaveStep j) ∈ weilNearRowDivisors n u ∧ lo < rightLowWaveStep j ∧ rightLowWaveStep j ≤ hi

theorem reverse_weil_full_rows_eq_union (n u lo hi : ℕ) :
    reverseWeilFullRowItems n u lo hi =
      reverseWeilRowItems n u lo hi ∪ smallReverseWeilRowItems n u lo hi := by
  ext j
  simp only [reverseWeilFullRowItems,reverseWeilRowItems,smallReverseWeilRowItems,mem_filter,mem_union]
  by_cases h : j.2 ≤ reverseWeilShortCut n
  · simp [h,not_lt_of_ge h]
  · simp [h,lt_of_not_ge h]

theorem reverse_weil_rows_disjoint (n u lo hi : ℕ) :
    Disjoint (reverseWeilRowItems n u lo hi) (smallReverseWeilRowItems n u lo hi) := by
  refine disjoint_left.mpr fun j h h' => ?_
  exact (not_le_of_gt (mem_filter.mp h).2.1) (mem_filter.mp h').2.1

def reverseWeilFullExtra (n u v : ℕ) : Prop :=
  u ≤ ⌊(n : ℝ)^(1/2 : ℝ)⌋₊ ∧ u ≤ extendedWideStepCap n ∧
    widerLowFarModulusCap n < v ∧ u ≤ v ∧ u*v ≤ weilNearProductCap n

set_option maxHeartbeats 1400000 in
theorem reverse_weil_full_near_product_mask_iff {n : ℕ} {i : ℕ × ℕ} {j : RightLowWaveIndex}
    (hi : i ∈ bilateralLeftWaveItems n) (hj : j ∈ longRightLowItems n) :
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    (i ∈ reverseWeilLeftRows n ∧ j ∈ reverseWeilFullRowItems n u (reverseWeilStepLower n u) (reverseWeilStepUpper n u)) ↔
      (u ≤ expandedWideStepCap n ∧ ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧
        farInnerThinGate n u v ∧ retainedLowTargetMask n u v ∧ stepWithoutLargeSquare n u ∧
        reverseWeilFullExtra n u v ∧ u.gcd v ∣ n) := by
  dsimp only
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  have ur := mem_Icc.mp (bilateral_left_step_range hi)
  have vr := mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))
  have u0 : 0 < u := ur.1
  have n0 : 0 < n := ur.1.trans ur.2
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n0
  have cutoff : thinHighGcdCap n ≤ cutoffU n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have cof : 1 ≤ cofactorCap n := Nat.le_floor (Real.one_le_rpow nR (by norm_num))
  have gCap : thinHighGcdCap n ≤ maximumStep n := cutoff.trans (by
    change cutoffU n ≤ cutoffU n*cofactorCap n
    simpa only [mul_one] using Nat.mul_le_mul_left (cutoffU n) cof)
  have C1 : expandedHighModulusCap n ≤ widerLowFarModulusCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have C2 : shortLowModulusCap n ≤ widerLowFarModulusCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have rest (h : widerLowFarModulusCap n < v) : remainingExpandedLow n u v :=
    ⟨(fun small => (not_le_of_gt (C1.trans_lt h)) small.1),
      (fun mid => (not_le_of_gt (C2.trans_lt h)) mid.2.2.1),
      (fun wide => (not_le_of_gt h) wide.2.2.1)⟩
  have long : maximumStep n < v := Nat.lt_of_not_ge (mem_filter.mp hj).2
  have level : u-1<v ↔ u≤v := by omega
  have dlo : reverseWeilStepLower n u < v ↔
      widerLowFarModulusCap n < v ∧ u ≤ v ∧ maximumStep n^2 < u*v ∧
      thinHighProductCap n < u*v ∧ highFarStripProductCap n < u*v := by
    simp only [reverseWeilStepLower, max_lt_iff, long, true_and, level,
      Nat.div_lt_iff_lt_mul u0, Nat.mul_comm v u]
  have dhi : v ≤ reverseWeilStepUpper n u ↔ u*v ≤ weilNearProductCap n := by
    have vN : v ≤ n := vr.2
    simp only [reverseWeilStepUpper, le_min_iff, vN, true_and, Nat.le_div_iff_mul_le u0, Nat.mul_comm v u]
  have gg : u.gcd v ∈ weilNearRowDivisors n u ↔ u.gcd v ∣ n ∧ u.gcd v ≤ thinHighGcdCap n := by
    rw [weilNearRowDivisors,mem_filter,Nat.mem_divisors]
    exact ⟨fun h => ⟨h.1.1,h.2.2⟩,fun h => ⟨⟨h.1,n0.ne'⟩,Nat.gcd_dvd_left _ _,h.2⟩⟩
  have rowItems : j ∈ reverseWeilFullRowItems n u (reverseWeilStepLower n u) (reverseWeilStepUpper n u) ↔
      v.gcd n ≤ sparseTargetDivisorCap n ∧ v.gcd n ≤ targetDivisorCap n ∧
      (u.gcd v ∣ n ∧ u.gcd v ≤ thinHighGcdCap n) ∧
      (widerLowFarModulusCap n < v ∧ u ≤ v ∧ maximumStep n^2 < u*v ∧ thinHighProductCap n < u*v ∧
        highFarStripProductCap n < u*v) ∧ u*v ≤ weilNearProductCap n := by
    simp only [reverseWeilFullRowItems,mem_filter,hj,true_and]
    change (j.2.gcd n ≤ sparseTargetDivisorCap n ∧
      j.2.gcd n ≤ targetDivisorCap n ∧ u.gcd v ∈ weilNearRowDivisors n u ∧
      reverseWeilStepLower n u < v ∧ v ≤ reverseWeilStepUpper n u) ↔ _
    rw [← long_right_low_gcd_eq hj]
    change (v.gcd n ≤ _ ∧ v.gcd n ≤ _ ∧ _ ∧ _ ∧ _) ↔ _
    rw [gg,dlo,dhi]
  change (i ∈ reverseWeilLeftRows n ∧
    j ∈ reverseWeilFullRowItems n u (reverseWeilStepLower n u) (reverseWeilStepUpper n u)) ↔ _
  rw [rowItems]
  have lRows : i ∈ reverseWeilLeftRows n ↔
      ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧ u ≤ ⌊(n : ℝ)^(1/2 : ℝ)⌋₊ ∧
      u ≤ expandedWideStepCap n ∧ u ≤ extendedWideStepCap n ∧ weilNearLeftKept n u := by
    simp only [reverseWeilLeftRows,mem_filter,hi,true_and]
    rfl
  rw [lRows]
  simp only [farInnerThinGate,boundedOuterLeftKeptGate,farInnerGate,prefixStepGate,weilNearLeftKept,
    retainedLowTargetMask,targetDivisorKept,reverseWeilFullExtra]
  constructor
  · rintro ⟨⟨geom,root,extCap,ext,left,sq⟩,sparse,target,⟨dvd,gcd⟩,⟨wide,size,mp,tp,fp⟩,top⟩
    exact ⟨extCap,geom,⟨⟨⟨⟨mp,gcd.trans gCap⟩,fp⟩,tp,gcd,target⟩,left⟩,
      ⟨rest wide,sparse⟩,sq,⟨root,ext,wide,size,top⟩,dvd⟩
  · rintro ⟨extCap,geom,⟨⟨⟨⟨mp,_⟩,fp⟩,tp,gcd,target⟩,left⟩,⟨_,sparse⟩,sq,
      ⟨root,ext,wide,size,top⟩,dvd⟩
    exact ⟨⟨geom,root,extCap,ext,left,sq⟩,sparse,target,⟨dvd,gcd⟩,⟨wide,size,mp,tp,fp⟩,top⟩

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_full_reverse_remainder -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def reverseWeilFullSelected (n : ℕ) : ℂ :=
  ∑ i ∈ reverseWeilLeftRows n, leftPrimeWeight n i *
    ∑ j ∈ reverseWeilFullRowItems n (leftBilinearStep i) (reverseWeilStepLower n (leftBilinearStep i))
      (reverseWeilStepUpper n (leftBilinearStep i)),
      rightLowWaveWeight j*(rightInverseRamp n (rightLowWaveStep j) (leftBilinearStep i) : ℂ)

theorem reverse_weil_full_selected_eq_add (n : ℕ) :
    reverseWeilFullSelected n=reverseWeilOriginalCut n+smallReverseWeilOriginalCut n := by
  unfold reverseWeilFullSelected
  rw [reverse_weil_original_cut_eq_selected,small_reverse_weil_original_cut_eq_selected,← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [reverse_weil_full_rows_eq_union,sum_union (reverse_weil_rows_disjoint ..),mul_add]

def reverseWeilFullCutOnOriginal (n : ℕ) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ longRightLowItems n,
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    @ite ℂ (symmetricLowPairKept n u v ∧ reverseWeilFullExtra n u v ∧ u.gcd v ∣ n)
      (Classical.propDecidable _) (leftPrimeWeight n i*rightLowWaveWeight j*(rightInverseRamp n v u : ℂ)) 0

set_option maxHeartbeats 1600000 in
theorem reverse_weil_full_cut_eq_on_original (n : ℕ) :
    reverseWeilFullSelected n=reverseWeilFullCutOnOriginal n := by
  unfold reverseWeilFullSelected
  unfold reverseWeilFullCutOnOriginal
  let L := bilateralLeftWaveItems n
  let J := longRightLowItems n
  let lPredicate (i : ℕ × ℕ) :=
    let u := leftBilinearStep i
    ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧ u ≤ ⌊(n : ℝ)^(1/2 : ℝ)⌋₊ ∧
      u ≤ expandedWideStepCap n ∧ u ≤ extendedWideStepCap n ∧ weilNearLeftKept n u
  have maskL : reverseWeilLeftRows n=L.filter lPredicate := by
    ext i
    simp only [reverseWeilLeftRows,L,mem_filter]
    rfl
  rw [maskL,sum_filter]
  refine sum_congr rfl fun i hi => ?_
  let u := leftBilinearStep i
  let v := rightLowWaveStep
  let R := reverseWeilFullRowItems n u (reverseWeilStepLower n u) (reverseWeilStepUpper n u)
  let p (j : RightLowWaveIndex) := symmetricLowPairKept n u (v j) ∧ reverseWeilFullExtra n u (v j) ∧ u.gcd (v j) ∣ n
  have mask (j : RightLowWaveIndex) (hj : j ∈ J) : i ∈ reverseWeilLeftRows n ∧ j ∈ R ↔ p j := by
    have q := reverse_weil_full_near_product_mask_iff hi hj
    dsimp only at q
    constructor
    · intro x
      obtain ⟨cap,geom,far,target,square,extra,dvd⟩ := q.mp x
      exact ⟨⟨cap,geom,far,target,square⟩,extra,dvd⟩
    · rintro ⟨⟨cap,geom,far,target,square⟩,extra,dvd⟩
      exact q.mpr ⟨cap,geom,far,target,square,extra,dvd⟩
  by_cases left : lPredicate i
  · rw [if_pos left]
    have iRows : i ∈ reverseWeilLeftRows n := by rw [maskL]; exact mem_filter.mpr ⟨hi,left⟩
    have rows : R=J.filter p := by
      ext j
      rw [mem_filter]
      exact ⟨fun jRows =>
          have hJ : j ∈ J := (mem_filter.mp jRows).1
          ⟨hJ,(mask j hJ).mp ⟨iRows,jRows⟩⟩,
        fun h => ((mask j h.1).mpr h.2).2⟩
    change leftPrimeWeight n i*(∑ j ∈ R, rightLowWaveWeight j*(rightInverseRamp n (v j) u : ℂ)) = _
    rw [rows,sum_filter,mul_sum]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : p j
    · rw [if_pos h,if_pos h]
      exact (mul_assoc ..).symm
    · rw [if_neg h,if_neg h,mul_zero]
  · rw [if_neg left]
    symm
    refine sum_eq_zero fun j hj => ?_
    have notP : ¬p j := by
      intro h
      have iRows := ((mask j hj).mpr h).1
      rw [maskL] at iRows
      exact left (mem_filter.mp iRows).2
    exact if_neg notP

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_weil_adaptive_exact -/
section

namespace GoldbachTypeII13

open Finset
open DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def weilAdaptiveLowInterior (n : ℕ) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ longRightLowItems n,
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    if symmetricLowPairKept n u v then
      leftPrimeWeight n i*rightLowWaveWeight j*
        (if (weilNearExtra n i v ∨ weilAdaptiveExtra n i v) ∧ u.gcd v ∣ n then (rightInverseRamp n v u : ℂ)
          else (symmetricResidueError n u v 0 : ℂ))
    else 0

set_option maxHeartbeats 1600000 in
theorem weil_adaptive_low_interior_eq_sub (n : ℕ) :
    weilAdaptiveLowInterior n = weilNearLowInterior n-weilAdaptiveRightRampKept n := by
  unfold weilAdaptiveLowInterior weilNearLowInterior weilAdaptiveRightRampKept
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  unfold weilNearRightRows
  rw [sum_filter,← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  dsimp only
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  let keep := symmetricLowPairKept n u v
  let band := weilAdaptiveExtra n i v ∧ u.gcd v ∣ n
  let old := weilNearExtra n i v ∧ u.gcd v ∣ n
  let both := (weilNearExtra n i v ∨ weilAdaptiveExtra n i v) ∧ u.gcd v ∣ n
  let right := widerLowFarModulusCap n < v ∧ v.gcd n ≤ sparseTargetDivisorCap n ∧ v.gcd n ≤ targetDivisorCap n
  let sub := weilAdaptiveGroupGate n i j ∧ weilNearLeftKept n u
  let w := leftPrimeWeight n i*rightLowWaveWeight j
  let err := (symmetricResidueError n u v 0 : ℂ)
  let r₁ := (rightInverseRamp n u v : ℂ)
  let r₂ := (rightInverseRamp n v u : ℂ)
  change (if keep then w*(if both then r₂ else err) else 0) =
    (if keep then w*(if old then r₂ else err) else 0)-(if right then w*(if sub then r₁ else 0) else 0)
  have mask : right ∧ sub ↔ keep ∧ band := by
    have h := weil_adaptive_product_mask_iff (i := i) hj
    dsimp only at h
    constructor
    · intro h₁
      have inRows : j ∈ weilNearRightRows n := mem_filter.mpr ⟨hj,h₁.1⟩
      obtain ⟨cap,geo,thin,target,square,extra,dvd⟩ := h.mp ⟨inRows,h₁.2.1,h₁.2.2⟩
      exact ⟨⟨cap,geo,thin,target,square⟩,extra,dvd⟩
    · intro h₁
      obtain ⟨⟨cap,geo,thin,target,square⟩,extra,dvd⟩ := h₁
      obtain ⟨inRows,group,arithmetic⟩ := h.mpr ⟨cap,geo,thin,target,square,extra,dvd⟩
      exact ⟨(mem_filter.mp inRows).2,group,arithmetic⟩
  have simpCut : (if right then w*(if sub then r₁ else 0) else 0) =
      if keep ∧ band then w*r₁ else 0 := by
    by_cases h : right ∧ sub
    · rw [if_pos h.1,if_pos h.2,if_pos (mask.mp h)]
    · rw [if_neg (fun hs => h (mask.mpr hs))]
      by_cases hr : right
      · rw [if_pos hr,if_neg (fun hs => h ⟨hr,hs⟩),mul_zero]
      · rw [if_neg hr]
  rw [simpCut]
  by_cases hk : keep
  · rw [if_pos hk,if_pos hk]
    by_cases hb : band
    · have vr := mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))
      have n0 : 0 < n := vr.1.trans vr.2
      have absent : ¬old := fun h => (weil_adaptive_right_ramp_factor_lower n0 hb.1.2.2.2.2).not_ge
        h.1.2.2.2.2
      have used : both := ⟨Or.inr hb.1,hb.2⟩
      rw [if_pos used,if_neg absent,if_pos ⟨hk,hb⟩]
      have e : err=r₁+r₂ := by
        unfold err r₁ r₂
        exact_mod_cast symmetric_low_residue_decomposes n0 hb.2
      rw [e]
      ring
    · rw [if_neg (fun h : keep ∧ band => hb h.2),sub_zero]
      by_cases ho : old
      · have hc : both := ⟨Or.inl ho.1,ho.2⟩
        rw [if_pos ho,if_pos hc]
      · have hc : ¬both := fun h => h.1.elim (fun f => ho ⟨f,h.2⟩) (fun f => hb ⟨f,h.2⟩)
        rw [if_neg ho,if_neg hc]
  · simp only [if_neg hk,if_neg (fun h : keep ∧ band => hk h.1),sub_zero]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_both_weil_exact_remainder -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def reverseWeilCutOnOriginal (n : ℕ) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ longRightLowItems n,
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    @ite ℂ (symmetricLowPairKept n u v ∧ reverseWeilExtra n u v j.2 ∧ u.gcd v ∣ n)
      (Classical.propDecidable _) (leftPrimeWeight n i*rightLowWaveWeight j*(rightInverseRamp n v u : ℂ)) 0

set_option maxHeartbeats 1600000 in
theorem reverse_weil_cut_eq_on_original (n : ℕ) :
    reverseWeilOriginalCut n=reverseWeilCutOnOriginal n := by
  rw [reverse_weil_original_cut_eq_selected]
  unfold reverseWeilCutOnOriginal
  let L := bilateralLeftWaveItems n
  let J := longRightLowItems n
  let lPredicate (i : ℕ × ℕ) :=
    let u := leftBilinearStep i
    ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧ u ≤ ⌊(n : ℝ)^(1/2 : ℝ)⌋₊ ∧
      u ≤ expandedWideStepCap n ∧ u ≤ extendedWideStepCap n ∧ weilNearLeftKept n u
  have maskL : reverseWeilLeftRows n=L.filter lPredicate := by
    ext i
    simp only [reverseWeilLeftRows,L,mem_filter]
    rfl
  rw [maskL,sum_filter]
  refine sum_congr rfl fun i hi => ?_
  let u := leftBilinearStep i
  let v := rightLowWaveStep
  let R := reverseWeilRowItems n u (reverseWeilStepLower n u) (reverseWeilStepUpper n u)
  let p (j : RightLowWaveIndex) := symmetricLowPairKept n u (v j) ∧ reverseWeilExtra n u (v j) j.2 ∧ u.gcd (v j) ∣ n
  have mask (j : RightLowWaveIndex) (hj : j ∈ J) : i ∈ reverseWeilLeftRows n ∧ j ∈ R ↔ p j := by
    have q := reverse_weil_near_product_mask_iff hi hj
    dsimp only at q
    constructor
    · intro x
      obtain ⟨cap,geom,far,target,square,extra,dvd⟩ := q.mp x
      exact ⟨⟨cap,geom,far,target,square⟩,extra,dvd⟩
    · rintro ⟨⟨cap,geom,far,target,square⟩,extra,dvd⟩
      exact q.mpr ⟨cap,geom,far,target,square,extra,dvd⟩
  by_cases left : lPredicate i
  · rw [if_pos left]
    have iRows : i ∈ reverseWeilLeftRows n := by rw [maskL]; exact mem_filter.mpr ⟨hi,left⟩
    have rows : R=J.filter p := by
      ext j
      rw [mem_filter]
      exact ⟨fun jRows =>
          have hJ : j ∈ J := (mem_filter.mp jRows).1
          ⟨hJ,(mask j hJ).mp ⟨iRows,jRows⟩⟩,
        fun h => ((mask j h.1).mpr h.2).2⟩
    change leftPrimeWeight n i*(∑ j ∈ R, rightLowWaveWeight j*(rightInverseRamp n (v j) u : ℂ)) = _
    rw [rows,sum_filter,mul_sum]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : p j
    · rw [if_pos h,if_pos h]
      exact (mul_assoc ..).symm
    · rw [if_neg h,if_neg h,mul_zero]
  · rw [if_neg left]
    symm
    refine sum_eq_zero fun j hj => ?_
    have notP : ¬p j := by
      intro h
      have iRows := ((mask j hj).mpr h).1
      rw [maskL] at iRows
      exact left (mem_filter.mp iRows).2
    exact if_neg notP

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_remainder -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def adaptiveInnerLowRemainder (n : ℕ) : ℂ :=
  weilAdaptiveLowInterior n-reverseWeilFullCutOnOriginal n

def innerLowFirstRamp (n : ℕ) (keep : ℕ × ℕ → RightLowWaveIndex → Prop) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ longRightLowItems n,
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    if symmetricLowPairKept n u v ∧ u.gcd v ∣ n ∧ keep i j ∧
        ¬(weilNearExtra n i v ∨ weilAdaptiveExtra n i v) then
      leftPrimeWeight n i*rightLowWaveWeight j*(rightInverseRamp n u v : ℂ)
    else 0

def innerLowSecondRamp (n : ℕ) (keep : ℕ × ℕ → RightLowWaveIndex → Prop) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ longRightLowItems n,
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    if symmetricLowPairKept n u v ∧ u.gcd v ∣ n ∧ keep i j ∧ ¬reverseWeilFullExtra n u v then
      leftPrimeWeight n i*rightLowWaveWeight j*(rightInverseRamp n v u : ℂ)
    else 0

set_option maxHeartbeats 1500000 in
theorem adaptive_inner_low_remainder_eq_ramps (n : ℕ) :
    adaptiveInnerLowRemainder n =
      innerLowFirstRamp n (fun _ _ => True)+innerLowSecondRamp n (fun _ _ => True) := by
  unfold adaptiveInnerLowRemainder weilAdaptiveLowInterior reverseWeilFullCutOnOriginal
    innerLowFirstRamp innerLowSecondRamp
  rw [← sum_sub_distrib,← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib,← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  dsimp only
  by_cases hk : symmetricLowPairKept n u v
  · by_cases hd : u.gcd v ∣ n
    · have vr := mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))
      have n0 : 0 < n := vr.1.trans vr.2
      have e : (symmetricResidueError n u v 0 : ℂ) =
          (rightInverseRamp n u v : ℂ)+(rightInverseRamp n v u : ℂ) := by
        exact_mod_cast symmetric_low_residue_decomposes n0 hd
      by_cases h₁ : weilNearExtra n i v ∨ weilAdaptiveExtra n i v <;>
        by_cases h₂ : reverseWeilFullExtra n u v <;>
        dsimp only [u,v] at hk hd h₁ h₂ e <;>
        simp [hk,hd,h₁,h₂,e] <;> ring
    · have e : (symmetricResidueError n u v 0 : ℂ) = 0 := by
        unfold symmetricResidueError
        dsimp only
        rw [if_neg (fun h => hd h.1)]
        simp
      dsimp only [u,v] at hk hd e
      simp [hk,hd,e]
  · dsimp only [u,v] at hk
    simp [hk]

theorem innerLowFirstRamp_split (n : ℕ) (keep : ℕ × ℕ → RightLowWaveIndex → Prop) :
    innerLowFirstRamp n (fun _ _ => True) =
      innerLowFirstRamp n keep+innerLowFirstRamp n (fun i j => ¬keep i j) := by
  unfold innerLowFirstRamp
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : keep i j <;> simp [h]

theorem innerLowSecondRamp_split (n : ℕ) (keep : ℕ × ℕ → RightLowWaveIndex → Prop) :
    innerLowSecondRamp n (fun _ _ => True) =
      innerLowSecondRamp n keep+innerLowSecondRamp n (fun i j => ¬keep i j) := by
  unfold innerLowSecondRamp
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : keep i j <;> simp [h]

def innerLowNearProduct (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  leftBilinearStep i*rightLowWaveStep j ≤ weilNearProductCap n

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_near_geometry -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4PairIntegral
open scoped Classical

noncomputable section

private theorem half_le_nat_floor_of_two_le {x : ℝ} (h : 2 ≤ x) : x/2 ≤ (⌊x⌋₊ : ℝ) := by
  linarith only [Nat.lt_floor_add_one x,h]

theorem reverse_weil_full_extra_of_inner_low_near {n u : ℕ} {j : RightLowWaveIndex}
    (n1 : 1 ≤ n) (huge : (2 : ℝ) ≤ (n : ℝ)^(1/8192 : ℝ))
    (hj : j ∈ longRightLowItems n)
    (keep : symmetricLowPairKept n u (rightLowWaveStep j))
    (prod : u*rightLowWaveStep j ≤ weilNearProductCap n) :
    reverseWeilFullExtra n u (rightLowWaveStep j) := by
  let N := (n : ℝ)
  let v := rightLowWaveStep j
  have N1 : 1 ≤ N := by unfold N; exact_mod_cast n1
  have N0 := zero_lt_one.trans_le N1
  have huge' (x : ℝ) (h : 1/8192 ≤ x) : 2 ≤ N^x :=
    huge.trans (Real.rpow_le_rpow_of_exponent_le N1 h)
  have four : (4 : ℝ) ≤ N^(7/256 : ℝ) := calc
    _ ≤ N^(1/8192 : ℝ)*N^(1/8192 : ℝ) := by
      simpa only [show (2 : ℝ)*2=4 by norm_num] using mul_le_mul huge huge (by norm_num) (by positivity)
    _ = N^((1:ℝ)/8192+1/8192) := (Real.rpow_add N0 _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le N1 (by norm_num)
  have stepLo : N^(15/32 : ℝ) ≤ (v : ℝ) := by
    have hU := half_le_nat_floor_of_two_le (huge' (1/16) (by norm_num))
    have hC := half_le_nat_floor_of_two_le (huge' (111/256) (by norm_num))
    have lower : (N^(1/16 : ℝ)/2)*(N^(111/256 : ℝ)/2) ≤ (maximumStep n : ℝ) := by
      unfold maximumStep cutoffU cofactorCap
      push_cast
      exact mul_le_mul hU hC (by positivity) (by positivity)
    have step : maximumStep n < v := lt_of_not_ge (mem_filter.mp hj).2
    calc
      _ ≤ N^(7/256 : ℝ)*N^(15/32 : ℝ)/4 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ)<4)).mpr
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right four (by positivity)
      _ = (N^(1/16 : ℝ)/2)*(N^(111/256 : ℝ)/2) := by
        have e : N^(7/256 : ℝ)*N^(15/32 : ℝ)=N^(1/16 : ℝ)*N^(111/256 : ℝ) := by
          rw [← Real.rpow_add N0,← Real.rpow_add N0]
          congr 1 <;> norm_num
        rw [e]
        ring
      _ ≤ _ := lower.trans (by exact_mod_cast step.le)
  have prodN : (u : ℝ)*(v : ℝ) ≤ N^(1+4/8192 : ℝ) := by
    have bound : (u : ℝ)*(v : ℝ) ≤ (weilNearProductCap n : ℝ) := by exact_mod_cast prod
    calc
      _ ≤ 2*N^(1+3/8192 : ℝ) := by
        apply bound.trans
        unfold weilNearProductCap
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
      _ ≤ N^(1/8192 : ℝ)*N^(1+3/8192 : ℝ) := mul_le_mul_of_nonneg_right huge (by positivity)
      _ = _ := by rw [← Real.rpow_add N0]; congr 1 <;> norm_num
  have uBound {r s : ℝ} (vr : N^s ≤ (v : ℝ)) (exps : 1+4/8192 ≤ r+s) : (u : ℝ) ≤ N^r := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos N0 s)).mp
    calc
      _ ≤ (u : ℝ)*(v : ℝ) := mul_le_mul_of_nonneg_left vr (by positivity)
      _ ≤ _ := prodN.trans (by rw [← Real.rpow_add N0]; exact Real.rpow_le_rpow_of_exponent_le N1 exps)
  have uExt : u ≤ extendedWideStepCap n :=
    Nat.le_floor ((uBound stepLo (r := 9/16) (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le N1 (by norm_num)))
  have capProd : u*v ≤ expandedHyperbolaProductCap n := prod.trans <| by
    unfold weilNearProductCap expandedHyperbolaProductCap
    exact Nat.mul_le_mul_left _ (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le N1 (by norm_num)))
  have rest : remainingExpandedLow n u v := keep.2.2.2.1.1
  have wider : widerLowFarModulusCap n < v := by
    by_contra! h
    by_cases a : v ≤ expandedHighModulusCap n
    · exact rest.1 ⟨a,capProd⟩
    by_cases b : v ≤ shortLowModulusCap n
    · exact rest.2.1 ⟨uExt,lt_of_not_ge a,b,capProd⟩
    · exact rest.2.2 ⟨uExt,lt_of_not_ge b,h,capProd⟩
  have vPower : N^(535/1024 : ℝ) ≤ (v : ℝ) :=
    (Nat.lt_floor_add_one _).le.trans (by exact_mod_cast Nat.succ_le_of_lt wider)
  have uHalf : (u : ℝ) ≤ N^(1/2 : ℝ) := uBound vPower (by norm_num)
  have uv : u ≤ v := by
    have h : (u : ℝ) ≤ (v : ℝ) := uHalf.trans
      ((Real.rpow_le_rpow_of_exponent_le N1 (by norm_num)).trans vPower)
    exact_mod_cast h
  exact ⟨Nat.le_floor uHalf,uExt,wider,uv,prod⟩

theorem inner_low_near_second_eventually_zero :
    ∀ᶠ n : ℕ in atTop, innerLowSecondRamp n (innerLowNearProduct n)=0 := by
  have huge : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (n : ℝ)^(1/8192 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/8192)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop 1,huge] with n n1 large
  unfold innerLowSecondRamp
  refine sum_eq_zero fun i _ => sum_eq_zero fun j hj => ?_
  dsimp only
  apply if_neg
  rintro ⟨kept,_,prod,excluded⟩
  exact excluded (reverse_weil_full_extra_of_inner_low_near n1 large hj kept prod)

theorem inner_low_near_second_saving :
    saving (fun n => innerLowSecondRamp n (innerLowNearProduct n)) := by
  intro e e0
  obtain ⟨N,hN⟩ := eventually_atTop.mp inner_low_near_second_eventually_zero
  refine ⟨N,fun n hn _ => ?_⟩
  change ‖innerLowSecondRamp n (innerLowNearProduct n)‖ ≤ _
  rw [hN n hn,norm_zero]
  positivity

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_double_fourth_remainder -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def weilRemainingNearGroupGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  let g := u.gcd v
  g ∈ weilNearRowDivisors n v ∧ weilNearProductLower n j g < u ∧ u ≤ weilNearProductUpper n j g ∧
    weilRemainingNearRightRampFactor n v i.1

def weilRemainingNearRightRampKept (n : ℕ) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ weilNearRightRows n,
    leftPrimeWeight n i*rightLowWaveWeight j*
      (if weilRemainingNearGroupGate n i j ∧ weilNearLeftKept n (leftBilinearStep i) then
        (rightInverseRamp n (leftBilinearStep i) (rightLowWaveStep j) : ℂ) else 0)

private theorem adaptive_near_right_rows_sub_b13m135 (n : ℕ) : weilNearRightRows n ⊆ rightLowWaveItems n :=
  fun _ hj => long_right_low_subset n (mem_filter.mp hj).1

private theorem adaptive_near_upper_mul_le_b13m135 (n : ℕ) {j : RightLowWaveIndex} {g : ℕ} :
    weilNearProductUpper n j g*rightLowWaveStep j ≤ weilNearProductCap n := by
  calc
    _ ≤ (weilNearProductCap n/rightLowWaveStep j)*rightLowWaveStep j :=
      Nat.mul_le_mul_right _ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    _ ≤ _ := Nat.div_mul_le_self _ _

private theorem weil_remaining_near_right_ramp_broad_saving :
    saving (weilRemainingNearRightRampSlice weilNearRightRows weilNearProductLower weilNearProductUpper) := by
  apply weil_remaining_near_right_ramp_saving
  · intro n j hj
    exact ⟨adaptive_near_right_rows_sub_b13m135 n hj,long_right_low_step_le_power (mem_filter.mp hj).1,
      (mem_filter.mp hj).2.1,(mem_filter.mp hj).2.2.1⟩
  · intro n j hj g
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · intro n j hj g
    exact adaptive_near_upper_mul_le_b13m135 n

set_option maxHeartbeats 1200000 in
private theorem weil_remaining_near_right_ramp_broad_eq {n : ℕ} :
    weilRemainingNearRightRampSlice weilNearRightRows weilNearProductLower weilNearProductUpper n =
      ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ weilNearRightRows n,
        leftPrimeWeight n i*rightLowWaveWeight j*
        (if weilRemainingNearGroupGate n i j then (rightInverseRamp n (leftBilinearStep i) (rightLowWaveStep j) : ℂ)
          else 0) := by
  unfold weilRemainingNearRightRampSlice
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have ranges := mem_Icc.mp (bilateral_right_low_step_range (adaptive_near_right_rows_sub_b13m135 n hj))
  have n1 : 1 ≤ n := ranges.1.trans ranges.2
  have lower (g : ℕ) : leftMediumCap n ≤ weilNearProductLower n j g :=
    (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n1) (by norm_num))).trans
      (le_max_left _ _)
  rw [weil_remaining_near_right_ramp_row_eq_selected (upper := weilNearProductUpper n j) ranges.1 ranges.2 lower (fun _ => min_le_left _ _)]
  have items : weilRemainingNearRightRampRowItems n (rightLowWaveStep j) (weilNearProductLower n j) (weilNearProductUpper n j) =
      (bilateralLeftWaveItems n).filter (fun i => weilRemainingNearGroupGate n i j) := by
    ext i
    simp only [weilRemainingNearRightRampRowItems,mem_filter]
    rfl
  rw [items,sum_filter,mul_sum]
  refine sum_congr rfl fun i hi => ?_
  by_cases h : weilRemainingNearGroupGate n i j
  · simp only [if_pos h]
    rw [← mul_assoc,mul_comm (rightLowWaveWeight j) (leftPrimeWeight n i)]
  · simp only [if_neg h,mul_zero]

theorem weil_remaining_near_right_ramp_kept_saving : saving weilRemainingNearRightRampKept := by
  let F := weilRemainingNearRightRampSlice weilNearRightRows weilNearProductLower weilNearProductUpper
  let E := weilNearLeftCutFrom bilateralLeftWaveItems weilNearRightRows weilRemainingNearGroupGate
  have correction : saving E :=
    weil_near_left_cut_saving bilateralLeftWaveItems weilNearRightRows weilRemainingNearGroupGate
      (fun _ _ h => h) adaptive_near_right_rows_sub_b13m135
      (fun n i j h => (Nat.mul_le_mul_right _ h.2.2.1).trans (adaptive_near_upper_mul_le_b13m135 n))
  have balance (n : ℕ) : weilRemainingNearRightRampKept n = F n-E n := by
    unfold F E weilRemainingNearRightRampKept weilNearLeftCutFrom
    rw [weil_remaining_near_right_ramp_broad_eq,← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : weilRemainingNearGroupGate n i j <;> by_cases k : weilNearLeftKept n (leftBilinearStep i) <;>
      simp [h,k]
  have negCorrection : saving (fun n => -E n) := by
    intro ε ε0
    obtain ⟨N,hN⟩ := correction ε ε0
    exact ⟨N,fun n hn ev => by simpa only [norm_neg] using hN n hn ev⟩
  have S : saving (fun n => F n + (-E n)) := saving_sum_two weil_remaining_near_right_ramp_broad_saving negCorrection
  have h : (fun n => F n + (-E n)) = weilRemainingNearRightRampKept := funext fun n => by
    rw [← sub_eq_add_neg,balance]
  rw [h] at S
  exact S

def weilRemainingNearExtra (n : ℕ) (i : ℕ × ℕ) (v : ℕ) : Prop :=
  let u := leftBilinearStep i
  widerLowFarModulusCap n < v ∧ u ≤ extendedWideStepCap n ∧ u ≤ v ∧ u*v ≤ weilNearProductCap n ∧
    weilRemainingNearRightRampFactor n v i.1

set_option maxHeartbeats 1200000 in
theorem weil_remaining_near_product_mask_iff {n : ℕ} {i : ℕ × ℕ} {j : RightLowWaveIndex}
    (hj : j ∈ longRightLowItems n) :
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    (j ∈ weilNearRightRows n ∧ weilRemainingNearGroupGate n i j ∧ weilNearLeftKept n u) ↔
      (u ≤ expandedWideStepCap n ∧ ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧
        farInnerThinGate n u v ∧ retainedLowTargetMask n u v ∧ stepWithoutLargeSquare n u ∧
        weilRemainingNearExtra n i v ∧ u.gcd v ∣ n) := by
  dsimp only
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  have vr := mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))
  have v0 : 0 < v := vr.1
  have n0 : 0 < n := vr.1.trans vr.2
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n0
  have cutoff : thinHighGcdCap n ≤ cutoffU n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have cof : 1 ≤ cofactorCap n := Nat.le_floor (Real.one_le_rpow nR (by norm_num))
  have gCap : thinHighGcdCap n ≤ maximumStep n := cutoff.trans (by
    change cutoffU n ≤ cutoffU n*cofactorCap n
    simpa only [mul_one] using Nat.mul_le_mul_left (cutoffU n) cof)
  have C1 : expandedHighModulusCap n ≤ widerLowFarModulusCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have C2 : shortLowModulusCap n ≤ widerLowFarModulusCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have rest (h : widerLowFarModulusCap n < v) : remainingExpandedLow n u v := by
    refine ⟨?_,?_,?_⟩
    · exact fun small => (not_le_of_gt (C1.trans_lt h)) small.1
    · exact fun mid => (not_le_of_gt (C2.trans_lt h)) mid.2.2.1
    · exact fun wide => (not_le_of_gt h) wide.2.2.1
  have dl : weilNearProductLower n j (u.gcd v) < u ↔
      ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < u ∧ maximumStep n^2 < u*v ∧
      thinHighProductCap n < u*v ∧ highFarStripProductCap n < u*v := by
    simp only [weilNearProductLower, v, max_lt_iff, Nat.div_lt_iff_lt_mul v0]
  have du : u ≤ weilNearProductUpper n j (u.gcd v) ↔
      u ≤ extendedWideStepCap n ∧ u ≤ expandedWideStepCap n ∧ u ≤ v ∧ u*v ≤ weilNearProductCap n := by
    simp only [weilNearProductUpper, v, le_min_iff, Nat.le_div_iff_mul_le v0]
  have gg : u.gcd v ∈ weilNearRowDivisors n v ↔ u.gcd v ∣ n ∧ u.gcd v ≤ thinHighGcdCap n := by
    rw [weilNearRowDivisors,mem_filter,Nat.mem_divisors]
    exact ⟨fun h => ⟨h.1.1,h.2.2⟩,
      fun h => ⟨⟨h.1,n0.ne'⟩,Nat.gcd_dvd_right _ _,h.2⟩⟩
  have rightMask : j ∈ weilNearRightRows n ↔
      widerLowFarModulusCap n < v ∧ v.gcd n ≤ sparseTargetDivisorCap n ∧ v.gcd n ≤ targetDivisorCap n := by
    unfold weilNearRightRows
    simp only [mem_filter,hj,true_and]
    rfl
  change (j ∈ weilNearRightRows n ∧
      ((u.gcd v ∈ weilNearRowDivisors n v) ∧
        weilNearProductLower n j (u.gcd v) < u ∧ u ≤ weilNearProductUpper n j (u.gcd v) ∧
        weilRemainingNearRightRampFactor n v i.1) ∧ weilNearLeftKept n u) ↔ _
  rw [dl,du,gg,rightMask]
  simp only [weilNearLeftKept,farInnerThinGate,boundedOuterLeftKeptGate,farInnerGate,prefixStepGate,
    retainedLowTargetMask,targetDivisorKept,weilRemainingNearExtra]
  constructor
  · rintro ⟨⟨wide,sparse,target⟩,⟨⟨dvd,gcd⟩,⟨geom,mp,tp,fp⟩,⟨ext,cap,uv,p⟩,factor⟩,left,square⟩
    exact ⟨cap,geom,⟨⟨⟨⟨mp,gcd.trans gCap⟩,fp⟩,tp,gcd,target⟩,left⟩,⟨rest wide,sparse⟩,square,
      ⟨wide,ext,uv,p,factor⟩,dvd⟩
  · rintro ⟨cap,geom,⟨⟨⟨⟨mp,_⟩,fp⟩,tp,gcd,target⟩,left⟩,⟨_,sparse⟩,square,
      ⟨wide,ext,uv,p,factor⟩,dvd⟩
    exact ⟨⟨wide,sparse,target⟩,⟨⟨dvd,gcd⟩,⟨geom,mp,tp,fp⟩,⟨ext,cap,uv,p⟩,factor⟩,left,square⟩

set_option maxHeartbeats 1500000 in
theorem inner_low_near_first_eq_remaining_near (n : ℕ)
    (huge : (2 : ℝ) ≤ (n : ℝ)^(1/8192 : ℝ)) :
    innerLowFirstRamp n (innerLowNearProduct n)=weilRemainingNearRightRampKept n := by
  unfold innerLowFirstRamp weilRemainingNearRightRampKept weilNearRightRows
  refine sum_congr rfl fun i hi => ?_
  rw [sum_filter]
  refine sum_congr rfl fun j hj => ?_
  dsimp only
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  let go := widerLowFarModulusCap n < v ∧ v.gcd n ≤ sparseTargetDivisorCap n ∧ v.gcd n ≤ targetDivisorCap n
  let cut := weilRemainingNearGroupGate n i j ∧ weilNearLeftKept n u
  let W := leftPrimeWeight n i*rightLowWaveWeight j
  let a := (rightInverseRamp n u v : ℂ)
  let box := symmetricLowPairKept n u v ∧ u.gcd v ∣ n ∧ innerLowNearProduct n i j ∧
    ¬(weilNearExtra n i v ∨ weilAdaptiveExtra n i v)
  have vr := mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))
  have n1 : 1 ≤ n := vr.1.trans vr.2
  have iRange := (mem_product.mp (mem_filter.mp (mem_filter.mp hi).1).1).1
  have factor := weil_remaining_near_right_ramp_factor_iff (v := v) n1 iRange
  have bib : go ∧ cut ↔ symmetricLowPairKept n u v ∧ u.gcd v ∣ n ∧ weilRemainingNearExtra n i v := by
    have h := weil_remaining_near_product_mask_iff (i := i) hj
    dsimp only at h
    constructor
    · rintro ⟨r,l,c⟩
      have jRows : j ∈ weilNearRightRows n := mem_filter.mpr ⟨hj,r⟩
      obtain ⟨cap,geo,gate,target,square,extra,dvd⟩ := h.mp ⟨jRows,l,c⟩
      exact ⟨⟨cap,geo,gate,target,square⟩,dvd,extra⟩
    · rintro ⟨⟨cap,geo,gate,target,square⟩,dvd,extra⟩
      obtain ⟨jRows,l,c⟩ := h.mpr ⟨cap,geo,gate,target,square,extra,dvd⟩
      exact ⟨(mem_filter.mp jRows).2,l,c⟩
  have mask : go ∧ cut ↔ box := by
    rw [bib]
    constructor
    · rintro ⟨kept,dvd,wide,ext,uv,prod,selected⟩
      have f := factor.mp selected
      refine ⟨kept,dvd,prod,?_⟩
      rintro (old | adaptive)
      · exact f.1.not_ge old.2.2.2.2
      · exact f.2 adaptive.2.2.2.2
    · rintro ⟨kept,dvd,prod,excluded⟩
      obtain ⟨_,ext,wide,uv,_⟩ := reverse_weil_full_extra_of_inner_low_near n1 huge hj kept prod
      have aLarge : primeHyperbolaFactorFloor n 32 < i.1 := lt_of_not_ge (fun h =>
        excluded (Or.inl ⟨wide,ext,uv,prod,h⟩))
      have noAdaptive : ¬weilAdaptiveRightRampFactor n v i.1 :=
        fun h => excluded (Or.inr ⟨wide,ext,uv,prod,h⟩)
      exact ⟨kept,dvd,wide,ext,uv,prod,factor.mpr ⟨aLarge,noAdaptive⟩⟩
  by_cases h : go ∧ cut
  · have yes : box := mask.mp h
    dsimp only [box,u,v] at yes
    rw [if_pos yes,if_pos h.1,if_pos h.2]
  · have no : ¬box := fun p => h (mask.mpr p)
    dsimp only [box,u,v] at no
    rw [if_neg no]
    by_cases right : go
    · rw [if_pos right,if_neg (fun left : cut => h ⟨right,left⟩),mul_zero]
    · rw [if_neg right]

theorem inner_low_near_first_saving : saving (fun n => innerLowFirstRamp n (innerLowNearProduct n)) := by
  intro e e0
  obtain ⟨N,hN⟩ := weil_remaining_near_right_ramp_kept_saving e e0
  have huge : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ (n : ℝ)^(1/8192 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/8192)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp huge
  refine ⟨max N M,fun n hn even => ?_⟩
  change ‖innerLowFirstRamp n (innerLowNearProduct n)‖ ≤ _
  rw [inner_low_near_first_eq_remaining_near n (hM n ((le_max_right ..).trans hn))]
  exact hN n ((le_max_left ..).trans hn) even


end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_far_count -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def innerLowFarGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  symmetricLowPairKept n u v ∧ u.gcd v ∣ n ∧ ¬innerLowNearProduct n i j

def innerLowFarWeighted (n : ℕ) (f : ℕ → ℕ → ℂ) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ longRightLowItems n,
    if innerLowFarGate n i j then
      leftPrimeWeight n i*rightLowWaveWeight j*f (leftBilinearStep i) (rightLowWaveStep j)
    else 0

def innerLowFarCountDiscrepancy (n : ℕ) : ℂ :=
  innerLowFarWeighted n fun u v =>
    ((progressionPairSolutions n u v 0 (n/u) 0 (n/v)).card : ℂ)-
      ((u.gcd v : ℝ)*((n : ℝ)/((u : ℝ)*(v : ℝ))) : ℂ)

def innerLowFarBoundary (n : ℕ) : ℂ :=
  innerLowFarWeighted n fun u v =>
    ((u.gcd v : ℝ)*(1/(2*(u : ℝ))+1/(2*(v : ℝ))) : ℂ)

set_option maxHeartbeats 1800000 in
theorem inner_low_far_eq_count_and_boundary (n : ℕ) :
    innerLowFirstRamp n (fun i j => ¬innerLowNearProduct n i j)+
      innerLowSecondRamp n (fun i j => ¬innerLowNearProduct n i j) =
      innerLowFarCountDiscrepancy n+innerLowFarBoundary n := by
  unfold innerLowFirstRamp innerLowSecondRamp innerLowFarCountDiscrepancy innerLowFarBoundary
    innerLowFarWeighted
  rw [← sum_add_distrib,← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_add_distrib,← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  have u0 : 0 < u := (mem_Icc.mp (bilateral_left_step_range hi)).1
  have vr := mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))
  have v0 : 0 < v := vr.1
  have n0 : 0 < n := vr.1.trans vr.2
  dsimp only
  by_cases far : innerLowFarGate n i j
  · have phase₁ : ¬(weilNearExtra n i v ∨ weilAdaptiveExtra n i v) := fun h =>
      h.elim (fun h₁ => far.2.2 h₁.2.2.2.1) (fun h₂ => far.2.2 h₂.2.2.2.1)
    have phase₂ : ¬reverseWeilFullExtra n u v := fun h => far.2.2 h.2.2.2.2
    have h₁ := show symmetricLowPairKept n u v ∧ u.gcd v ∣ n ∧ ¬innerLowNearProduct n i j ∧
        ¬(weilNearExtra n i v ∨ weilAdaptiveExtra n i v) from ⟨far.1,far.2.1,far.2.2,phase₁⟩
    have h₂ := show symmetricLowPairKept n u v ∧ u.gcd v ∣ n ∧ ¬innerLowNearProduct n i j ∧
        ¬reverseWeilFullExtra n u v from ⟨far.1,far.2.1,far.2.2,phase₂⟩
    dsimp only [u,v] at h₁ h₂
    rw [if_pos h₁,if_pos h₂,if_pos far,if_pos far]
    have mass := full_progression_pair_count_eq_centered_ramps (n := n) (p := 0) u0 v0
    have cof : u.gcd v ∣ n ∧ v*0<n := ⟨far.2.1,by simpa only [Nat.mul_zero] using n0⟩
    rw [symmetric_count_main_eq_unreduced u0 v0,if_pos cof,symmetric_low_residue_decomposes n0 far.2.1] at mass
    have massC := congrArg Complex.ofReal mass
    push_cast at massC
    dsimp only [u,v] at massC
    rw [massC]
    push_cast
    ring
  · have h₁ : ¬(symmetricLowPairKept n u v ∧ u.gcd v ∣ n ∧ ¬innerLowNearProduct n i j ∧
        ¬(weilNearExtra n i v ∨ weilAdaptiveExtra n i v)) := fun h => far ⟨h.1,h.2.1,h.2.2.1⟩
    have h₂ : ¬(symmetricLowPairKept n u v ∧ u.gcd v ∣ n ∧ ¬innerLowNearProduct n i j ∧
        ¬reverseWeilFullExtra n u v) := fun h => far ⟨h.1,h.2.1,h.2.2.1⟩
    dsimp only [u,v] at h₁ h₂
    simp only [if_neg h₁,if_neg h₂,if_neg far]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_far_boundary -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

private theorem inner_low_weighted_reciprocal_mass {ι : Type*} (F : Finset ι)
    (step : ι → ℕ) (w : ι → ℂ) {n : ℕ} {W : ℝ} (n1 : 1 ≤ n) (W0 : 0 ≤ W)
    (steps : ∀ i ∈ F, step i ∈ Icc 1 n)
    (mass : ∀ m ∈ Icc 1 n, (∑ i ∈ F.filter (fun i => step i=m), ‖w i‖) ≤ W) :
    (∑ i ∈ F, ‖w i‖*(1/(step i : ℝ))) ≤ W*logBudget n := by
  apply (sum_norm_mul_le_of_step_mass F step w (fun m => 1/(m : ℝ)) steps
    (fun _ _ => by positivity) mass).trans
  apply mul_le_mul_of_nonneg_left _ W0
  calc
    _ = (harmonic n : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    _ ≤ 1+Real.log n := by exact_mod_cast harmonic_le_one_add_log n
    _ ≤ _ := by
      unfold logBudget
      exact add_le_add (le_refl _) (Real.log_le_log (by exact_mod_cast n1) (by linarith))

set_option maxHeartbeats 1800000 in
theorem inner_low_far_boundary_saving : saving innerLowFarBoundary := by
  apply saving_of_weil_near_growth _ 2 (by norm_num)
  intro n n1 T T1 divs
  let X := expandedWideStepCap n
  let D := (thinHighGcdCap n : ℝ)
  let u := leftBilinearStep
  let v := rightLowWaveStep
  let a := leftPrimeWeight n
  let b := rightLowWaveWeight
  let L := logBudget n
  let W := T^3*L
  let I := (bilateralLeftWaveItems n).filter (fun i => u i ≤ X)
  let J := longRightLowItems n
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have nR0 := zero_lt_one.trans_le nR
  have D0 : 0 ≤ D := by unfold D; positivity
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have W0 : 0 ≤ W := by unfold W; positivity
  have XN : X ≤ n := expanded_wide_step_le n1
  have IX (i : ℕ × ℕ) (hi : i ∈ I) : u i ∈ Icc 1 X :=
    mem_Icc.mpr ⟨(mem_Icc.mp (bilateral_left_step_range (mem_filter.mp hi).1)).1,(mem_filter.mp hi).2⟩
  have JX (j : RightLowWaveIndex) (hj : j ∈ J) : v j ∈ Icc 1 X :=
    mem_Icc.mpr ⟨(mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))).1,
      long_right_low_step_within_expanded n1 hj⟩
  have divN (m : ℕ) (hm : m ≤ n) : (m.divisors.card : ℝ) ≤ T := by
    apply divs m (hm.trans ?_)
    have p : n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
    omega
  have lm := prime_left_mass_of_subset (filter_subset (fun i => u i ≤ X) (bilateralLeftWaveItems n)) T1 divN
  have rm := long_right_low_step_mass T1 divN
  have massU : (∑ i ∈ I, ‖a i‖) ≤ W*(X : ℝ) :=
    sum_norm_le_of_step_mass I u a IX (fun m hm => lm m (Icc_subset_Icc_right XN hm))
  have massV : (∑ j ∈ J, ‖b j‖) ≤ W*(X : ℝ) :=
    sum_norm_le_of_step_mass J v b JX (fun m hm => rm m (Icc_subset_Icc_right XN hm))
  have recipU : (∑ i ∈ I, ‖a i‖*(1/(u i : ℝ))) ≤ W*L :=
    inner_low_weighted_reciprocal_mass I u a n1 W0
      (fun i hi => Icc_subset_Icc_right XN (IX i hi)) lm
  have recipV : (∑ j ∈ J, ‖b j‖*(1/(v j : ℝ))) ≤ W*L :=
    inner_low_weighted_reciprocal_mass J v b n1 W0
      (fun j hj => Icc_subset_Icc_right XN (JX j hj)) rm
  let boundary (i : ℕ × ℕ) (j : RightLowWaveIndex) : ℝ :=
    ((u i).gcd (v j) : ℝ)*(1/(2*(u i : ℝ))+1/(2*(v j : ℝ)))
  let f (i : ℕ × ℕ) (j : RightLowWaveIndex) : ℂ :=
    if innerLowFarGate n i j then a i*b j*(boundary i j : ℂ) else 0
  have main : innerLowFarBoundary n = ∑ i ∈ I, ∑ j ∈ J, f i j := by
    unfold innerLowFarBoundary innerLowFarWeighted I J f boundary a b u v
    rw [sum_filter]
    refine sum_congr rfl fun i _ => ?_
    by_cases hi : leftBilinearStep i ≤ X
    · rw [if_pos hi]
      refine sum_congr rfl fun j _ => ?_
      by_cases h : innerLowFarGate n i j
      · rw [if_pos h,if_pos h]
        push_cast <;> first | rfl | ring
      · rw [if_neg h,if_neg h]
    · rw [if_neg hi]
      exact sum_eq_zero fun j _ => if_neg (fun h => hi h.1.1)
  have point (i : ℕ × ℕ) (hi : i ∈ I) (j : RightLowWaveIndex) (hj : j ∈ J) :
      ‖f i j‖ ≤ D*(‖a i‖*(1/(u i : ℝ))*‖b j‖+‖a i‖*(‖b j‖*(1/(v j : ℝ)))) := by
    by_cases kept : innerLowFarGate n i j
    · have gcd : ((u i).gcd (v j) : ℝ) ≤ D := by
        unfold D
        exact_mod_cast kept.1.2.2.1.1.2.2.1
      have u0 : (0 : ℝ) < u i := by exact_mod_cast (mem_Icc.mp (IX i hi)).1
      have v0 : (0 : ℝ) < v j := by exact_mod_cast (mem_Icc.mp (JX j hj)).1
      have boundaryLe : boundary i j ≤ D*(1/(u i : ℝ)+1/(v j : ℝ)) := by
        unfold boundary
        exact mul_le_mul gcd
          (add_le_add (div_le_div_of_nonneg_left zero_le_one u0 (by linarith only [u0]))
            (div_le_div_of_nonneg_left zero_le_one v0 (by linarith only [v0]))) (by positivity) D0
      unfold f
      rw [if_pos kept,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by unfold boundary; positivity)]
      exact (mul_le_mul_of_nonneg_left boundaryLe (by positivity)).trans_eq (by ring)
    · unfold f
      rw [if_neg kept,norm_zero]
      positivity
  have sumBound :
      (∑ i ∈ I, ∑ j ∈ J, D*(‖a i‖*(1/(u i : ℝ))*‖b j‖+
        ‖a i‖*(‖b j‖*(1/(v j : ℝ))))) ≤ 2*D*(X : ℝ)*W^2*L := by
    let R₁ := ∑ i ∈ I, ‖a i‖*(1/(u i : ℝ))
    let R₂ := ∑ j ∈ J, ‖b j‖*(1/(v j : ℝ))
    let M₁ := ∑ i ∈ I, ‖a i‖
    let M₂ := ∑ j ∈ J, ‖b j‖
    have sep (a' : ℕ × ℕ → ℝ) (b' : RightLowWaveIndex → ℝ) :
        (∑ i ∈ I, ∑ j ∈ J, D*(a' i*b' j)) =
          D*((∑ i ∈ I,a' i)*(∑ j ∈ J,b' j)) := by
      conv_rhs => rw [sum_mul,mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum,mul_sum]
    calc
      _ = D*(R₁*M₂+M₁*R₂) := by
        simp only [mul_add,sum_add_distrib]
        rw [sep (fun i => ‖a i‖*(1/(u i : ℝ))) (fun j => ‖b j‖),
          sep (fun i => ‖a i‖) (fun j => ‖b j‖*(1/(v j : ℝ)))]
      _ ≤ D*((W*L)*(W*(X : ℝ))+(W*(X : ℝ))*(W*L)) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul recipU massV (by unfold M₂; positivity) (by positivity))
          (mul_le_mul massU recipV (by unfold R₂; positivity) (by positivity))) D0
      _ = _ := by ring
  have power : D*(X : ℝ) ≤ (n : ℝ)^(8191/8192 : ℝ) := calc
    _ ≤ (n : ℝ)^(1/4096 : ℝ)*(n : ℝ)^(511/768 : ℝ) :=
      mul_le_mul (Nat.floor_le (by positivity)) (Nat.floor_le (by positivity)) (by positivity) (by positivity)
    _ = (n : ℝ)^(1/4096+511/768 : ℝ) := (Real.rpow_add nR0 _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le nR (by norm_num)
  rw [main]
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ‖f i j‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ _ := sum_le_sum (fun i hi => sum_le_sum (fun j hj => point i hi j hj))
    _ ≤ _ := sumBound
    _ = 2*(D*(X : ℝ))*T^6*L^3 := by unfold W; ring
    _ ≤ 2*(n : ℝ)^(8191/8192 : ℝ)*T^9*L^5 := by
      have pT : T^6 ≤ T^9 := pow_le_pow_right₀ T1 (by decide)
      have pL : L^3 ≤ L^5 := pow_le_pow_right₀ (one_le_logBudget n) (by decide)
      gcongr
    _ = _ := rfl

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_post_noon_inner_low -/
section

namespace GoldbachTypeII13

open DyadicMixedB4EnergyTail

noncomputable section

theorem inner_low_near_and_half_endpoints_saving :
    saving (fun n => (weilNearLowInterior n - reverseWeilCutOnOriginal n) -
      innerLowFarCountDiscrepancy n) := by
  let A := weilAdaptiveRightRampKept
  let B := smallReverseWeilOriginalCut
  let C := fun n => innerLowFirstRamp n (innerLowNearProduct n)
  let D := fun n => innerLowSecondRamp n (innerLowNearProduct n)
  let E := innerLowFarBoundary
  have ab : saving (fun n => A n + B n) :=
    saving_sum_two weil_adaptive_right_ramp_kept_saving small_reverse_weil_original_cut_saving
  have cd : saving (fun n => C n + D n) :=
    saving_sum_two inner_low_near_first_saving inner_low_near_second_saving
  have near : saving (fun n => (A n + B n) + (C n + D n) + E n) :=
    saving_sum_two (saving_sum_two ab cd) inner_low_far_boundary_saving
  have eq (n : ℕ) : (weilNearLowInterior n - reverseWeilCutOnOriginal n) -
      innerLowFarCountDiscrepancy n = (A n + B n) + (C n + D n) + E n := by
    have start : weilNearLowInterior n - reverseWeilCutOnOriginal n =
        adaptiveInnerLowRemainder n + (A n + B n) := by
      unfold adaptiveInnerLowRemainder A B
      rw [weil_adaptive_low_interior_eq_sub, ← reverse_weil_full_cut_eq_on_original,
        reverse_weil_full_selected_eq_add, reverse_weil_cut_eq_on_original]
      ring
    rw [start, adaptive_inner_low_remainder_eq_ramps,
      innerLowFirstRamp_split n (innerLowNearProduct n), innerLowSecondRamp_split n (innerLowNearProduct n)]
    have join (x₁ x₂ y₁ y₂ z : ℂ) : (x₁+x₂+(y₁+y₂))+z = (x₂+y₂)+((x₁+y₁)+z) := by abel
    rw [join, inner_low_far_eq_count_and_boundary]
    unfold C D E
    abel
  rw [funext eq]
  exact near

end

end GoldbachTypeII13

end

end B13InnerLowNearAndEndpointSavingProof

set_option maxHeartbeats 4000000 in
theorem Conjectures.Goldbach.B13InnerLowNearAndEndpointSaving :
let Λ := ArithmeticFunction.vonMangoldt
    let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
    let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊
    let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊
    let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
    let M := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
    let PL := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 96 : ℝ)⌋₊
    let K := fun n : ℕ => ⌊(n : ℝ) ^ (33 / 64 : ℝ)⌋₊
    let Lcap := fun n : ℕ => ⌊(n : ℝ) ^ (3 / 10 : ℝ)⌋₊
    let stepCap := fun n : ℕ => U n * ⌊(n : ℝ) ^ (111 / 256 : ℝ)⌋₊
    let FPrime := fun (P m : ℕ) => ∑ x ∈ Nat.divisorsAntidiagonal m,
      (M x.1 - (if x.1 ≤ P then M x.1 else 0)) *
        @ite ℝ (P<x.2 ∧ x.2.Prime)
          (@instDecidableAnd (P<x.2) x.2.Prime
            (Nat.decLt P x.2) (Classical.propDecidable _))
          (Λ x.2) 0
    let u := fun i : ℕ × ℕ => i.1 * i.2
    let vl := fun j : (Σ _ : ℕ, ℕ) => j.2 * j.1
    let X := fun n : ℕ => (((Finset.Ioc (U n) (B₁ n) ×ˢ Finset.Icc 1 n).filter (fun i => Lcap n < u i)).filter (fun i => u i ≤ n))
    let Y := fun n : ℕ => (Finset.Ioc (U n) (min n (K n))).sigma (fun b => Finset.Icc 1 (min (U n) (n / b)))
    let w := fun (n : ℕ) (i : ℕ × ℕ) => ((∑ d ∈ (Nat.divisors i.1).filter (fun d => U n < d), μ d : ℝ) : ℂ) * (FPrime (PL n) i.2 : ℂ)
    let ramp := fun (m : ℕ) (r : ℤ) => ((m : ℝ)-1)/(2*(m : ℝ))-((r%(m : ℤ) : ℤ) : ℝ)/(m : ℝ)
    let symmetric := fun (n u v p : ℕ) =>
      let d := u.gcd v
      let g := u/d
      let h := v/d
      let z : ℤ := (n/d : ℕ)
      if d ∣ n ∧ v*p<n then
        ramp h (z*Nat.gcdA g h-1)+ramp g (z*Nat.gcdA h g-p-1)
      else 0
    let inverseRamp := fun (n u v : ℕ) =>
      let d := u.gcd v
      ramp (v/d) ((((n/d : ℕ) : ℤ)*Nat.gcdA (u/d) (v/d))-1)
    let expandedCap := fun n : ℕ => ⌊(n : ℝ)^(511/768 : ℝ)⌋₊
    let productCap := fun n : ℕ => 2*⌊(n : ℝ)^(4097/4096 : ℝ)⌋₊
    let originalInside := fun (n u v : ℕ) =>
      (((stepCap n^2 < u*v ∧ u.gcd v ≤ stepCap n) ∧ productCap n < u*v) ∧
        ⌊(n : ℝ)^(8191/8192 : ℝ)⌋₊ < u*v ∧ u.gcd v ≤ ⌊(n : ℝ)^(1/4096 : ℝ)⌋₊ ∧
        v.gcd n ≤ ⌊(n : ℝ)^(1/128 : ℝ)⌋₊) ∧ u.gcd n ≤ ⌊(n : ℝ)^(1/2048 : ℝ)⌋₊
    let moved := fun (n u v : ℕ) => v ≤ ⌊(n : ℝ)^(515/1024 : ℝ)⌋₊ ∧ u*v ≤ 2*⌊(n : ℝ)^(513/512 : ℝ)⌋₊
    let extended := fun n : ℕ => ⌊(n : ℝ)^(21/32 : ℝ)⌋₊
    let modulusLow := fun n : ℕ => ⌊(n : ℝ)^(515/1024 : ℝ)⌋₊
    let modulusMiddle := fun n : ℕ => ⌊(n : ℝ)^(133/256 : ℝ)⌋₊
    let modulusWider := fun n : ℕ => ⌊(n : ℝ)^(535/1024 : ℝ)⌋₊
    let widerProduct := fun n : ℕ => 2*⌊(n : ℝ)^(513/512 : ℝ)⌋₊
    let belowTarget := fun (n v : ℕ) => v.gcd n ≤ ⌊(n : ℝ)^(1/2048 : ℝ)⌋₊
    let between := fun (lo hi : ℕ → ℕ) (n u v : ℕ) =>
      u ≤ extended n ∧ lo n < v ∧ v ≤ hi n ∧ u*v ≤ widerProduct n
    let largeSquares := fun n : ℕ => (Finset.Icc 1 n).filter
      (fun m => ∃ h ∈ Finset.Ioc ⌊(n : ℝ)^(1/768 : ℝ)⌋₊ n, h^2 ∣ m)
    let squareFree := fun (n m : ℕ) => m ∉ largeSquares n
    let keepLow := fun (n u v : ℕ) =>
      (¬moved n u v ∧ ¬between modulusLow modulusMiddle n u v ∧ ¬between modulusMiddle modulusWider n u v) ∧
        belowTarget n v
    let longLow := fun n : ℕ =>
      @Finset.filter (Σ _ : ℕ, ℕ) (fun j => ¬vl j ≤ stepCap n)
        (fun j => @instDecidableNot (vl j ≤ stepCap n) (Classical.propDecidable _))
        ((Y n).filter (fun j => j.1.Prime ∧ ¬j.1 ∣ n))
    let narrowProduct := fun n : ℕ => 2*⌊(n : ℝ)^(1+3/8192 : ℝ)⌋₊
    let near := fun (n : ℕ) (i : ℕ × ℕ) (v : ℕ) =>
      modulusWider n < v ∧ u i ≤ extended n ∧ u i ≤ v ∧ u i*v ≤ narrowProduct n ∧
        i.1 ≤ ⌊(n : ℝ)^((32 : ℝ)/256)⌋₊
    let lowKept := fun (n g h : ℕ) =>
      g ≤ expandedCap n ∧ ⌊(n : ℝ)^(27/64 : ℝ)⌋₊ < g ∧
        originalInside n g h ∧ keepLow n g h ∧ squareFree n g
    let insideLow := fun n : ℕ =>
      ∑ i ∈ X n, ∑ j ∈ longLow n,
        @ite ℂ (lowKept n (u i) (vl j)) (Classical.propDecidable _)
          (w n i*((-(μ j.2 : ℂ))*(Λ j.1 : ℂ))*
            (@ite ℂ (near n i (vl j) ∧ (u i).gcd (vl j) ∣ n)
              (@instDecidableAnd (near n i (vl j)) ((u i).gcd (vl j) ∣ n)
                (Classical.propDecidable _) (((u i).gcd (vl j)).decidable_dvd n))
              (inverseRamp n (vl j) (u i) : ℂ) (symmetric n (u i) (vl j) 0 : ℂ))) 0
    let reverseExtra := fun (n g h q : ℕ) =>
      g ≤ ⌊(n : ℝ)^(1/2 : ℝ)⌋₊ ∧ g ≤ extended n ∧ modulusWider n < h ∧ g ≤ h ∧
        g*h ≤ narrowProduct n ∧ ⌊(n : ℝ)^(1/24 : ℝ)⌋₊ < q
    let reverseCorrection := fun n : ℕ =>
      ∑ i ∈ X n, ∑ j ∈ longLow n,
        @ite ℂ (lowKept n (u i) (vl j) ∧ reverseExtra n (u i) (vl j) j.2 ∧ (u i).gcd (vl j) ∣ n)
          (Classical.propDecidable _) (w n i*((-(μ j.2 : ℂ))*(Λ j.1 : ℂ))*
            (inverseRamp n (vl j) (u i) : ℂ)) 0
    let unrestrictedCount := fun (n g h : ℕ) =>
      ((Finset.Ioc 0 (n/g) ×ˢ Finset.Ioc 0 (n/h)).filter
        (fun p => g*p.1+h*p.2 = n)).card
    let farRaw := fun n : ℕ =>
      ∑ i ∈ X n, ∑ j ∈ longLow n,
        let g := u i
        let h := vl j
        @ite ℂ (lowKept n g h ∧ g.gcd h ∣ n ∧ ¬(g*h ≤ narrowProduct n)) (Classical.propDecidable _)
          (w n i*((-(μ j.2 : ℂ))*(Λ j.1 : ℂ))*
            ((unrestrictedCount n g h : ℂ) - ((g.gcd h : ℝ)*((n : ℝ)/((g : ℝ)*(h : ℝ))) : ℂ))) 0
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ‖(insideLow n-reverseCorrection n)-farRaw n‖ ≤ e*(n : ℝ) := by
  exact B13InnerLowNearAndEndpointSavingProof.GoldbachTypeII13.inner_low_near_and_half_endpoints_saving
