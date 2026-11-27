import Mathlib

/-!
B13 Type-II estimates for the first and third Vaughan bands.

Part of the circle-method framework is adapted from goldbach-proofs #2489
(xuanyou-li, 653f53ba55eea5e3ce3bd067ece0d7e30e37cba2) and #2468
(3d9be84b446f4e30f46b52e1c83dc7e49e4535d9). The latter draws on
openai/math GeometricCharacterBound (3344da59991ed94f9ba711217b29c1d760badfa6).
Some arithmetic and character estimates draw on kimihiro64/bombieri-vinogradov
(7a1748306e026825ed6a5555516cc2f28989b2ac). These sources are under Apache-2.0.
-/

/- Prime inverse moment -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Reciprocal fibre factorization -/
section

namespace B13BoundedStepProductSavingProof

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
        (add_le_add) (mul_le_mul_of_nonneg_left xy (abs_nonneg _))
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

end B13BoundedStepProductSavingProof

end

/- Reciprocal fibre budget -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Reciprocal fourth moment -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- L goldbach frontier type2 b1 b3 -/
section

namespace B13BoundedStepProductSavingProof

section

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

end
end DyadicMixedB4Geometric

end

section

namespace DyadicMixedB4ArcGeometry
open Finset MeasureTheory DyadicMixedB4Geometric
noncomputable section

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

namespace BombieriVinogradov.LargeSieve

end BombieriVinogradov.LargeSieve

namespace BombieriVinogradov.LargeSieve

end BombieriVinogradov.LargeSieve

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

end BombieriVinogradov.LargeSieve

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

end BombieriVinogradov.LargeSieve

end

section

open Complex Finset Real

namespace BombieriVinogradov.LargeSieve

noncomputable section

end
end BombieriVinogradov.LargeSieve

end

section

noncomputable section

open Complex Finset Real
open scoped BigOperators ComplexConjugate

namespace BombieriVinogradov.LargeSieve

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

end
end DyadicMixedB4RamanujanCharacters

end

section

open Finset DyadicMixedB4GaussLift DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open BombieriVinogradov.LargeSieve DyadicMixedB4Ramanujan DyadicMixedB4RamanujanCharacters

namespace DyadicMixedB4RamanujanUnits

noncomputable section

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
def cutoffB (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

def cofactorCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (111 / 256 : ℝ)⌋₊
def maximumStep (n : ℕ) : ℕ := cutoffU n * cofactorCap n

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
end B13BoundedStepProductSavingProof

namespace B13BoundedStepProductSavingProof

open Finset MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Arithmetic DyadicMixedB4Scale DyadicMixedB4HighAtoms
open DyadicMixedB4PairIntegral DyadicMixedB4Finish

noncomputable section

def upperCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊

def splitCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (7 / 12 : ℝ)⌋₊

def saving (f : ℕ → ℂ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖f n‖ ≤ e * (n : ℝ)

end

end B13BoundedStepProductSavingProof

namespace B13BoundedStepProductSavingProof

open Finset MeasureTheory ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4LowBand
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open DyadicMixedB4YoungIntegral DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth

noncomputable section

end

end B13BoundedStepProductSavingProof

namespace B13BoundedStepProductSavingProof

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Arithmetic DyadicMixedB4Scale DyadicMixedB4ArcDecomposition DyadicMixedB4Geometric

noncomputable section

end

end B13BoundedStepProductSavingProof

namespace B13BoundedStepProductSavingProof

open Finset MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4PairIntegral DyadicMixedB4Finish

noncomputable section

end

end B13BoundedStepProductSavingProof

namespace B13BoundedStepProductSavingProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Fourier
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4PairIntegral

noncomputable section

end

end B13BoundedStepProductSavingProof

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Right cofactor -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4ArcDecomposition DyadicMixedB4TailScale
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def rightLargeCofactorCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (33 / 64 : ℝ)⌋₊

def rightVaughanCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 256 : ℝ)⌋₊

def shortRightBandIndices (n K d : ℕ) : Finset ℕ :=
  Ioc (cutoffB n / d) (min (splitCut n / d) (n / (K + 1) / d))

end

end B13BoundedStepProductSavingProof

end

/- Left type one -/
section

namespace B13BoundedStepProductSavingProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4EnergyTail
open DyadicMixedB4ArcGeometry DyadicMixedB4OffWaveMoment DyadicMixedB4YoungIntegral
open DyadicMixedB4ArcDecomposition DyadicMixedB4PairIntegral
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

noncomputable section

def truncateArithmetic (f : ArithmeticFunction ℝ) (H : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m ≤ H then f m else 0, by simp⟩

end

end B13BoundedStepProductSavingProof

end

/- Left zeta -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Vaughan zeta -/
section

namespace B13BoundedStepProductSavingProof

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail
open DyadicMixedB4MoebiusGauss DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def vaughanShortCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 96 : ℝ)⌋₊

end

end B13BoundedStepProductSavingProof

end

/- Right type one saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4MoebiusGauss
open DyadicMixedB4DivisorGrowth DyadicMixedB4Finish DyadicMixedB4NumericBudgets
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def rightVaughanMoebius (n : ℕ) : ArithmeticFunction ℝ :=
  truncateArithmetic (μ : ArithmeticFunction ℝ) (rightVaughanCut n)

def rightVaughanMangoldt (n : ℕ) : ArithmeticFunction ℝ :=
  truncateArithmetic vonMangoldt (rightVaughanCut n)

end

end B13BoundedStepProductSavingProof

end

/- Bilateral short -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Left medium waves -/
section

namespace B13BoundedStepProductSavingProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4EnergyTail
open DyadicMixedB4ArcGeometry DyadicMixedB4OffWaveMoment DyadicMixedB4YoungIntegral
open DyadicMixedB4ArcDecomposition DyadicMixedB4PairIntegral
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

noncomputable section

def leftMediumCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (3 / 10 : ℝ)⌋₊

end

end B13BoundedStepProductSavingProof

end

/- Left bilinear short -/
section

namespace B13BoundedStepProductSavingProof

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4PairIntegral
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4MoebiusGauss
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def leftBilinearFactor (n : ℕ) : ArithmeticFunction ℝ :=
  let P := vaughanShortCut n
  let M := (μ : ArithmeticFunction ℝ)
  (M - truncateArithmetic M P) * (vonMangoldt - truncateArithmetic vonMangoldt P)

def leftBilinearItems (n : ℕ) : Finset (ℕ × ℕ) := Ioc (cutoffU n) (lowCut n) ×ˢ Icc 1 n

def leftBilinearStep (i : ℕ × ℕ) : ℕ := i.1 * i.2

def leftBilinearWeight (n : ℕ) (i : ℕ × ℕ) : ℂ :=
  (leftBandMoebius n i.1 : ℂ) * (leftBilinearFactor n i.2 : ℂ)

def leftLargeBilinearItems (n : ℕ) : Finset (ℕ × ℕ) :=
  (leftBilinearItems n).filter (fun i => leftMediumCap n < leftBilinearStep i)

private theorem norm_left_bilinear_factor {n s : ℕ} (hs : s ≤ n)
    {T : ℝ} (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖(leftBilinearFactor n s : ℂ)‖ ≤ T * logBudget n := by
  let P := vaughanShortCut n
  let M := (μ : ArithmeticFunction ℝ)
  let f := M - truncateArithmetic M P
  let g := vonMangoldt - truncateArithmetic vonMangoldt P
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have shortM (j : ℕ) (_ : j ≤ n) : ‖(f j : ℂ)‖ ≤ 1 := by
    change ‖(((μ j : ℝ) - (if j ≤ P then (μ j : ℝ) else 0) : ℝ) : ℂ)‖ ≤ 1
    by_cases h : j ≤ P
    · simp [h]
    · simpa [h, moebiusComplex] using norm_moebiusComplex_le_one j
  have shortΛ (j : ℕ) (hj : j ≤ n) : ‖(g j : ℂ)‖ ≤ logBudget n := by
    change ‖((vonMangoldt j - (if j ≤ P then vonMangoldt j else 0) : ℝ) : ℂ)‖ ≤ logBudget n
    by_cases h : j ≤ P
    · simp [h, L0]
    · simp only [h, ite_false, sub_zero]
      by_cases zero : j = 0
      · simp [zero, L0]
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
        exact vonMangoldt_le_log.trans (log_le_logBudget (Nat.pos_of_ne_zero zero) hj)
  change ‖(((f * g : ArithmeticFunction ℝ) s) : ℂ)‖ ≤ T * logBudget n
  simpa only [one_mul] using
    norm_convolution_apply_le hs f g zero_le_one L0 (divisorBound s hs) shortM shortΛ

end

theorem norm_left_bilinear_factor_bound {n s : ℕ} (hs : s ≤ n)
    {T : ℝ} (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖(leftBilinearFactor n s : ℂ)‖ ≤ T*logBudget n :=
  norm_left_bilinear_factor hs divisorBound

end B13BoundedStepProductSavingProof

end

/- Right bilinear waves -/
section

namespace B13BoundedStepProductSavingProof

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

def rightLowWaveUpper (n : ℕ) (i : RightLowWaveIndex) : ℕ :=
  min (upperCut n / i.2) (n / rightLowWaveStep i)

abbrev RightHighWaveIndex := Σ _ : ℕ, ℕ × ℕ

def rightHighWaveBase (n : ℕ) : Finset RightHighWaveIndex :=
  (Icc 1 (cutoffU n)).sigma fun d =>
    shortRightBandIndices n (rightLargeCofactorCut n) d ×ˢ Icc 1 n

def rightHighWaveStep (i : RightHighWaveIndex) : ℕ := i.1 * i.2.1 * i.2.2

def rightHighWaveItems (n : ℕ) : Finset RightHighWaveIndex :=
  (rightHighWaveBase n).filter (fun i => rightHighWaveStep i ≤ n)

def rightHighWaveFactor (n : ℕ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ) - rightVaughanMoebius n) * (vonMangoldt - rightVaughanMangoldt n)

def rightHighWaveWeight (n : ℕ) (i : RightHighWaveIndex) : ℂ :=
  -(μ i.1 : ℂ) * (rightHighWaveFactor n i.2.2 : ℂ)

def rightHighWaveLower (n : ℕ) (i : RightHighWaveIndex) : ℕ := rightLargeCofactorCut n / i.2.2

end

end B13BoundedStepProductSavingProof

end

/- Joint actual waves -/
section

namespace B13BoundedStepProductSavingProof

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

theorem bilateral_right_high_step_range {n : ℕ} {i : RightHighWaveIndex} (hi : i ∈ rightHighWaveItems n) :
    rightHighWaveStep i ∈ Icc 1 n := by
  obtain ⟨hd,hks⟩ := mem_sigma.mp (mem_filter.mp hi).1
  obtain ⟨hk,hs⟩ := mem_product.mp hks
  have kp : 0 < i.2.1 := (Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1
  exact mem_Icc.mpr ⟨Nat.mul_pos (Nat.mul_pos (mem_Icc.mp hd).1 kp) (mem_Icc.mp hs).1, (mem_filter.mp hi).2⟩

private theorem norm_tail_vaughan_factor_le {n s : ℕ} (P : ℕ) (hs : s ≤ n)
    {T : ℝ} (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖((( ((μ : ArithmeticFunction ℝ) - truncateArithmetic (μ : ArithmeticFunction ℝ) P) *
        (vonMangoldt - truncateArithmetic vonMangoldt P) : ArithmeticFunction ℝ) s) : ℂ)‖ ≤
      T * logBudget n := by
  let M := (μ : ArithmeticFunction ℝ)
  let f := M - truncateArithmetic M P
  let g := vonMangoldt - truncateArithmetic vonMangoldt P
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have mNorm (j : ℕ) (_ : j ≤ n) : ‖(f j : ℂ)‖ ≤ 1 := by
    change ‖(((μ j : ℝ) - (if j ≤ P then (μ j : ℝ) else 0) : ℝ) : ℂ)‖ ≤ 1
    by_cases h : j ≤ P
    · simp [h]
    · simpa [h, moebiusComplex] using norm_moebiusComplex_le_one j
  have lNorm (j : ℕ) (hj : j ≤ n) : ‖(g j : ℂ)‖ ≤ logBudget n := by
    change ‖((vonMangoldt j - (if j ≤ P then vonMangoldt j else 0) : ℝ) : ℂ)‖ ≤ logBudget n
    by_cases h : j ≤ P
    · simp [h, L0]
    · simp only [h, ite_false, sub_zero]
      by_cases zero : j = 0
      · simp [zero, L0]
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
        exact vonMangoldt_le_log.trans (log_le_logBudget (Nat.pos_of_ne_zero zero) hj)
  change ‖(((f*g : ArithmeticFunction ℝ) s) : ℂ)‖ ≤ _
  simpa only [one_mul] using norm_convolution_apply_le hs f g zero_le_one L0 (divisorBound s hs) mNorm lNorm

private theorem norm_mass_le_of_card_le {α : Type*} (S : Finset α) (c : α → ℂ)
    {A B : ℝ} (cardBound : (S.card : ℝ) ≤ A) (B0 : 0 ≤ B) (wt : ∀ i ∈ S, ‖c i‖ ≤ B) :
    (∑ i ∈ S, ‖c i‖) ≤ A*B := by
  calc
    _ ≤ ∑ _ ∈ S, B := sum_le_sum wt
    _ = (S.card : ℝ)*B := by rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right cardBound B0

theorem norm_bilateral_left_step_mass {n : ℕ} (hn : 0 < n) {T : ℝ} (T0 : 0 ≤ T)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (u : ℕ) (hu : u ∈ Icc 1 n) :
    (∑ i ∈ (bilateralLeftWaveItems n).filter (fun i => leftBilinearStep i = u),
      ‖leftBilinearWeight n i‖) ≤ T^3 * logBudget n := by
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
  refine (norm_mass_le_of_card_le selected (leftBilinearWeight n) cn
    (mul_nonneg T0 (mul_nonneg T0 (zero_le_one.trans (one_le_logBudget n)))) ?_).trans_eq (by ring)
  intro i hi
  obtain ⟨ha,hs⟩ := mem_product.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hi).1).1).1
  have aBound := (mem_Ioc.mp ha).2.trans
    (show lowCut n ≤ n from Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num)))
  rw [leftBilinearWeight, norm_mul]
  refine mul_le_mul ((norm_leftBandMoebius_le n i.1).trans (divisorBound i.1 aBound)) ?_ (norm_nonneg _) T0
  exact norm_tail_vaughan_factor_le (vaughanShortCut n) (mem_Icc.mp hs).2 divisorBound

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

theorem norm_bilateral_right_high_step_mass {n : ℕ} {T : ℝ} (T0 : 0 ≤ T)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (u : ℕ) (hu : u ∈ Icc 1 n) :
    (∑ i ∈ (rightHighWaveItems n).filter (fun i => rightHighWaveStep i = u), ‖rightHighWaveWeight n i‖) ≤
      T^3 * logBudget n := by
  let selected := (rightHighWaveItems n).filter (fun i => rightHighWaveStep i = u)
  have up : 0 < u := (mem_Icc.mp hu).1
  have count : selected.card ≤ (u.divisors ×ˢ u.divisors).card := by
    apply card_le_card_of_injOn (fun i : RightHighWaveIndex => (i.1,i.2.2))
    · intro i hi
      have hi' : i ∈ selected := hi
      have eq : i.1*i.2.1*i.2.2 = u := (mem_filter.mp hi').2
      refine mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨?_,up.ne'⟩, Nat.mem_divisors.mpr ⟨?_,up.ne'⟩⟩
      · exact ⟨i.2.1*i.2.2, eq.symm.trans (Nat.mul_assoc _ _ _)⟩
      · exact ⟨i.1*i.2.1, eq.symm.trans (Nat.mul_comm (i.1*i.2.1) i.2.2)⟩
    · intro i hi j hj first
      have ii : i ∈ selected := hi
      have jj : j ∈ selected := hj
      have eq := (mem_filter.mp ii).2.trans (mem_filter.mp jj).2.symm
      have ⟨hd,hks⟩ := mem_sigma.mp (mem_filter.mp (mem_filter.mp ii).1).1
      have hs := (mem_product.mp hks).2
      rcases i with ⟨d,k,s⟩
      rcases j with ⟨e,p,r⟩
      change (d,s)=(e,r) at first
      injection first with dSame sSame
      subst e
      subst r
      change d*k*s = d*p*s at eq
      have kSame := Nat.eq_of_mul_eq_mul_left (mem_Icc.mp hd).1
        (Nat.eq_of_mul_eq_mul_right (mem_Icc.mp hs).1 eq)
      simp [kSame]
  have cn : (selected.card : ℝ) ≤ T^2 := by
    calc
      _ ≤ ((u.divisors ×ˢ u.divisors).card : ℝ) := by exact_mod_cast count
      _ = (u.divisors.card : ℝ)^2 := by simp [card_product,pow_two]
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) (divisorBound u (mem_Icc.mp hu).2) _
  refine (norm_mass_le_of_card_le selected (rightHighWaveWeight n) cn
    (mul_nonneg T0 (zero_le_one.trans (one_le_logBudget n))) ?_).trans_eq (by ring)
  intro i hi
  have hh := (mem_sigma.mp (mem_filter.mp (mem_filter.mp hi).1).1).2
  have sBound := (mem_Icc.mp (mem_product.mp hh).2).2
  rw [rightHighWaveWeight, norm_mul, norm_neg]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (by simpa [moebiusComplex] using norm_moebiusComplex_le_one i.1)).trans
    (norm_tail_vaughan_factor_le (rightVaughanCut n) sBound divisorBound)

end

end B13BoundedStepProductSavingProof

end

/- Joint product limit -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Long lattice -/
section

namespace B13BoundedStepProductSavingProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open DyadicMixedB4Fourier DyadicMixedB4ArcDecomposition DyadicMixedB4OffWaveMoment
open DyadicMixedB4Scale
open scoped Classical

noncomputable section

def progressionPairSolutions (n u v l r p s : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc l r ×ˢ Ioc p s).filter (fun i => u*i.1 + v*i.2 = n)

theorem progression_pair_empty_of_not_gcd_dvd {n u v l r p s : ℕ} (hn : ¬u.gcd v ∣ n) :
    progressionPairSolutions n u v l r p s = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  have eq := (mem_filter.mp hi).2
  exact hn (eq ▸ dvd_add ((Nat.gcd_dvd_left u v).trans (dvd_mul_right u i.1))
    ((Nat.gcd_dvd_right u v).trans (dvd_mul_right v i.2)))

end

end B13BoundedStepProductSavingProof

end

/- Residue count -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

def pairLeftLower (n u v l s : ℕ) : ℤ :=
  max (l : ℤ) (((n : ℤ) - (v : ℤ)*s - 1)/(u : ℤ))

def pairLeftUpper (n u v r p : ℕ) : ℤ :=
  min (r : ℤ) (((n : ℤ) - (v : ℤ)*((p : ℤ)+1))/(u : ℤ))

private def pairLeftRange (n u v l r p s : ℕ) : Finset ℤ :=
  (Ioc (pairLeftLower n u v l s) (pairLeftUpper n u v r p)).filter
    (fun x => (u : ℤ)*x ≡ n [ZMOD (v : ℤ)])

private theorem mem_pair_left_range {n u v l r p s : ℕ} {x : ℤ} (hu : 0 < u) :
    x ∈ pairLeftRange n u v l r p s ↔
      (l : ℤ) < x ∧ x ≤ (r : ℤ) ∧ (n : ℤ) ≤ (u : ℤ)*x + (v : ℤ)*s ∧
        (u : ℤ)*x + (v : ℤ)*((p : ℤ)+1) ≤ n ∧ (u : ℤ)*x ≡ n [ZMOD (v : ℤ)] := by
  have ur : (0 : ℤ) < u := by exact_mod_cast hu
  unfold pairLeftRange pairLeftLower pairLeftUpper
  rw [mem_filter, mem_Ioc, max_lt_iff, le_min_iff, Int.ediv_lt_iff_lt_mul ur, Int.le_ediv_iff_mul_le ur]
  rw [mul_comm x (u : ℤ)]
  constructor
  · rintro ⟨⟨⟨lBound, lower⟩, rBound, upper⟩, modEq⟩
    exact ⟨lBound, rBound, by omega, by omega, modEq⟩
  · rintro ⟨lBound, rBound, lower, upper, modEq⟩
    exact ⟨⟨⟨lBound, by omega⟩, rBound, by omega⟩, modEq⟩

private theorem progression_pair_count_eq_left_range {n u v l r p s : ℕ} (hu : 0 < u) (hv : 0 < v) :
    (progressionPairSolutions n u v l r p s).card = (pairLeftRange n u v l r p s).card := by
  have vr : (0 : ℤ) < v := by exact_mod_cast hv
  apply card_bij (fun i _ => (i.1 : ℤ))
  · intro i hi
    obtain ⟨inside, eq⟩ := mem_filter.mp hi
    obtain ⟨left, right⟩ := mem_product.mp inside
    obtain ⟨lBound, rBound⟩ := mem_Ioc.mp left
    obtain ⟨pBound, sBound⟩ := mem_Ioc.mp right
    have zeq : (u : ℤ)*(i.1 : ℤ) + (v : ℤ)*(i.2 : ℤ) = n := by exact_mod_cast eq
    refine (mem_pair_left_range hu).mpr ⟨by exact_mod_cast lBound, by exact_mod_cast rBound, ?_, ?_, ?_⟩
    · rw [← zeq]
      have sb : (i.2 : ℤ) ≤ (s : ℤ) := by exact_mod_cast sBound
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left sb vr.le)
    · rw [← zeq]
      have pb : ((p : ℤ)+1) ≤ (i.2 : ℤ) := by exact_mod_cast Nat.succ_le_of_lt pBound
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left pb vr.le)
    · apply Int.modEq_iff_dvd.mpr
      exact ⟨i.2, by omega⟩
  · intro i hi j hj same
    have eqI := (mem_filter.mp hi).2
    have eqJ := (mem_filter.mp hj).2
    have eqX : i.1 = j.1 := by exact_mod_cast same
    rw [eqX] at eqI
    exact Prod.ext eqX (Nat.eq_of_mul_eq_mul_left hv (Nat.add_left_cancel (eqI.trans eqJ.symm)))
  · intro x hx
    obtain ⟨xl, xr, lower, upper, eq⟩ := (mem_pair_left_range hu).mp hx
    obtain ⟨y, hy⟩ := Int.modEq_iff_dvd.mp eq
    have yLower : (p : ℤ) + 1 ≤ y := by
      apply le_of_mul_le_mul_left _ vr
      linarith only [upper, hy]
    have yUpper : y ≤ (s : ℤ) := by
      apply le_of_mul_le_mul_left _ vr
      linarith only [lower, hy]
    have xNonnegative : 0 ≤ x := by omega
    have yNonnegative : 0 ≤ y := by omega
    have xExact := Int.toNat_of_nonneg xNonnegative
    have yExact := Int.toNat_of_nonneg yNonnegative
    have mapped : (x.toNat, y.toNat) ∈ progressionPairSolutions n u v l r p s := by
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, mem_Ioc.mpr ⟨?_, ?_⟩⟩, ?_⟩
      · exact_mod_cast (show (l : ℤ) < (x.toNat : ℤ) by rw [xExact]; exact xl)
      · exact_mod_cast (show (x.toNat : ℤ) ≤ (r : ℤ) by rw [xExact]; exact xr)
      · exact_mod_cast (show (p : ℤ) < (y.toNat : ℤ) by rw [yExact]; omega)
      · exact_mod_cast (show (y.toNat : ℤ) ≤ (s : ℤ) by rw [yExact]; exact yUpper)
      · exact_mod_cast (show (u : ℤ)*(x.toNat : ℤ) + (v : ℤ)*(y.toNat : ℤ) = n by
          rw [xExact, yExact]
          omega)
    exact ⟨(x.toNat, y.toNat), mapped, xExact⟩

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

def pairResidue (n u v : ℕ) : ℤ :=
  let d := u.gcd v
  ((n/d : ℕ) : ℤ) * Nat.gcdA (u/d) (v/d) % ((v/d : ℕ) : ℤ)

private theorem pair_congruence_iff {n u v : ℕ} (hv : 0 < v) (hn : u.gcd v ∣ n) (x : ℤ) :
    ((u : ℤ)*x ≡ n [ZMOD (v : ℤ)]) ↔ x ≡ pairResidue n u v [ZMOD ((v/u.gcd v : ℕ) : ℤ)] := by
  let d := u.gcd v
  let A := u/d
  let B := v/d
  let C := n/d
  have dNat : 0 < d := Nat.gcd_pos_of_pos_right u hv
  have ar : (A : ℤ)*(d : ℤ) = (u : ℤ) := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left u v)
  have br : (B : ℤ)*(d : ℤ) = (v : ℤ) := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right u v)
  have cr : (C : ℤ)*(d : ℤ) = (n : ℤ) := by exact_mod_cast Nat.div_mul_cancel hn
  have dr : (d : ℤ) ≠ 0 := by exact_mod_cast dNat.ne'
  have cancel : (u : ℤ)*x ≡ n [ZMOD (v : ℤ)] ↔ (A : ℤ)*x ≡ C [ZMOD (B : ℤ)] := by
    simp only [Int.modEq_iff_dvd]
    rw [← ar, ← br, ← cr]
    have rearrange : (C : ℤ)*d - (A : ℤ)*d*x = ((C : ℤ)-(A : ℤ)*x)*d := by ring
    rw [rearrange]
    exact mul_dvd_mul_iff_right dr
  have coprime : A.Coprime B := Nat.coprime_div_gcd_div_gcd dNat
  have gcdA := Int.gcd_a_modEq A B
  rw [coprime.gcd_eq_one, Nat.cast_one] at gcdA
  have rho := Int.mod_modEq ((C : ℤ) * Nat.gcdA A B) (B : ℤ)
  change pairResidue n u v ≡ _ [ZMOD _] at rho
  refine cancel.trans ⟨fun h => ?_, fun h => ?_⟩
  · have comp := h.mul_right (Nat.gcdA A B)
    have left := gcdA.mul_right x
    have same : (A : ℤ)*x*Nat.gcdA A B = (A : ℤ)*Nat.gcdA A B*x := by ring
    rw [same] at comp
    rw [one_mul] at left
    exact left.symm.trans (comp.trans rho.symm)
  · have comp := (h.trans rho).mul_left (A : ℤ)
    have right := gcdA.mul_right (C : ℤ)
    have same : (A : ℤ)*((C : ℤ)*Nat.gcdA A B) = (A : ℤ)*Nat.gcdA A B*C := by ring
    rw [same] at comp
    rw [one_mul] at right
    exact comp.trans right

theorem progression_pair_count_floor {n u v l r p s : ℕ} (hu : 0 < u) (hv : 0 < v) :
    (progressionPairSolutions n u v l r p s).card =
      if u.gcd v ∣ n then
        let m : ℤ := (v/u.gcd v : ℕ)
        let z := pairResidue n u v
        ((pairLeftUpper n u v r p-z)/m - (pairLeftLower n u v l s-z)/m).toNat
      else 0 := by
  by_cases compatible : u.gcd v ∣ n
  · rw [ite_eq_left compatible, progression_pair_count_eq_left_range hu hv]
    have modulus : (0 : ℤ) < ((v/u.gcd v : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right ..)) (Nat.gcd_pos_of_pos_right u hv)
    unfold pairLeftRange
    simp_rw [pair_congruence_iff hv compatible]
    exact card_residue_Ioc _ _ _ _ modulus
  · rw [ite_eq_right compatible, progression_pair_empty_of_not_gcd_dvd compatible, card_empty]

theorem card_residue_in_integer_interval (a b z m : ℤ) (hm : 0 < m) :
    ((Ioc a b).filter (fun x => x ≡ z [ZMOD m])).card =
      ((b-z)/m - (a-z)/m).toNat :=
  card_residue_Ioc a b z m hm

end B13BoundedStepProductSavingProof

end

/- Residue error -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

def pairVolume (n u v l r p s : ℕ) : ℝ :=
  if u.gcd v ∣ n then
    let a := pairLeftLower n u v l s
    let b := pairLeftUpper n u v r p
    ((max 0 (b-a) : ℤ) : ℝ) / ((v/u.gcd v : ℕ) : ℝ)
  else 0

def pairResidueError (n u v l r p s : ℕ) : ℝ :=
  if u.gcd v ∣ n then
    let a := pairLeftLower n u v l s
    let b := pairLeftUpper n u v r p
    let z := pairResidue n u v
    let m : ℤ := (v/u.gcd v : ℕ)
    if a ≤ b then ((((a-z)%m : ℤ) : ℝ) - (((b-z)%m : ℤ) : ℝ))/(m : ℝ) else 0
  else 0

theorem progression_pair_count_eq_volume_add_error {n u v l r p s : ℕ} (hu : 0 < u) (hv : 0 < v) :
    ((progressionPairSolutions n u v l r p s).card : ℝ) =
      pairVolume n u v l r p s + pairResidueError n u v l r p s := by
  rw [progression_pair_count_floor hu hv]
  unfold pairVolume pairResidueError
  by_cases compatible : u.gcd v ∣ n
  · simp only [ite_eq_left compatible]
    let a := pairLeftLower n u v l s
    let b := pairLeftUpper n u v r p
    let z := pairResidue n u v
    let m : ℤ := (v/u.gcd v : ℕ)
    have mNat : 0 < v/u.gcd v :=
      Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right ..)) (Nat.gcd_pos_of_pos_right u hv)
    have mPos : 0 < m := by dsimp [m]; exact_mod_cast mNat
    change (((((b-z)/m - (a-z)/m).toNat) : ℕ) : ℝ) = ((max 0 (b-a) : ℤ) : ℝ)/(m : ℝ) +
      if a ≤ b then ((((a-z)%m : ℤ) : ℝ) - (((b-z)%m : ℤ) : ℝ))/(m : ℝ) else 0
    by_cases order : a ≤ b
    · have qle : (a-z)/m ≤ (b-z)/m := Int.ediv_le_ediv (by omega) (by omega)
      rw [ite_eq_left order, max_eq_right (sub_nonneg.mpr order)]
      have positive := Int.toNat_of_nonneg (sub_nonneg.mpr qle)
      have cast : (((((b-z)/m - (a-z)/m).toNat) : ℕ) : ℝ) = ((((b-z)/m - (a-z)/m : ℤ)) : ℝ) := by
        exact_mod_cast positive
      rw [cast]
      have mr : (0 : ℝ) < m := by exact_mod_cast mPos
      have lower : (((a-z)%m : ℤ) : ℝ) + (m : ℝ)*(((a-z)/m : ℤ) : ℝ) = (a : ℝ) - (z : ℝ) := by
        exact_mod_cast Int.emod_add_mul_ediv (a-z) m
      have upper : (((b-z)%m : ℤ) : ℝ) + (m : ℝ)*(((b-z)/m : ℤ) : ℝ) = (b : ℝ) - (z : ℝ) := by
        exact_mod_cast Int.emod_add_mul_ediv (b-z) m
      push_cast
      field_simp
      linarith only [lower, upper]
    · have qle : (b-z)/m ≤ (a-z)/m := Int.ediv_le_ediv (by omega) (by omega)
      have zero : ((b-z)/m - (a-z)/m).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      rw [ite_eq_right order, max_eq_left (by omega), zero]
      simp
  · simp [compatible]

theorem abs_pair_residue_error_lt_one (n u v l r p s : ℕ) (hv : 0 < v) :
    |pairResidueError n u v l r p s| < 1 := by
  unfold pairResidueError
  by_cases compatible : u.gcd v ∣ n
  · rw [ite_eq_left compatible]
    dsimp only
    let a := pairLeftLower n u v l s
    let b := pairLeftUpper n u v r p
    let z := pairResidue n u v
    let m : ℤ := (v/u.gcd v : ℕ)
    have mNat : 0 < v/u.gcd v :=
      Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right ..)) (Nat.gcd_pos_of_pos_right u hv)
    have mPos : 0 < m := by dsimp [m]; exact_mod_cast mNat
    have mr : (0 : ℝ) < m := by exact_mod_cast mPos
    have leftLo : (0 : ℝ) ≤ (((a-z)%m : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg (a-z) mPos.ne'
    have rightLo : (0 : ℝ) ≤ (((b-z)%m : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg (b-z) mPos.ne'
    have leftHi : (((a-z)%m : ℤ) : ℝ) < (m : ℝ) := by exact_mod_cast Int.emod_lt_of_pos (a-z) mPos
    have rightHi : (((b-z)%m : ℤ) : ℝ) < (m : ℝ) := by exact_mod_cast Int.emod_lt_of_pos (b-z) mPos
    change |if a ≤ b then ((((a-z)%m : ℤ) : ℝ)-(((b-z)%m : ℤ) : ℝ))/(m : ℝ) else 0| < 1
    by_cases order : a ≤ b
    · rw [ite_eq_left order, abs_div, abs_of_pos mr, div_lt_one mr, abs_lt]
      constructor <;> linarith only [leftLo,rightLo,leftHi,rightHi]
    · rw [ite_eq_right order]
      norm_num
  · rw [ite_eq_right compatible]
    norm_num

end

end B13BoundedStepProductSavingProof

end

/- Residue fourier -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Interval residue fourier -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Prime right low residue -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Prime weighted intervals -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

def gatedBilinearSum {ι : Type*} (I : Finset ι) (J : Finset ℤ) (α : ι → ℂ) (β : ℤ → ℂ)
    (lo hi : ι → ℤ) (val : ι → ℤ → ℂ) : ℂ :=
  ∑ j ∈ J, β j * ∑ i ∈ I, if lo i < j ∧ j ≤ hi i then α i*val i j else 0

theorem int_interval_residue_count_add (p : ℕ) {v w u : ℤ}
    (hvw : v ≤ w) (hwu : w ≤ u) (z : ZMod p) :
    intIntervalResidueCount p v u z =
      intIntervalResidueCount p v w z + intIntervalResidueCount p w u z := by
  let f (a b : ℤ) := (Ioc a b).filter (fun (j : ℤ) => (j : ZMod p) = z)
  have disj : Disjoint (f v w) (f w u) := by
    rw [disjoint_left]
    intro j h₁ h₂
    exact (not_lt_of_ge (mem_Ioc.mp (mem_filter.mp h₁).1).2) (mem_Ioc.mp (mem_filter.mp h₂).1).1
  have parts : f v u = (f v w) ∪ (f w u) := by
    ext j
    simp only [f, mem_filter, mem_Ioc, mem_union]
    constructor
    · intro h
      by_cases le : j ≤ w
      · exact Or.inl ⟨⟨h.1.1, le⟩,h.2⟩
      · exact Or.inr ⟨⟨lt_of_not_ge le, h.1.2⟩, h.2⟩
    · rintro (h | h)
      · exact ⟨⟨h.1.1, h.1.2.trans hwu⟩, h.2⟩
      · exact ⟨⟨hvw.trans_lt h.1.1, h.1.2⟩, h.2⟩
  change #(f v u) = #(f v w)+#(f w u)
  rw [parts, card_union_of_disjoint disj]

theorem norm_centered_residue_change_le (p : ℕ) [NeZero p] {v b w u : ℤ}
    (hvb : v ≤ b) (hbw : b ≤ w) (hwu : w ≤ u) (z : ZMod p) :
    ‖centeredIntIntervalResidue p v w z - centeredIntIntervalResidue p v b z‖ ≤
      (intIntervalResidueCount p b u z : ℝ) + ((u-b : ℤ) : ℝ)/(p : ℝ) := by
  have p0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have changeEq : centeredIntIntervalResidue p v w z - centeredIntIntervalResidue p v b z =
      (intIntervalResidueCount p b w z : ℂ) - ((w-b : ℤ) : ℂ)/(p : ℂ) := by
    unfold centeredIntIntervalResidue
    rw [int_interval_residue_count_add p hvb hbw]
    push_cast
    ring
  have dist : (0 : ℝ) ≤ ((w-b : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hbw
  have dist_le : (((w-b : ℤ) : ℝ)) ≤ ((u-b : ℤ) : ℝ) := by exact_mod_cast sub_le_sub_right hwu b
  have count : intIntervalResidueCount p b w z ≤ intIntervalResidueCount p b u z := by
    rw [int_interval_residue_count_add p hbw hwu]
    exact Nat.le_add_right _ _
  rw [changeEq]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_natCast, norm_div, Complex.norm_intCast, Complex.norm_natCast, abs_of_nonneg dist]
  exact add_le_add (by exact_mod_cast count) (div_le_div_of_nonneg_right dist_le p0.le)

private theorem gated_bilinear_congr {ι : Type*} (I : Finset ι) (J : Finset ℤ)
    (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ) {f g : ι → ℤ → ℂ}
    (h : ∀ i ∈ I, ∀ j ∈ J, lo i < j ∧ j ≤ hi i → f i j = g i j) :
    gatedBilinearSum I J α β lo hi f = gatedBilinearSum I J α β lo hi g := by
  unfold gatedBilinearSum
  refine sum_congr rfl fun j hj => congrArg (fun z : ℂ => β j*z)
    (sum_congr rfl fun i hiI => ?_)
  by_cases gate : lo i < j ∧ j ≤ hi i
  · rw [ite_eq_left gate, ite_eq_left gate, h i hiI j hj gate]
  · simp [gate]

private theorem gated_bilinear_add {ι : Type*} (I : Finset ι) (J : Finset ℤ)
    (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ) (f g : ι → ℤ → ℂ) :
    gatedBilinearSum I J α β lo hi (fun i j => f i j + g i j) =
      gatedBilinearSum I J α β lo hi f + gatedBilinearSum I J α β lo hi g := by
  unfold gatedBilinearSum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_add, ← sum_add_distrib]
  refine congrArg (fun z : ℂ => β j*z) (sum_congr rfl fun i _ => ?_)
  split_ifs <;> simp [mul_add]

private theorem gated_bilinear_sub {ι : Type*} (I : Finset ι) (J : Finset ℤ)
    (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ) (f g : ι → ℤ → ℂ) :
    gatedBilinearSum I J α β lo hi f - gatedBilinearSum I J α β lo hi g =
      gatedBilinearSum I J α β lo hi (fun i j => f i j - g i j) := by
  unfold gatedBilinearSum
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sub, ← sum_sub_distrib]
  refine congrArg (fun z : ℂ => β j*z) (sum_congr rfl fun i _ => ?_)
  split_ifs <;> simp [mul_sub]

private theorem norm_gated_bilinear_sum_le {ι : Type*} (I : Finset ι) (J : Finset ℤ)
    (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ) (f : ι → ℤ → ℂ) (B : ι → ℤ → ℝ)
    (h : ∀ i ∈ I, ∀ j ∈ J, lo i < j ∧ j ≤ hi i → ‖f i j‖ ≤ B i j) :
    ‖gatedBilinearSum I J α β lo hi f‖ ≤
      ∑ j ∈ J, ‖β j‖*∑ i ∈ I, if lo i < j ∧ j ≤ hi i then ‖α i‖*B i j else 0 := by
  unfold gatedBilinearSum
  refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i hiI => ?_)) (norm_nonneg _)
  by_cases gate : lo i < j ∧ j ≤ hi i
  · simp only [ite_eq_left gate, norm_mul]
    exact mul_le_mul_of_nonneg_left (h i hiI j hj gate) (norm_nonneg _)
  · simp [gate]

theorem norm_gated_residue_variable_endpoint_le (p : ℕ) [NeZero p] {ι : Type*}
    (I : Finset ι) (J : Finset ℤ) (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ)
    {v b u : ℤ} (hvb : v ≤ b) (hbu : b ≤ u) (z : ι → ℤ → ZMod p) (endpt : ι → ℤ → ℤ)
    (bracket : ∀ i ∈ I, ∀ j ∈ J, lo i < j ∧ j ≤ hi i → b ≤ endpt i j ∧ endpt i j ≤ u)
    {boundValue : ℝ}
    (baseEstimate : ‖gatedBilinearSum I J α β lo hi (fun i j => centeredIntIntervalResidue p v b (z i j))‖ ≤ boundValue)
    (edgeEstimate : ‖gatedBilinearSum I J (fun i => (‖α i‖ : ℂ)) (fun j => (‖β j‖ : ℂ)) lo hi
      (fun i j => centeredIntIntervalResidue p b u (z i j))‖ ≤ boundValue) :
    ‖gatedBilinearSum I J α β lo hi (fun i j => centeredIntIntervalResidue p v (endpt i j) (z i j))‖ ≤
      2*boundValue + (2*(((u-b : ℤ) : ℝ)/(p : ℝ))) *
        (∑ j ∈ J, ‖β j‖*∑ i ∈ I, if lo i < j ∧ j ≤ hi i then ‖α i‖ else 0) := by
  let U (i : ι) : ℂ := ‖α i‖
  let V (j : ℤ) : ℂ := ‖β j‖
  let f (i : ι) (j : ℤ) := centeredIntIntervalResidue p v (endpt i j) (z i j)
  let base (i : ι) (j : ℤ) := centeredIntIntervalResidue p v b (z i j)
  let edge (i : ι) (j : ℤ) := centeredIntIntervalResidue p b u (z i j)
  let Δ : ℝ := ((u-b : ℤ) : ℝ)/(p : ℝ)
  let mass := ∑ j ∈ J, ‖β j‖*∑ i ∈ I, if lo i < j ∧ j ≤ hi i then ‖α i‖ else 0
  let B (i : ι) (j : ℤ) := (intIntervalResidueCount p b u (z i j) : ℝ)+Δ
  let E := ∑ j ∈ J, ‖β j‖*∑ i ∈ I, if lo i < j ∧ j ≤ hi i then ‖α i‖*B i j else 0
  let F := boundValue
  have Δ0 : 0 ≤ Δ := div_nonneg (by exact_mod_cast sub_nonneg.mpr hbu) (by positivity)
  have E0 : 0 ≤ E := by
    unfold E
    exact sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (sum_nonneg fun i _ => by
      split_ifs
      · exact mul_nonneg (norm_nonneg _) (add_nonneg (by positivity) Δ0)
      · exact le_rfl)
  have baseline : ‖gatedBilinearSum I J α β lo hi base‖ ≤ F := baseEstimate
  have edgeb : ‖gatedBilinearSum I J U V lo hi edge‖ ≤ F := edgeEstimate
  have diff : ‖gatedBilinearSum I J α β lo hi f - gatedBilinearSum I J α β lo hi base‖ ≤ E := by
    rw [gated_bilinear_sub]
    refine norm_gated_bilinear_sum_le I J α β lo hi _ B (fun i hiI j hj gate => ?_)
    obtain ⟨lb,ub⟩ := bracket i hiI j hj gate
    exact norm_centered_residue_change_le p hvb lb ub (z i j)
  have castE : (E : ℂ) = gatedBilinearSum I J U V lo hi (fun i j => (B i j : ℂ)) := by
    change Complex.ofRealHom (∑ j ∈ J, ‖β j‖*∑ i ∈ I,
      if lo i < j ∧ j ≤ hi i then ‖α i‖*B i j else 0) = _
    simp only [map_sum, map_mul]
    unfold gatedBilinearSum
    refine sum_congr rfl fun j _ => congrArg (fun z : ℂ => V j*z)
      (sum_congr rfl fun i _ => ?_)
    split_ifs
    · rw [map_mul]
      rfl
    · exact map_zero Complex.ofRealHom
  have decomp : gatedBilinearSum I J U V lo hi (fun i j => (B i j : ℂ)) =
      gatedBilinearSum I J U V lo hi edge + gatedBilinearSum I J U V lo hi (fun _ _ => (2*Δ : ℂ)) := by
    rw [← gated_bilinear_add]
    refine gated_bilinear_congr I J U V lo hi fun i _ j _ _ => ?_
    simp only [B, edge, centeredIntIntervalResidue, Complex.ofReal_add, Complex.ofReal_natCast]
    have delta : (Δ : ℂ) = ((u-b : ℤ) : ℂ)/(p : ℂ) := by
      simp only [Δ, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_natCast]
    rw [delta]
    ring
  have massb : ‖gatedBilinearSum I J U V lo hi (fun _ _ => (2*Δ : ℂ))‖ ≤ (2*Δ)*mass := by
    have e := norm_gated_bilinear_sum_le I J U V lo hi (fun _ _ => (2*Δ : ℂ))
      (fun _ _ => 2*Δ) (fun _ _ _ _ _ => by
        rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)])
    simp only [U, V, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at e
    refine e.trans_eq ?_
    have factor (j : ℤ) : (∑ i ∈ I, if lo i < j ∧ j ≤ hi i then ‖α i‖*(2*Δ) else 0) =
        (∑ i ∈ I, if lo i < j ∧ j ≤ hi i then ‖α i‖ else 0)*(2*Δ) := by
      rw [sum_mul]
      refine sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    simp_rw [factor]
    calc
      _ = ∑ j ∈ J, (‖β j‖*(∑ i ∈ I, if lo i < j ∧ j ≤ hi i then ‖α i‖ else 0))*(2*Δ) :=
        sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)
      _ = mass*(2*Δ) := (sum_mul ..).symm
      _ = _ := mul_comm mass (2*Δ)
  have EBound : E ≤ F+(2*Δ)*mass := by
    calc
      _ = ‖(E : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg E0]
      _ = ‖gatedBilinearSum I J U V lo hi edge +
            gatedBilinearSum I J U V lo hi (fun _ _ => (2*Δ : ℂ))‖ := by rw [castE,decomp]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add edgeb massb)
  change ‖gatedBilinearSum I J α β lo hi f‖ ≤
    2*boundValue + (2*Δ)*mass
  calc
    _ = ‖gatedBilinearSum I J α β lo hi base +
          (gatedBilinearSum I J α β lo hi f - gatedBilinearSum I J α β lo hi base)‖ := by
      have eq : gatedBilinearSum I J α β lo hi base +
          (gatedBilinearSum I J α β lo hi f-gatedBilinearSum I J α β lo hi base) =
          gatedBilinearSum I J α β lo hi f := by abel
      rw [eq]
    _ ≤ F+E := (norm_add_le _ _).trans (add_le_add baseline diff)
    _ ≤ F+(F+(2*Δ)*mass) := add_le_add (le_refl F) EBound
    _ = _ := by unfold F; ring

end

end B13BoundedStepProductSavingProof

end

/- Reciprocal bilinear -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

def reciprocalBilinearBound (p A K : ℕ) (T : ℝ) : ℝ :=
  (((K : ℝ)^3)*(p : ℝ)*(A : ℝ)^2*(1+inverseFibreBudget p A T))^(1/4 : ℝ)

private theorem finite_sum_fourth_le_card_cube {ι : Type*} (J : Finset ι) (f : ι → ℝ) :
    (∑ j ∈ J, f j)^4 ≤ (J.card : ℝ)^3*(∑ j ∈ J, f j^4) := by
  have a : (∑ j ∈ J, f j)^2 ≤ (J.card : ℝ)*(∑ j ∈ J, f j^2) := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => 1 : ι → ℝ) f
  have sum_power : (∑ j ∈ J, (f j^2)^2) = ∑ j ∈ J, f j^4 :=
    sum_congr rfl (fun _ _ => by ring)
  have b : (∑ j ∈ J, f j^2)^2 ≤ (J.card : ℝ)*(∑ j ∈ J, f j^4) := by
    rw [← sum_power]
    simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => 1 : ι → ℝ) (fun j => f j^2)
  calc
    _ = ((∑ j ∈ J, f j)^2)^2 := by ring
    _ ≤ ((J.card : ℝ)*(∑ j ∈ J, f j^2))^2 := pow_le_pow_left₀ (by positivity) a 2
    _ = (J.card : ℝ)^2*(∑ j ∈ J, f j^2)^2 := mul_pow _ _ _
    _ ≤ (J.card : ℝ)^2*((J.card : ℝ)*(∑ j ∈ J, f j^4)) :=
      mul_le_mul_of_nonneg_left b (by positivity)
    _ = _ := by ring

theorem norm_rectangular_inverse_sum_le_of_fourth_moment {p A : ℕ} [NeZero p]
    (I : Finset ℕ) {ι : Type*} (J : Finset ι) (freq : ι → ZMod p) (injective : Set.InjOn freq J)
    (α : ℕ → ℂ) (β : ι → ℂ) {W V T : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (T0 : 0 ≤ T)
    (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (fourthMoment : (∑ x : ZMod p, ‖inverseFrequencySum p I α x‖^4) ≤
      (p : ℝ)*(A : ℝ)^2*(1+inverseFibreBudget p A T)*W^4) :
    ‖∑ j ∈ J, β j*inverseFrequencySum p I α (freq j)‖ ≤
      W*V*reciprocalBilinearBound p A J.card T := by
  let f (j : ι) := ‖inverseFrequencySum p I α (freq j)‖
  let B := (p : ℝ)*(A : ℝ)^2*(1+inverseFibreBudget p A T)
  let D := ((J.card : ℝ)^3)*B
  have B0 : 0 ≤ B := by unfold B inverseFibreBudget; positivity
  have D0 : 0 ≤ D := by unfold D; positivity
  have BD : reciprocalBilinearBound p A J.card T = D^(1/4 : ℝ) := by
    unfold reciprocalBilinearBound D B
    congr 1
    ring
  have power : (D^(1/4 : ℝ))^4 = D := by
    calc
      _ = (D^(1/4 : ℝ))^(4 : ℝ) := (Real.rpow_natCast _ 4).symm
      _ = _ := by rw [← Real.rpow_mul D0]; norm_num
  have complete : (∑ j ∈ J, f j^4) ≤ B*W^4 := by
    calc
      _ = ∑ x ∈ J.image freq, ‖inverseFrequencySum p I α x‖^4 := by
        rw [sum_image (fun x hx y hy h => injective hx hy h)]
      _ ≤ ∑ x : ZMod p, ‖inverseFrequencySum p I α x‖^4 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
      _ ≤ _ := fourthMoment
  have htriangle : ‖∑ j ∈ J, β j*inverseFrequencySum p I α (freq j)‖ ≤ V*(∑ j ∈ J, f j) := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (bw j hj) (norm_nonneg _)
  have moment := (finite_sum_fourth_le_card_cube J f).trans
    (mul_le_mul_of_nonneg_left complete (by positivity : (0 : ℝ) ≤ (J.card : ℝ)^3))
  rw [BD]
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by decide : 4 ≠ 0)).mp
  calc
    _ ≤ (V*(∑ j ∈ J, f j))^4 := pow_le_pow_left₀ (norm_nonneg _) htriangle 4
    _ = V^4*(∑ j ∈ J, f j)^4 := mul_pow _ _ _
    _ ≤ V^4*(((J.card : ℝ)^3)*(B*W^4)) := mul_le_mul_of_nonneg_left moment (by positivity)
    _ = (W*V*D^(1/4 : ℝ))^4 := by
      rw [mul_pow,mul_pow,power]
      unfold D
      ring

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

private theorem indicator_eq_interval_residue_count {p : ℕ} [NeZero p] {a b j : ℤ}
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

theorem norm_gated_frequency_sum_le_of_fourth_moment {p A S : ℕ} [NeZero p]
    (Sp : S ≤ p) (I : Finset ℕ) (J : Finset ℤ) (Jrange : J ⊆ Ioc 0 (S : ℤ))
    (ψ : ℤ → ZMod p) (ψinj : Set.InjOn ψ J)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {W V T : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (T0 : 0 ≤ T)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ W) (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (fourthMoment : ∀ (weight : ℕ → ℂ) {X : ℝ}, 0 ≤ X → (∀ i ∈ I, ‖weight i‖ ≤ X) →
      (∑ x : ZMod p, ‖inverseFrequencySum p I weight x‖^4) ≤
        (p : ℝ)*(A : ℝ)^2*(1+inverseFibreBudget p A T)*X^4) :
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹))‖ ≤
      (2+Real.log p)*W*V*reciprocalBilinearBound p A J.card T := by
  let H := (univ : Finset (ZMod p)).filter (fun h => h ≠ 0)
  let a (i : ℕ) := max 0 (min (lo i) (S : ℤ))
  let b (i : ℕ) := max (a i) (min (hi i) (S : ℤ))
  let atZero (i : ℕ) : ℂ := ((b i-a i : ℤ) : ℂ)/(p : ℂ)
  let coeff (h : ZMod p) (i : ℕ) := intIntervalFourierCoefficient p (a i) (b i) h
  let βh (h : ZMod p) (j : ℤ) := β j*ZMod.stdAddChar (-(h*(j : ZMod p)))
  let G (h : ZMod p) := ∑ j ∈ J, βh h j*inverseFrequencySum p I (fun i => α i*coeff h i) (ψ j)
  let F := ∑ j ∈ J, β j*inverseFrequencySum p I (fun i => α i*atZero i) (ψ j)
  let Q := reciprocalBilinearBound p A J.card T
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
    rw [indicator_eq_interval_residue_count (left0 i) (rightcap i) (jRange hj),
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
    refine norm_rectangular_inverse_sum_le_of_fourth_moment I J ψ ψinj _ _ W0 V0 T0 bw
      (fourthMoment _ W0 ?_)
    intro i hiI
    rw [norm_mul]
    exact (mul_le_mul (aw i hiI) (az i) (norm_nonneg _) W0).trans_eq (mul_one _)
  have gLe (h : ZMod p) (hh : h ∈ H) : ‖G h‖ ≤ d h*(W*V*Q) := by
    have h0 := (mem_filter.mp hh).2
    have d0 : 0 ≤ d h := by unfold d; positivity
    have est := norm_rectangular_inverse_sum_le_of_fourth_moment I J ψ ψinj
      (fun i => α i*coeff h i) (βh h) (mul_nonneg W0 d0) V0 T0
      (by
        intro j hj
        rw [show ‖βh h j‖ = ‖β j‖ by simp [βh]]
        exact bw j hj)
      (fourthMoment _ (mul_nonneg W0 d0) (by
        intro i hiI
        rw [norm_mul]
        exact mul_le_mul (aw i hiI) (norm_int_interval_fourier_coefficient_le p (a i) (b i) h0)
          (norm_nonneg _) W0))
    change ‖G h‖ ≤ (W*d h)*V*Q at est
    exact est.trans_eq (by ring)
  rw [exactSum]
  have Q0 : 0 ≤ Q := by unfold Q reciprocalBilinearBound inverseFibreBudget; positivity
  calc
    _ ≤ ‖F‖+‖∑ h ∈ H, G h‖ := norm_add_le _ _
    _ ≤ W*V*Q+∑ h ∈ H, d h*(W*V*Q) :=
      (add_le_add) fLe ((norm_sum_le _ _).trans (sum_le_sum gLe))
    _ ≤ W*V*Q+(1+Real.log p)*(W*V*Q) := by
      rw [← sum_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (sum_inv_min_val_le p) (by positivity))
    _ = _ := by unfold Q; ring

end

end B13BoundedStepProductSavingProof

end

/- Reciprocal unit fibre -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

def inverseUnitCollisionFiber (m A : ℕ) (target : ZMod m) : Finset (ℕ × ℕ) :=
  (inverseCollisionFiber m A target).filter fun i => i.1.Coprime m ∧ i.2.Coprime m

end

end B13BoundedStepProductSavingProof

end

/- Shifted reciprocal gate -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

theorem norm_gated_translated_frequency_sum_le_of_fourth_moment {p A S : ℕ} [NeZero p]
    (Sp : S ≤ p) (L : ℤ) (I : Finset ℕ) (J : Finset ℤ) (Jrange : J ⊆ Ioc L (L+(S : ℤ)))
    (ψ : ℤ → ZMod p) (ψinj : Set.InjOn ψ J)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {W V T : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (T0 : 0 ≤ T)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ W) (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (fourthMoment : ∀ (weight : ℕ → ℂ) {X : ℝ}, 0 ≤ X → (∀ i ∈ I, ‖weight i‖ ≤ X) →
      (∑ x : ZMod p, ‖inverseFrequencySum p I weight x‖^4) ≤
        (p : ℝ)*(A : ℝ)^2*(1+inverseFibreBudget p A T)*X^4) :
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹))‖ ≤
      (2+Real.log p)*W*V*reciprocalBilinearBound p A J.card T := by
  let shift (j : ℤ) := j-L
  let unshift (j : ℤ) := j+L
  let K := J.image shift
  have identity (j : ℤ) : unshift (shift j) = j := by dsimp only [shift,unshift]; omega
  have unshift_mem {j : ℤ} (hj : j ∈ K) : unshift j ∈ J := by
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hj
    simpa only [identity] using ht
  have shift_inj : Function.Injective shift := by
    intro x y eq
    change x-L=y-L at eq
    omega
  have Kspan : K ⊆ Ioc (0 : ℤ) (S : ℤ) := by
    intro j hj
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hj
    have tr := mem_Ioc.mp (Jrange ht)
    exact mem_Ioc.mpr ⟨by unfold shift; omega,by unfold shift; omega⟩
  have inj : Set.InjOn (ψ ∘ unshift) K := by
    intro a ha b hb eq
    have same := ψinj (unshift_mem ha) (unshift_mem hb) eq
    change a+L=b+L at same
    omega
  have wt (j : ℤ) (hj : j ∈ K) : ‖(β ∘ unshift) j‖ ≤ V := bw _ (unshift_mem hj)
  have est := norm_gated_frequency_sum_le_of_fourth_moment Sp I K Kspan (ψ ∘ unshift) inj
    α (β ∘ unshift) (fun i => lo i-L) (fun i => hi i-L) W0 V0 T0 aw wt fourthMoment
  have eq : gatedBilinearSum I K α (β ∘ unshift) (fun i => lo i-L) (fun i => hi i-L)
      (fun i j => ZMod.stdAddChar ((ψ ∘ unshift) j*(i : ZMod p)⁻¹)) =
      gatedBilinearSum I J α β lo hi (fun i j => ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹)) := by
    unfold gatedBilinearSum K
    rw [sum_image (fun a _ b _ h => shift_inj h)]
    refine sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply,identity]
    apply congrArg (β j * ·)
    refine sum_congr rfl fun i _ => ?_
    have shifted : lo i-L < shift j ∧ shift j ≤ hi i-L ↔ lo i < j ∧ j ≤ hi i := by
      unfold shift
      omega
    simp only [shifted]
  rw [eq, show K.card = J.card from card_image_of_injective J shift_inj] at est
  exact est

theorem reciprocal_bilinear_bound_mono_card {m A B C : ℕ} {T : ℝ} (T0 : 0 ≤ T) (h : B ≤ C) :
    reciprocalBilinearBound m A B T ≤ reciprocalBilinearBound m A C T := by
  unfold reciprocalBilinearBound
  have Tbase : 0 ≤ 1+inverseFibreBudget m A T := by unfold inverseFibreBudget; positivity
  have cast : (B : ℝ) ≤ C := by exact_mod_cast h
  apply Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
  gcongr

end

end B13BoundedStepProductSavingProof

end

/- Prime product interval -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale
open scoped Classical

noncomputable section

private theorem cofactor_interval_iff_product {a l r : ℕ} (ha : 0 < a) {j : ℤ} (hj : 0 ≤ j) :
    (((l/a : ℕ) : ℤ) < j ∧ j ≤ ((r/a : ℕ) : ℤ)) ↔ l < a*j.toNat ∧ a*j.toNat ≤ r := by
  have cast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
  rw [← cast]
  simp only [Int.ofNat_lt, Int.ofNat_le, Nat.div_lt_iff_lt_mul ha, Nat.le_div_iff_mul_le ha,
    Nat.mul_comm j.toNat a, Int.toNat_natCast]

private theorem div_eq_iff_interval {m d k : ℕ} (hd : 0 < d) :
    m/d = k ↔ k*d ≤ m ∧ m < (k+1)*d := by
  rw [← Nat.le_div_iff_mul_le hd, ← Nat.div_lt_iff_lt_mul hd]
  omega

private def windowStepLo (N l d k : ℕ) : ℕ := max l (N/((k+1)*d))

private def windowStepHi (N r d k : ℕ) : ℕ := min r (if k = 0 then r else N/(k*d))

private theorem window_step_iff {N l r d k x : ℕ} (hd : 0 < d) (hx : 0 < x) :
    (windowStepLo N l d k < x ∧ x ≤ windowStepHi N r d k) ↔
      (l < x ∧ x ≤ r) ∧ (N/x)/d = k := by
  have left : N/((k+1)*d) < x ↔ N/x < (k+1)*d := by
    rw [Nat.div_lt_iff_lt_mul (mul_pos (by omega) hd), Nat.div_lt_iff_lt_mul hx, Nat.mul_comm x]
  have right (hk : k ≠ 0) : x ≤ N/(k*d) ↔ k*d ≤ N/x := by
    rw [Nat.le_div_iff_mul_le (mul_pos (Nat.pos_of_ne_zero hk) hd), Nat.le_div_iff_mul_le hx,
      Nat.mul_comm x]
  unfold windowStepLo windowStepHi
  rw [max_lt_iff, le_min_iff, left, div_eq_iff_interval hd]
  by_cases hk : k = 0
  · simp only [hk, ite_true, zero_mul, Nat.zero_le, true_and]
    tauto
  · simp only [ite_eq_right hk, right hk]
    tauto

theorem norm_product_interval_le_of_ratio_window {num p : ℕ}
    (I : Finset ℕ) (J : Finset ℤ) (α : ℕ → ℂ) (β : ℤ → ℂ) (f : ℕ → ℤ → ℂ)
    (apos : ∀ a ∈ I, 0 < a) (jpos : ∀ j ∈ J, 0 < j)
    {l r d endpointCap : ℕ} (hd : 0 < d)
    (cap : num/(l+1) ≤ endpointCap) {Q : ℝ}
    (windowEstimate : ∀ (g h : ℕ → ℤ) {b u : ℤ}, 0 ≤ b → b ≤ u →
      (∀ a ∈ I, ∀ j ∈ J, g a < j ∧ j ≤ h a →
        l+1 ≤ a*j.toNat ∧
          b ≤ (num : ℤ)/((a*j.toNat : ℕ) : ℤ) ∧
          (num : ℤ)/((a*j.toNat : ℕ) : ℤ) ≤ u) →
      ‖∑ j ∈ J, ∑ a ∈ I, if g a < j ∧ j ≤ h a then f a j else 0‖ ≤
        Q + (2*(((u-b : ℤ) : ℝ)/(p : ℝ))) *
          (∑ j ∈ J, ‖β j‖*∑ a ∈ I, if g a < j ∧ j ≤ h a then ‖α a‖ else 0)) :
    let lo (a : ℕ) : ℤ := (l/a : ℕ)
    let hi (a : ℕ) : ℤ := (r/a : ℕ)
    ‖∑ j ∈ J, ∑ a ∈ I, if lo a < j ∧ j ≤ hi a then f a j else 0‖ ≤
      ((endpointCap/d+1 : ℕ) : ℝ)*Q+(2*((d : ℝ)/(p : ℝ))) *
        (∑ j ∈ J, ‖β j‖*∑ a ∈ I, if lo a < j ∧ j ≤ hi a then ‖α a‖ else 0) := by
  dsimp only
  let K := range (endpointCap/d+1)
  let N := num
  let lo (a : ℕ) : ℤ := (l/a : ℕ)
  let hi (a : ℕ) : ℤ := (r/a : ℕ)
  let loK (k a : ℕ) : ℤ := (windowStepLo N l d k/a : ℕ)
  let hiK (k a : ℕ) : ℤ := (windowStepHi N r d k/a : ℕ)
  let B (a : ℕ) (j : ℤ) := N/(a*j.toNat)
  let V (k : ℕ) := ∑ j ∈ J, ∑ a ∈ I, if loK k a < j ∧ j ≤ hiK k a then f a j else 0
  let mass (f g : ℕ → ℤ) : ℝ :=
    ∑ j ∈ J, ‖β j‖*∑ a ∈ I, if f a < j ∧ j ≤ g a then ‖α a‖ else 0
  let D : ℝ := 2*((d : ℝ)/(p : ℝ))
  have jp {j : ℤ} (hj : j ∈ J) : 0 < j := jpos j hj
  have step_pos {a : ℕ} {j : ℤ} (ha : a ∈ I) (hj : j ∈ J) : 0 < a*j.toNat := by
    have jn : 0 < j.toNat := by have := jp hj; omega
    exact mul_pos (apos a ha) jn
  have gate {a : ℕ} {j : ℤ} (ha : a ∈ I) (hj : j ∈ J) :
      (lo a < j ∧ j ≤ hi a) ↔ l < a*j.toNat ∧ a*j.toNat ≤ r :=
    cofactor_interval_iff_product (apos a ha) (jp hj).le
  have gateK (k : ℕ) {a : ℕ} {j : ℤ} (ha : a ∈ I) (hj : j ∈ J) :
      (loK k a < j ∧ j ≤ hiK k a) ↔ (lo a < j ∧ j ≤ hi a) ∧ B a j / d = k := by
    rw [gate ha hj]
    exact (cofactor_interval_iff_product (apos a ha) (jp hj).le).trans
      (window_step_iff hd (step_pos ha hj))
  have Bbound {a : ℕ} {j : ℤ} (ha : a ∈ I) (hj : j ∈ J) (h : lo a < j ∧ j ≤ hi a) :
      B a j ≤ endpointCap := by
    have step : l+1 ≤ a*j.toNat := Nat.succ_le_of_lt ((gate ha hj).mp h).1
    exact (Nat.div_le_div_left step (Nat.succ_pos _)).trans cap
  have splitSum {R : Type} [AddCommMonoid R] (f : ℕ → ℤ → R) :
      (∑ j ∈ J, ∑ a ∈ I, if lo a < j ∧ j ≤ hi a then f a j else 0) =
        ∑ k ∈ K, ∑ j ∈ J, ∑ a ∈ I, if loK k a < j ∧ j ≤ hiK k a then f a j else 0 := by
    rw [sum_comm (s := K) (t := J)]
    refine sum_congr rfl fun j hj => ?_
    rw [sum_comm (s := K) (t := I)]
    refine sum_congr rfl fun a ha => ?_
    simp_rw [gateK _ ha hj]
    by_cases h : lo a < j ∧ j ≤ hi a
    · have mem : B a j/d ∈ K := by
        apply mem_range.mpr
        exact Nat.lt_succ_of_le (Nat.div_le_div_right (Bbound ha hj h))
      simp only [h, true_and, ite_true, sum_ite_eq, mem]
    · simp [h]
  have sumV : (∑ j ∈ J, ∑ a ∈ I, if lo a < j ∧ j ≤ hi a then f a j else 0) = ∑ k ∈ K, V k :=
    splitSum f
  have mass_repr (f g : ℕ → ℤ) :
      mass f g = ∑ j ∈ J, ∑ a ∈ I, if f a < j ∧ j ≤ g a then ‖β j‖*‖α a‖ else 0 := by
    unfold mass
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  have sumMass : mass lo hi = ∑ k ∈ K, mass (loK k) (hiK k) := by
    simp only [mass_repr]
    exact splitSum _
  have window (k : ℕ) : ‖V k‖ ≤ Q+D*mass (loK k) (hiK k) := by
    have order : ((k*d : ℕ) : ℤ) ≤ (((k+1)*d : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_right d (Nat.le_succ k)
    have lower0 : 0 ≤ ((k*d : ℕ) : ℤ) := by positivity
    have est := windowEstimate (loK k) (hiK k) lower0 order (fun a ha j hj h => ?_)
    · have delta : ((((k+1)*d : ℕ) : ℤ)-((k*d : ℕ) : ℤ) : ℤ) = d := by
        push_cast
        ring
      simpa only [V, D, mass, delta, Int.cast_natCast] using est
    · obtain ⟨orig,eq⟩ := (gateK k ha hj).mp h
      have hx : l+1 ≤ a*j.toNat := Nat.succ_le_of_lt ((gate ha hj).mp orig).1
      have castB : (B a j : ℤ) = (num : ℤ)/((a*j.toNat : ℕ) : ℤ) := by
        unfold B N
        rw [Int.natCast_ediv]
      obtain ⟨lb,ub⟩ := (div_eq_iff_interval hd).mp eq
      rw [←castB]
      exact ⟨hx, by exact_mod_cast lb, by exact_mod_cast ub.le⟩
  change ‖∑ j ∈ J, ∑ a ∈ I, if lo a < j ∧ j ≤ hi a then f a j else 0‖ ≤ ((endpointCap/d+1 : ℕ) : ℝ)*Q+D*mass lo hi
  rw [sumV]
  calc
    _ ≤ ∑ k ∈ K, ‖V k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ K, (Q+D*mass (loK k) (hiK k)) := sum_le_sum fun k _ => window k
    _ = _ := by
      rw [sum_add_distrib]
      have dm : (∑ k ∈ K, D*mass (loK k) (hiK k)) = D*mass lo hi := by rw [← mul_sum, ← sumMass]
      rw [dm]
      simp [K]

end

end B13BoundedStepProductSavingProof

end

/- Prime hyperbola size -/
section

namespace B13BoundedStepProductSavingProof

noncomputable section

theorem reciprocal_bilinear_bound_le_separated {p A S : ℕ} {T : ℝ}
    (p1 : 1 ≤ (p : ℝ)) (T1 : 1 ≤ T) :
    reciprocalBilinearBound p A S T ≤
      2*T*((S : ℝ)^(3/4 : ℝ)*(p : ℝ)^(1/4 : ℝ)*(A : ℝ)^(1/2 : ℝ))*
        (1+(A : ℝ)^(3/8 : ℝ)*(p : ℝ)^(-1/8 : ℝ)) := by
  let P := (p : ℝ)
  let B := (A : ℝ)
  let K := (S : ℝ)
  let F := B^(3/8 : ℝ)*P^(-1/8 : ℝ)
  let H := K^(3/4 : ℝ)*P^(1/4 : ℝ)*B^(1/2 : ℝ)
  have pp : 0 < P := zero_lt_one.trans_le p1
  have B0 : 0 ≤ B := by positivity
  have K0 : 0 ≤ K := by positivity
  have T0 := zero_le_one.trans T1
  have F0 : 0 ≤ F := by unfold F; positivity
  have eqF : F^4 = B*Real.sqrt (P*B)/P := by
    unfold F
    rw [mul_pow,← Real.rpow_mul_natCast B0,← Real.rpow_mul_natCast pp.le]
    norm_num
    rw [Real.sqrt_eq_rpow,Real.mul_rpow pp.le B0]
    have eqA : B^(3/2 : ℝ) = B^(1/2 : ℝ)*B := by
      rw [← Real.rpow_add_one' B0 (by norm_num : (1/2 : ℝ)+1 ≠ 0)]
      norm_num
    have eqP : P^(-(1/2) : ℝ) = P^(1/2 : ℝ)/P := by
      rw [← Real.rpow_sub_one pp.ne']
      norm_num
    rw [eqA,eqP]
    ring
  have binomial : 1+F^4 ≤ (1+F)^4 := by
    have d : 0 ≤ 4*F+6*F^2+4*F^3 := by positivity
    nlinarith only [d]
  have size : 1+inverseFibreBudget p A T ≤ (16*T^4)*(1+F)^4 := by
    have tpow : T ≤ T^4 := by simpa only [pow_one] using pow_le_pow_right₀ T1 (show 1 ≤ 4 by decide)
    unfold inverseFibreBudget
    change 1+2*T*(1+6*B*Real.sqrt (P*B)/P) ≤ _
    rw [show 6*B*Real.sqrt (P*B)/P = 6*F^4 from by rw [eqF]; ring]
    calc
      _ ≤ 3*T+12*T*F^4 := by nlinarith only [T1]
      _ ≤ 16*T*(1+F^4) := by nlinarith only [T0, mul_nonneg T0 (pow_nonneg F0 4)]
      _ ≤ 16*T*(1+F)^4 := mul_le_mul_of_nonneg_left binomial (by positivity)
      _ ≤ _ := by gcongr
  have Hfour : H^4 = K^3*P*B^2 := by
    unfold H
    rw [mul_pow,mul_pow,← Real.rpow_mul_natCast K0,← Real.rpow_mul_natCast pp.le,
      ← Real.rpow_mul_natCast B0]
    norm_num [Real.rpow_natCast]
  have power : (reciprocalBilinearBound p A S T)^4 =
      K^3*P*B^2*(1+inverseFibreBudget p A T) := by
    unfold reciprocalBilinearBound
    have rn : 0 ≤ 1+inverseFibreBudget p A T := by unfold inverseFibreBudget; positivity
    change ((K^3*P*B^2*(1+inverseFibreBudget p A T))^(1/4 : ℝ))^4 = _
    rw [← Real.rpow_mul_natCast (by positivity), show (1/4 : ℝ)*(4 : ℕ) = 1 by norm_num, Real.rpow_one]
  change reciprocalBilinearBound p A S T ≤ 2*T*H*(1+F)
  apply (pow_le_pow_iff_left₀ (by unfold reciprocalBilinearBound inverseFibreBudget; positivity)
    (by unfold H; positivity) (by decide : 4 ≠ 0)).mp
  rw [power,mul_pow,mul_pow,mul_pow,Hfour]
  calc
    _ ≤ (K^3*P*B^2)*((16*T^4)*(1+F)^4) := mul_le_mul_of_nonneg_left size (by positivity)
    _ = _ := by ring

end

end B13BoundedStepProductSavingProof

end

/- Bilinear inverse prime factor -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical ComplexConjugate

noncomputable section

def intIntervalModUnits (m : ℕ) (a b : ℤ) : Finset ℤ :=
  (Ioc a b).filter (fun (j : ℤ) => IsUnit (j : ZMod m))

end

end B13BoundedStepProductSavingProof

end

/- Right low coprime residue -/
section

namespace B13BoundedStepProductSavingProof

open DyadicMixedB4Scale
open scoped Classical

noncomputable section

theorem pair_residue_cast_of_coprime {n u v : ℕ} [NeZero v] (cop : u.Coprime v) :
    (pairResidue n u v : ZMod v) = (n : ZMod v)*(u : ZMod v)⁻¹ := by
  have bez := congrArg (fun z : ℤ => (z : ZMod v)) (Nat.gcd_eq_gcd_ab u v)
  rw [cop.gcd_eq_one] at bez
  have lin : (1 : ZMod v) = (u : ZMod v)*(Nat.gcdA u v : ZMod v) := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one, Nat.cast_one,
      ZMod.natCast_self, zero_mul, add_zero] using bez
  have inv : (u : ZMod v)⁻¹ = (Nat.gcdA u v : ZMod v) := ZMod.inv_eq_of_mul_eq_one _ _ _ lin.symm
  unfold pairResidue
  simp only [cop.gcd_eq_one, Nat.div_one, ZMod.intCast_mod, Int.cast_mul, Int.cast_natCast, inv]

theorem pair_residue_error_eq_centered_of_coprime {n u v l r p s : ℕ} [NeZero v]
    (cop : u.Coprime v) (order : pairLeftLower n u v l s ≤ pairLeftUpper n u v r p) :
    (pairResidueError n u v l r p s : ℂ) =
      centeredIntIntervalResidue v (pairLeftLower n u v l s) (pairLeftUpper n u v r p)
        ((n : ZMod v)*(u : ZMod v)⁻¹) := by
  rw [centered_int_interval_residue_fourier v order]
  unfold pairResidueError
  simp only [cop.gcd_eq_one,one_dvd,ite_true,Nat.div_one,ite_eq_left order]
  simp only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_intCast,Int.cast_natCast,
    Complex.ofReal_natCast]
  rw [residue_ramp_difference_fourier,pair_residue_cast_of_coprime cop]
  rfl

theorem right_low_full_prefix_of_cofactor_bound {n p d : ℕ} (h : n/p ≤ upperCut n) :
    n/rightLowWaveStep ⟨p,d⟩ ≤ upperCut n/d := by
  simpa only [Nat.div_div_eq_div_mul, rightLowWaveStep, Nat.mul_comm p d] using Nat.div_le_div_right (c := d) h

end

end B13BoundedStepProductSavingProof

end

/- Long cofactor inverse -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

def longCofactorSize (m p A S : ℕ) (T : ℝ) : ℝ :=
  reciprocalBilinearBound m A S T + (2*(S : ℝ)/(p : ℝ))*reciprocalBilinearBound m A p T

end

end B13BoundedStepProductSavingProof

end

/- Scaled composite hyperbola size -/
section

namespace B13BoundedStepProductSavingProof

noncomputable section

theorem long_cofactor_size_mul_modulus_le {p q A S : ℕ} {T : ℝ}
    (p0 : (0 : ℝ) < p) (m1 : 1 ≤ ((p*q : ℕ) : ℝ)) (T1 : 1 ≤ T) :
    let M := ((p*q : ℕ) : ℝ)
    let B := (A : ℝ)
    let Q := (q : ℝ)
    let Y := (S : ℝ)*M
    let X := Y^(3/4 : ℝ)
    longCofactorSize (p*q) p A S T*M ≤
      2*T*(X*M^(1/2 : ℝ)*B^(1/2 : ℝ)+X*M^(3/8 : ℝ)*B^(7/8 : ℝ)+
        2*Y*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+2*Y*Q^(1/4 : ℝ)*M^(-1/8 : ℝ)*B^(7/8 : ℝ)) := by
  dsimp only
  let P := ((p*q : ℕ) : ℝ)
  let C := (p : ℝ)
  let Q := (q : ℝ)
  let B := (A : ℝ)
  let K := (S : ℝ)
  let F := B^(3/8 : ℝ)*P^(-1/8 : ℝ)
  let Y := K*P
  let X := Y^(3/4 : ℝ)
  have pp : 0 < P := zero_lt_one.trans_le m1
  have B0 : 0 ≤ B := by positivity
  have F0 : 0 ≤ F := by unfold F; positivity
  have T0 := zero_le_one.trans T1
  have factorP : P*(K^(3/4 : ℝ)*P^(1/4 : ℝ)*B^(1/2 : ℝ)) = X*P^(1/2 : ℝ)*B^(1/2 : ℝ) := by
    have ex : P*P^(1/4 : ℝ) = P^(3/4 : ℝ)*P^(1/2 : ℝ) := by
      rw [mul_comm P, ← Real.rpow_add_one pp.ne', ← Real.rpow_add pp]
      norm_num
    unfold X Y
    rw [Real.mul_rpow (by positivity) pp.le]
    calc
      _ = K^(3/4 : ℝ)*(P*P^(1/4 : ℝ))*B^(1/2 : ℝ) := by ring
      _ = _ := by rw [ex]; ring
  have factorQ : ((2*K/C)*(C^(3/4 : ℝ)*P^(1/4 : ℝ)))*P = 2*Y*Q^(1/4 : ℝ) := by
    have cast : P = C*Q := by unfold P C Q; push_cast; rfl
    have powEq : P^(1/4 : ℝ) = C^(1/4 : ℝ)*Q^(1/4 : ℝ) := by
      rw [cast,Real.mul_rpow p0.le (by positivity)]
    have Cpos : 0 < C := p0
    have all : C^(3/4 : ℝ)*C^(1/4 : ℝ) = C := by rw [← Real.rpow_add Cpos]; norm_num
    rw [powEq]
    calc
      _ = ((2*K/C)*(C^(3/4 : ℝ)*C^(1/4 : ℝ)))*P*Q^(1/4 : ℝ) := by ring
      _ = _ := by rw [all,div_mul_cancel₀ _ p0.ne']; unfold Y; ring
  have bPower : B^(1/2 : ℝ)*B^(3/8 : ℝ) = B^(7/8 : ℝ) := by
    rw [← Real.rpow_add_of_nonneg B0 (by norm_num) (by norm_num)]
    norm_num
  have pPower : P^(1/2 : ℝ)*P^(-1/8 : ℝ) = P^(3/8 : ℝ) := by rw [← Real.rpow_add pp]; norm_num
  have term1 := reciprocal_bilinear_bound_le_separated (p := p*q) (S := S) m1 T1 (A := A)
  have term2 := reciprocal_bilinear_bound_le_separated (p := p*q) (S := p) m1 T1 (A := A)
  unfold longCofactorSize
  calc
    _ ≤ (2*T*(K^(3/4 : ℝ)*P^(1/4 : ℝ)*B^(1/2 : ℝ))*(1+F) +
        (2*K/C)*(2*T*(C^(3/4 : ℝ)*P^(1/4 : ℝ)*B^(1/2 : ℝ))*(1+F)))*P := by gcongr
    _ = 2*T*(X*P^(1/2 : ℝ)*B^(1/2 : ℝ)*(1+F)+2*Y*Q^(1/4 : ℝ)*B^(1/2 : ℝ)*(1+F)) := by
      calc
        _ = 2*T*((P*(K^(3/4 : ℝ)*P^(1/4 : ℝ)*B^(1/2 : ℝ)))*(1+F)+
          ((2*K/C)*(C^(3/4 : ℝ)*P^(1/4 : ℝ))*P)*B^(1/2 : ℝ)*(1+F)) := by ring
        _ = _ := by rw [factorP,factorQ]
    _ = 2*T*(X*P^(1/2 : ℝ)*B^(1/2 : ℝ)+X*P^(3/8 : ℝ)*B^(7/8 : ℝ)+
        2*Y*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+2*Y*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ)) := by
      unfold F
      calc
        _ = 2*T*(X*P^(1/2 : ℝ)*B^(1/2 : ℝ)+
          X*(P^(1/2 : ℝ)*P^(-1/8 : ℝ))*(B^(1/2 : ℝ)*B^(3/8 : ℝ))+
          2*Y*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+2*Y*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*(B^(1/2 : ℝ)*B^(3/8 : ℝ))) := by ring
        _ = _ := by rw [pPower,bPower]

end

end B13BoundedStepProductSavingProof

end

/- Expanded modulus hyperbola size -/
section

namespace B13BoundedStepProductSavingProof

noncomputable section

theorem scaled_long_cofactor_size_for_expanded_product {n p q A S d : ℕ} {x T : ℝ}
    (n1 : 1 ≤ (n : ℝ)) (p0 : (0 : ℝ) < p) (m1 : 1 ≤ ((p*q : ℕ) : ℝ)) (d1 : 1 ≤ (d : ℝ)) (T1 : 1 ≤ T)
    (mHi : ((p*q : ℕ) : ℝ) ≤ (n : ℝ)^(1/2+x/2-7/256))
    (mMid : ((p*q : ℕ) : ℝ) ≤ (n : ℝ)^(5/8-x/3)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ ((p*q : ℕ) : ℝ))
    (qCap : (q : ℝ) ≤ (n : ℝ)^(1/16 : ℝ))
    (xLo : 31/512 ≤ x) (xHi : x ≤ 1/4)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+3/512))
    (cofactorCap : (S : ℝ)*((p*q : ℕ) : ℝ)*(d : ℝ)^2 ≤ 2*(n : ℝ)^(513/512-x)) :
    longCofactorSize (p*q) p A S T ≤
      24*T*(n : ℝ)^(1015/1024 : ℝ)/(((p*q : ℕ) : ℝ)*(d : ℝ)^(3/2 : ℝ)) := by
  let N := (n : ℝ)
  let P := ((p*q : ℕ) : ℝ)
  let Q := (q : ℝ)
  let B := (A : ℝ)
  let K := (S : ℝ)
  let D := (d : ℝ)
  let Y := K*P*D^2
  let X := Y^(3/4 : ℝ)
  let H := N^(1015/1024 : ℝ)
  have np : 0 < N := zero_lt_one.trans_le n1
  have pp : 0 < P := zero_lt_one.trans_le m1
  have dp : 0 < D := zero_lt_one.trans_le d1
  have B0 : 0 ≤ B := by positivity
  have Y0 : 0 ≤ Y := by unfold Y; positivity
  have T0 := zero_le_one.trans T1
  have Ahalf : B^(1/2 : ℝ) ≤ N^((x+3/512)*(1/2)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow B0 aCap (by norm_num)
  have Aextra : B^(7/8 : ℝ) ≤ N^((x+3/512)*(7/8)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow B0 aCap (by norm_num)
  have Phalf : P^(1/2 : ℝ) ≤ N^((1/2+x/2-7/256)*(1/2)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow pp.le mHi (by norm_num)
  have Pthree : P^(3/8 : ℝ) ≤ N^((5/8-x/3)*(3/8)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow pp.le mMid (by norm_num)
  have Pneg : P^(-1/8 : ℝ) ≤ N^(-1/24 : ℝ) := by
    have cmp := Real.rpow_le_rpow (by positivity : 0 ≤ N^(1/3 : ℝ)) mLo (by norm_num : (0 : ℝ) ≤ 1/8)
    rw [← Real.rpow_mul np.le] at cmp
    norm_num at cmp
    rw [show (-1/8 : ℝ) = -(1/8 : ℝ) by ring, show (-1/24 : ℝ) = -(1/24 : ℝ) by ring,
      Real.rpow_neg pp.le, Real.rpow_neg np.le]
    have cast : P = (p : ℝ)*(q : ℝ) := by unfold P; push_cast; rfl
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (by simpa only [cast] using cmp)
  have xCap : X ≤ 2*N^((513/512-x)*(3/4)) := by
    calc
      _ ≤ (2*N^(513/512-x))^(3/4 : ℝ) := Real.rpow_le_rpow Y0 cofactorCap (by norm_num)
      _ = (2 : ℝ)^(3/4 : ℝ)*N^((513/512-x)*(3/4)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity),Real.rpow_mul np.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by positivity)
  have e1 : X*P^(1/2 : ℝ)*B^(1/2 : ℝ) ≤ 2*H := by
    calc
      _ ≤ (2*N^((513/512-x)*(3/4)))*N^((1/2+x/2-7/256)*(1/2))*N^((x+3/512)*(1/2)) := by gcongr
      _ = 2*N^((513/512-x)*(3/4)+(1/2+x/2-7/256)*(1/2)+(x+3/512)*(1/2)) := by
        rw [Real.rpow_add np,Real.rpow_add np]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)
  have e2 : X*P^(3/8 : ℝ)*B^(7/8 : ℝ) ≤ 2*H := by
    calc
      _ ≤ (2*N^((513/512-x)*(3/4)))*N^((5/8-x/3)*(3/8))*N^((x+3/512)*(7/8)) := by gcongr
      _ = 2*N^((513/512-x)*(3/4)+(5/8-x/3)*(3/8)+(x+3/512)*(7/8)) := by
        rw [Real.rpow_add np,Real.rpow_add np]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)
  have qQuarter : Q^(1/4 : ℝ) ≤ N^(1/64 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ Q) qCap (by norm_num : (0 : ℝ) ≤ 1/4)
    rw [← Real.rpow_mul np.le] at h
    norm_num at h ⊢
    exact h
  have e3 : 2*Y*Q^(1/4 : ℝ)*B^(1/2 : ℝ) ≤ 4*H := by
    calc
      _ ≤ 2*(2*N^(513/512-x))*N^(1/64 : ℝ)*N^((x+3/512)*(1/2)) := by gcongr
      _ = 4*N^((513/512-x)+1/64+(x+3/512)*(1/2)) := by rw [Real.rpow_add np,Real.rpow_add np]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)
  have e4 : 2*Y*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ) ≤ 4*H := by
    calc
      _ ≤ 2*(2*N^(513/512-x))*N^(1/64 : ℝ)*N^(-1/24 : ℝ)*N^((x+3/512)*(7/8)) := by gcongr
      _ = 4*N^((513/512-x)+1/64+(-1/24)+(x+3/512)*(7/8)) := by
        rw [Real.rpow_add np ((513/512-x)+1/64+(-1/24)), Real.rpow_add np ((513/512-x)+1/64) (-1/24),
          Real.rpow_add np (513/512-x) (1/64)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)

  have powerX : (K*P)^(3/4 : ℝ)*D^(3/2 : ℝ) = X := by
    unfold X Y
    have pow : (D^2)^(3/4 : ℝ) = D^(3/2 : ℝ) := by
      rw [← Real.rpow_natCast_mul dp.le 2]
      norm_num
    rw [Real.mul_rpow (by positivity : 0 ≤ K*P) (by positivity : 0 ≤ D^2),pow]
  have yd : (K*P)*D^(3/2 : ℝ) ≤ Y := by
    have dLe : D^(3/2 : ℝ) ≤ D^2 := calc
      _ ≤ D^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le d1 (by norm_num)
      _ = _ := by simpa only [Nat.cast_ofNat] using Real.rpow_natCast D 2
    exact mul_le_mul_of_nonneg_left dLe (by positivity)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < P*D^(3/2 : ℝ))).mpr
  change longCofactorSize (p*q) p A S T*(P*D^(3/2 : ℝ)) ≤ 24*T*H
  calc
    _ = (longCofactorSize (p*q) p A S T*P)*D^(3/2 : ℝ) := by ring
    _ ≤ (2*T*((K*P)^(3/4 : ℝ)*P^(1/2 : ℝ)*B^(1/2 : ℝ)+
      (K*P)^(3/4 : ℝ)*P^(3/8 : ℝ)*B^(7/8 : ℝ)+2*(K*P)*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+
        2*(K*P)*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ)))*D^(3/2 : ℝ) :=
      mul_le_mul_of_nonneg_right (long_cofactor_size_mul_modulus_le p0 m1 T1) (by positivity)
    _ = 2*T*(X*P^(1/2 : ℝ)*B^(1/2 : ℝ)+X*P^(3/8 : ℝ)*B^(7/8 : ℝ)+
        2*((K*P)*D^(3/2 : ℝ))*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+
        2*((K*P)*D^(3/2 : ℝ))*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ)) := by
      rw [← powerX]
      ring
    _ ≤ 2*T*(X*P^(1/2 : ℝ)*B^(1/2 : ℝ)+X*P^(3/8 : ℝ)*B^(7/8 : ℝ)+
        2*Y*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+2*Y*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ)) := by gcongr
    _ ≤ 2*T*(2*H+2*H+4*H+4*H) := by gcongr
    _ = _ := by ring

end

end B13BoundedStepProductSavingProof

end

/- Inverse frequency reduced period -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

def inverseFrequencyPeriod (m : ℕ) (c : ZMod m) : ℕ :=
  m/(m.gcd c.val)

theorem inverse_frequency_period_pos {m : ℕ} [NeZero m] (c : ZMod m) :
    0 < inverseFrequencyPeriod m c := by
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  exact Nat.div_pos (Nat.le_of_dvd m0 (Nat.gcd_dvd_left m c.val)) (Nat.gcd_pos_of_pos_left _ m0)

theorem unit_inverse_frequency_injOn_interval {m K : ℕ} [NeZero m]
    (c : ZMod m) (off : ℤ) (length : K ≤ inverseFrequencyPeriod m c)
    (J : Finset ℤ) (range : J ⊆ Ioc off (off+(K : ℤ)))
    (units : ∀ j ∈ J, IsUnit (j : ZMod m)) :
    Set.InjOn (fun j : ℤ => c*(j : ZMod m)⁻¹) J := by
  intro x hx y hy eq
  have uX := units x hx
  have uY := units y hy
  have mult : c*(x : ZMod m)=c*(y : ZMod m) := by
    have h := congrArg (fun z : ZMod m => z*((x : ZMod m)*(y : ZMod m))) eq
    have a : (c*(x : ZMod m)⁻¹)*((x : ZMod m)*(y : ZMod m))=c*(y : ZMod m) := by
      rw [mul_assoc,← mul_assoc ((x : ZMod m)⁻¹),ZMod.inv_mul_of_unit _ uX,one_mul]
    have b : (c*(y : ZMod m)⁻¹)*((x : ZMod m)*(y : ZMod m))=c*(x : ZMod m) := by
      rw [mul_comm (x : ZMod m) (y : ZMod m),mul_assoc,← mul_assoc ((y : ZMod m)⁻¹),
        ZMod.inv_mul_of_unit _ uY,one_mul]
    change (c*(x : ZMod m)⁻¹)*((x : ZMod m)*(y : ZMod m)) =
      (c*(y : ZMod m)⁻¹)*((x : ZMod m)*(y : ZMod m)) at h
    rw [a,b] at h
    exact h.symm
  have natval : (((c.val : ℕ) : ℤ) : ZMod m)=c := by
    rw [Int.cast_natCast,ZMod.natCast_val,ZMod.cast_id]
  have modEq : (c.val : ℤ)*x ≡ (c.val : ℤ)*y [ZMOD (m : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa only [Int.cast_mul,natval] using mult)
  have m0 : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  let p := inverseFrequencyPeriod m c
  have pEq : ((m : ℤ)/(Int.gcd (m : ℤ) (c.val : ℤ) : ℤ)) = (p : ℤ) := by
    unfold p inverseFrequencyPeriod
    rw [Int.natCast_ediv]
    rfl
  have eq' : x ≡ y [ZMOD (p : ℤ)] := by
    rw [← pEq]
    exact Int.ModEq.cancel_left_div_gcd m0 modEq
  have shifted : x-(off+1) ≡ y-(off+1) [ZMOD (p : ℤ)] :=
    eq'.sub (Int.ModEq.refl _)
  have xdata := mem_Ioc.mp (range hx)
  have ydata := mem_Ioc.mp (range hy)
  have bound : (K : ℤ) ≤ (p : ℤ) := by exact_mod_cast length
  have xlo : 0 ≤ x-(off+1) := by omega
  have ylo : 0 ≤ y-(off+1) := by omega
  have xhi : x-(off+1) < (p : ℤ) := by omega
  have yhi : y-(off+1) < (p : ℤ) := by omega
  change (x-(off+1))%(p : ℤ)=(y-(off+1))%(p : ℤ) at shifted
  rw [Int.emod_eq_of_lt xlo xhi,Int.emod_eq_of_lt ylo yhi] at shifted
  omega

end

end B13BoundedStepProductSavingProof

end

/- Reciprocal small composite fibre -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Reciprocal small order mass -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Reciprocal composite fourth moment -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Reduced period gated inverse -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

theorem norm_gated_inverse_energy_on_period_span {m p A S : ℕ} [NeZero m]
    (c : ZMod m) (pCap : p ≤ inverseFrequencyPeriod m c)
    (Sp : S ≤ p) (L : ℤ) (I : Finset ℕ) (J : Finset ℤ) (Jrange : J ⊆ Ioc L (L+(S : ℤ)))
    (units : ∀ j ∈ J, IsUnit (j : ZMod m))
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {W V T : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (T0 : 0 ≤ T)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ W) (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (fourthMoment : ∀ (weight : ℕ → ℂ) {X : ℝ}, 0 ≤ X → (∀ i ∈ I, ‖weight i‖ ≤ X) →
      (∑ x : ZMod m, ‖inverseFrequencySum m I weight x‖^4) ≤
        (m : ℝ)*(A : ℝ)^2*(1+inverseFibreBudget m A T)*X^4) :
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹))‖ ≤
      (2+Real.log m)*W*V*reciprocalBilinearBound m A J.card T := by
  let ψ (j : ℤ) := c*(j : ZMod m)⁻¹
  have inj : Set.InjOn ψ J := unit_inverse_frequency_injOn_interval c L (Sp.trans pCap) J Jrange units
  have Sm : S ≤ m := Sp.trans (pCap.trans (Nat.div_le_self _ _))
  have phase (i : ℕ) (j : ℤ) : c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹ = ψ j*(i : ZMod m)⁻¹ := by
    unfold ψ
    ring
  simp only [phase]
  exact norm_gated_translated_frequency_sum_le_of_fourth_moment Sm L I J Jrange ψ inj α β lo hi W0 V0 T0
    aw bw fourthMoment

theorem norm_gated_inverse_energy_on_reduced_long_interval {m p A S : ℕ} [NeZero m]
    (c : ZMod m) (pCap : p ≤ inverseFrequencyPeriod m c) (p0 : 0 < p)
    (I : Finset ℕ) (J : Finset ℤ) (Jrange : J ⊆ Ioc 0 (S : ℤ))
    (units : ∀ j ∈ J, IsUnit (j : ZMod m))
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {W V T : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (T0 : 0 ≤ T)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ W) (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (fourthMoment : ∀ (weight : ℕ → ℂ) {X : ℝ}, 0 ≤ X → (∀ i ∈ I, ‖weight i‖ ≤ X) →
      (∑ x : ZMod m, ‖inverseFrequencySum m I weight x‖^4) ≤
        (m : ℝ)*(A : ℝ)^2*(1+inverseFibreBudget m A T)*X^4) :
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹))‖ ≤
      ((S/p+1 : ℕ) : ℝ)*((2+Real.log m)*W*V*reciprocalBilinearBound m A p T) := by
  let R := range (S/p+1)
  let tag (j : ℤ) := (j-1).toNat/p
  let K (k : ℕ) := J.filter (fun j => tag j = k)
  let g (i : ℕ) (j : ℤ) := ZMod.stdAddChar (c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹)
  let F (k : ℕ) := gatedBilinearSum I (K k) α β lo hi g
  have m1 : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  have log0 := Real.log_nonneg m1
  have tags (j : ℤ) (hj : j ∈ J) : tag j ∈ R := by
    have data := mem_Ioc.mp (Jrange hj)
    have k : (j-1).toNat ≤ S := by omega
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right k))
  have geometry (k : ℕ) :
      K k ⊆ Ioc ((k*p : ℕ) : ℤ) (((k*p : ℕ) : ℤ)+(p : ℤ)) := by
    intro j hj
    obtain ⟨base,eq⟩ := mem_filter.mp hj
    have source := mem_Ioc.mp (Jrange base)
    have j0 : 0 ≤ j-1 := by omega
    have jcast : ((j-1).toNat : ℤ) = j-1 := Int.toNat_of_nonneg j0
    have start : ((k*p : ℕ) : ℤ) ≤ ((j-1).toNat : ℤ) := by
      have h := Nat.div_mul_le_self (j-1).toNat p
      change tag j*p ≤ (j-1).toNat at h
      rw [eq] at h
      exact_mod_cast h
    have ending : ((j-1).toNat : ℤ) < (((k+1)*p : ℕ) : ℤ) := by
      have h : tag j < k+1 := by rw [eq]; omega
      exact_mod_cast (Nat.div_lt_iff_lt_mul p0).mp h
    rw [jcast,Nat.add_mul,one_mul,Nat.cast_add] at ending
    rw [jcast] at start
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  have Kcard (k : ℕ) : #(K k) ≤ p := by
    refine (card_le_card (geometry k)).trans_eq ?_
    rw [Int.card_Ioc, show (((k*p : ℕ) : ℤ)+(p : ℤ))-((k*p : ℕ) : ℤ) = (p : ℤ) by omega,
      Int.toNat_natCast]
  have each (k : ℕ) : ‖F k‖ ≤ (2+Real.log m)*W*V*reciprocalBilinearBound m A p T := by
    have est := norm_gated_inverse_energy_on_period_span c pCap le_rfl ((k*p : ℕ) : ℤ) I (K k)
      (geometry k) (fun j hj => units j (mem_filter.mp hj).1) α β lo hi W0 V0 T0 aw
      (fun j hj => bw j (mem_filter.mp hj).1) fourthMoment
    exact est.trans (mul_le_mul_of_nonneg_left (reciprocal_bilinear_bound_mono_card T0 (Kcard k)) (by positivity))
  have grouped : gatedBilinearSum I J α β lo hi g = ∑ k ∈ R, F k := by
    unfold F K gatedBilinearSum
    exact (sum_fiberwise_of_maps_to tags _).symm
  rw [grouped]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun k _ => each k).trans_eq ?_)
  simp [R,nsmul_eq_mul]

theorem norm_gated_long_cofactor_inverse_le_with_reduced_period {m p A S : ℕ} [NeZero m]
    (c : ZMod m) (pCap : p ≤ inverseFrequencyPeriod m c) (pPos : 0 < p)
    (I : Finset ℕ) (J : Finset ℤ) (Jrange : J ⊆ Ioc 0 (S : ℤ))
    (units : ∀ j ∈ J, IsUnit (j : ZMod m))
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {W V T : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (T0 : 0 ≤ T)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ W) (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (moment : ∀ (weight : ℕ → ℂ) {X : ℝ}, 0 ≤ X → (∀ i ∈ I, ‖weight i‖ ≤ X) →
      (∑ x : ZMod m, ‖inverseFrequencySum m I weight x‖^4) ≤
        (m : ℝ)*(A : ℝ)^2*(1+inverseFibreBudget m A T)*X^4) :
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹))‖ ≤
      (2+Real.log m)*W*V*longCofactorSize m p A S T := by
  let B := longCofactorSize m p A S T
  let M := (2+Real.log m)*W*V
  have mPos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have pp : (0 : ℝ) < p := by exact_mod_cast pPos
  have log0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast mPos)
  have M0 : 0 ≤ M := by unfold M; positivity
  have bound0 (K : ℕ) : 0 ≤ reciprocalBilinearBound m A K T := by
    unfold reciprocalBilinearBound inverseFibreBudget
    positivity
  by_cases cap : S ≤ p
  · have rank : J.card ≤ S := (card_le_card Jrange).trans_eq (by
      rw [Int.card_Ioc,sub_zero,Int.toNat_natCast])
    have leB : reciprocalBilinearBound m A J.card T ≤ B :=
      (reciprocal_bilinear_bound_mono_card T0 rank).trans (by
        unfold B longCofactorSize
        exact le_add_of_nonneg_right (mul_nonneg (by positivity) (bound0 p)))
    have est := norm_gated_inverse_energy_on_period_span c pCap cap 0 I J
      (by simpa only [zero_add] using Jrange) units α β lo hi W0 V0 T0 aw bw moment
    exact est.trans (mul_le_mul_of_nonneg_left leB M0)
  · have pS : (p : ℝ) ≤ S := by exact_mod_cast (le_of_not_ge cap)
    have est := norm_gated_inverse_energy_on_reduced_long_interval c pCap pPos I J Jrange units
      α β lo hi W0 V0 T0 aw bw moment
    have divBound : ((S/p : ℕ) : ℝ) ≤ (S : ℝ)/(p : ℝ) :=
      (le_div_iff₀ pp).mpr (by exact_mod_cast Nat.div_mul_le_self S p)
    have oneBound : 1 ≤ (S : ℝ)/(p : ℝ) := (le_div_iff₀ pp).mpr (by simpa only [one_mul] using pS)
    have blocks : ((S/p+1 : ℕ) : ℝ) ≤ 2*(S : ℝ)/(p : ℝ) := by
      push_cast
      rw [mul_div_assoc]
      linarith only [divBound,oneBound]
    refine est.trans ?_
    change ((S/p+1 : ℕ) : ℝ)*(M*reciprocalBilinearBound m A p T) ≤ M*B
    calc
      _ ≤ (2*(S : ℝ)/(p : ℝ))*(M*reciprocalBilinearBound m A p T) :=
        mul_le_mul_of_nonneg_right blocks (mul_nonneg M0 (bound0 _))
      _ = M*((2*(S : ℝ)/(p : ℝ))*reciprocalBilinearBound m A p T) := by ring
      _ ≤ _ := by
        unfold B longCofactorSize
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (bound0 _)) M0

end

end B13BoundedStepProductSavingProof

end

/- Fourier phase gcd -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Fourier large divisor bound -/
section

namespace B13BoundedStepProductSavingProof

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
        (add_le_add_right) (Real.log_le_log (by exact_mod_cast q0 : (0 : ℝ) < q)
          (by exact_mod_cast Nat.div_le_self m d : (q : ℝ) ≤ m)) 1
      calc
        _ ≤ ((1 : ℝ)/d)*(1+Real.log m) := mul_le_mul_of_nonneg_left cmp (by positivity)
        _ = _ := by ring

theorem sum_norm_interval_coefficients_with_large_gcd_le {m : ℕ} [NeZero m] (D : ℕ) (a b : ℤ) :
    (∑ h ∈ ((univ : Finset (ZMod m)).filter (fun h => h ≠ 0)).filter (fun h => D < m.gcd h.val),
      ‖intIntervalFourierCoefficient m a b h‖) ≤
        (m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1) := by
  let H := (univ : Finset (ZMod m)).filter fun h => h ≠ 0
  let B := H.filter fun h => D < m.gcd h.val
  let J := m.divisors.filter fun d => D < d
  let F (h : ZMod m) := ‖intIntervalFourierCoefficient m a b h‖
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have L0 : 0 ≤ 1+Real.log (m : ℝ) := add_nonneg zero_le_one
    (Real.log_nonneg (by exact_mod_cast m0))
  have cover (h : ZMod m) (hh : h ∈ H) :
      (if D < m.gcd h.val then F h else 0) ≤ ∑ d ∈ J, if d ∣ h.val then F h else 0 := by
    by_cases hD : D < m.gcd h.val
    · let d := m.gcd h.val
      have dm : d ∈ J :=
        mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,m0.ne'⟩,hD⟩
      rw [ite_eq_left hD]
      have leading : ∀ a ∈ J, (0 : ℝ) ≤ (if a ∣ h.val then F h else 0) := by
        intro a ha
        split_ifs <;> positivity
      have dh : d ∣ h.val := Nat.gcd_dvd_right _ _
      exact (ite_eq_left dh).symm.le.trans (single_le_sum leading dm)
    · rw [ite_eq_right hD]
      exact sum_nonneg fun d _ => by split_ifs <;> positivity
  have each (d : ℕ) (hd : d ∈ J) :
      (∑ h ∈ H.filter (fun h => d ∣ h.val), F h) ≤ (1+Real.log m)/((D : ℝ)+1) := by
    obtain ⟨base,above⟩ := mem_filter.mp hd
    have dm := (Nat.mem_divisors.mp base).1
    have d0 : 0 < d := (Nat.zero_le _).trans_lt above
    have div_le : (D : ℝ)+1 ≤ (d : ℝ) := by exact_mod_cast Nat.succ_le_of_lt above
    exact (sum_norm_interval_coefficients_at_divisor_multiples_le d0 dm a b).trans
      (div_le_div_of_nonneg_left L0 (by positivity) div_le)
  change (∑ h ∈ B, F h) ≤ _
  unfold B
  rw [sum_filter]
  calc
    _ ≤ ∑ h ∈ H, ∑ d ∈ J, if d ∣ h.val then F h else 0 := sum_le_sum cover
    _ = ∑ d ∈ J, ∑ h ∈ H.filter (fun h => d ∣ h.val), F h := by
      rw [sum_comm]
      simp only [sum_filter]
    _ ≤ ∑ _ ∈ J, (1+Real.log (m : ℝ))/((D : ℝ)+1) := sum_le_sum each
    _ = (J.card : ℝ)*((1+Real.log (m : ℝ))/((D : ℝ)+1)) := by simp
    _ ≤ (m.divisors.card : ℝ)*((1+Real.log (m : ℝ))/((D : ℝ)+1)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card (filter_subset _ m.divisors)) (by positivity)
    _ = _ := by ring

end

end B13BoundedStepProductSavingProof

end

/- Weighted residue divisor split -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

theorem norm_gated_unit_residue_of_divisor_frequency_bound {m : ℕ} [NeZero m]
    (D : ℕ) {c : ZMod m}
    {ι : Type*} (I : Finset ι) (a : ι → ZMod m) (units : ∀ i ∈ I, IsUnit (a i))
    (α : ι → ℂ) (β : ℤ → ℂ) (lo hi : ι → ℤ) {L R v w : ℤ}
    (hvw : v ≤ w) {B : ℝ} (B0 : 0 ≤ B)
    (bound : ∀ h : ZMod m, h ≠ 0 → m.gcd h.val ≤ D →
      ‖gatedBilinearSum I (intIntervalModUnits m L R) α β lo hi
        (fun i j => ZMod.stdAddChar ((-(h*c))*(a i)⁻¹*(j : ZMod m)⁻¹))‖ ≤ B) :
    let J := intIntervalModUnits m L R
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => centeredIntIntervalResidue m v w (c*(a i*(j : ZMod m))⁻¹))‖ ≤
      (1+Real.log (m : ℕ))*B+
        ((m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1))*((∑ i ∈ I, ‖α i‖)*(∑ j ∈ J, ‖β j‖)) := by
  dsimp only
  let J := intIntervalModUnits m L R
  let H := (univ : Finset (ZMod m)).filter fun h => h ≠ 0
  let C (h : ZMod m) := intIntervalFourierCoefficient m v w h
  let f (h : ZMod m) (i : ι) (j : ℤ) := ZMod.stdAddChar ((-(h*c))*(a i)⁻¹*(j : ZMod m)⁻¹)
  let F (h : ZMod m) := gatedBilinearSum I J α β lo hi (f h)
  let mass := (∑ i ∈ I, ‖α i‖)*(∑ j ∈ J, ‖β j‖)
  have mass0 : 0 ≤ mass := by unfold mass; positivity
  have point (i : ι) (hiI : i ∈ I) (j : ℤ) (hj : j ∈ J) :
      (if lo i < j ∧ j ≤ hi i then
        α i*centeredIntIntervalResidue m v w (c*(a i*(j : ZMod m))⁻¹) else 0) =
      ∑ h ∈ H, C h*(if lo i < j ∧ j ≤ hi i then α i*f h i j else 0) := by
    by_cases gate : lo i < j ∧ j ≤ hi i
    · rw [ite_eq_left gate, centered_int_interval_residue_fourier m hvw, mul_sum]
      have jun : IsUnit (j : ZMod m) := by
        have h : j ∈ Ioc L R ∧ IsUnit (j : ZMod m) := by
          simpa only [J, intIntervalModUnits, mem_filter] using hj
        exact h.2
      have prodInv : (a i*(j : ZMod m))⁻¹ = (a i)⁻¹*(j : ZMod m)⁻¹ := by
        apply ZMod.inv_eq_of_mul_eq_one
        calc
          _ = ((a i)*(a i)⁻¹)*((j : ZMod m)*(j : ZMod m)⁻¹) := by ring
          _ = _ := by
            rw [ZMod.mul_inv_of_unit _ (units i hiI), ZMod.mul_inv_of_unit _ jun, one_mul]
      refine sum_congr rfl fun h _ => ?_
      have phase : -(h*(c*(a i*(j : ZMod m))⁻¹)) = -(h*c)*(a i)⁻¹*(j : ZMod m)⁻¹ := by rw [prodInv]; ring
      rw [ite_eq_left gate,phase]
      unfold C f
      ring
    · simp [gate]
  have expansion : gatedBilinearSum I J α β lo hi
        (fun i j => centeredIntIntervalResidue m v w (c*(a i*(j : ZMod m))⁻¹)) = ∑ h ∈ H, C h*F h := by
    calc
      _ = ∑ j ∈ J, β j*(∑ i ∈ I,∑ h ∈ H, C h*(if lo i < j ∧ j ≤ hi i then α i*f h i j else 0)) := by
        unfold gatedBilinearSum
        refine sum_congr rfl fun j hj => congrArg (fun z : ℂ => β j*z) (sum_congr rfl fun i hiI => point i hiI j hj)
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
        rw [← mul_sum]
        rfl
  have trivial (h : ZMod m) : ‖F h‖ ≤ mass := by
    unfold F gatedBilinearSum
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ j ∈ J, ‖β j‖*(∑ i ∈ I, ‖α i‖) := by
        refine sum_le_sum fun j _ => ?_
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)) (norm_nonneg _)
        split_ifs
        · rw [norm_mul, norm_stdAddChar_eq_one,mul_one]
        · simp
      _ = _ := by rw [← sum_mul]; exact mul_comm _ _
  have pointBound (h : ZMod m) (hh : h ∈ H) : ‖F h‖ ≤ B + if D < m.gcd h.val then mass else 0 := by
    by_cases hb : D < m.gcd h.val
    · rw [ite_eq_left hb]
      exact (trivial h).trans (le_add_of_nonneg_left B0)
    · rw [ite_eq_right hb, add_zero]
      exact bound h (mem_filter.mp hh).2 (le_of_not_gt hb)
  change ‖gatedBilinearSum I J α β lo hi (fun i j => centeredIntIntervalResidue m v w
    (c*(a i*(j : ZMod m))⁻¹))‖ ≤ (1+Real.log m)*B + ((m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1))*mass
  rw [expansion]
  calc
    _ ≤ ∑ h ∈ H, ‖C h*F h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ H, ‖C h‖*(B + if D < m.gcd h.val then mass else 0) := by
      refine sum_le_sum fun h hh => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (pointBound h hh) (norm_nonneg _)
    _ = (∑ h ∈ H, ‖C h‖)*B +
        (∑ h ∈ H.filter (fun h => D < m.gcd h.val), ‖C h‖)*mass := by
      simp only [mul_add,sum_add_distrib]
      apply congrArg₂ (·+·)
      · exact (sum_mul ..).symm
      · calc
          _ = ∑ h ∈ H, if D < m.gcd h.val then ‖C h‖*mass else 0 := by
            refine sum_congr rfl fun h _ => ?_
            split_ifs <;> simp
          _ = _ := by rw [←sum_filter, sum_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (sum_norm_int_interval_fourier_coefficient_le m v w) B0)
      (mul_le_mul_of_nonneg_right (sum_norm_interval_coefficients_with_large_gcd_le D v w) mass0)

end

end B13BoundedStepProductSavingProof

end

/- Expanded modulus fixed residue -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

theorem norm_gated_composite_expanded_product_fixed_endpoints_le {n m g A S : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/128 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(1/2+x/2-7/256))
    (mMid : (m : ℝ) ≤ (n : ℝ)^(5/8-x/3)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ))
    (xLo : 31/512 ≤ x) (xHi : x ≤ 1/4) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+3/512))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512-x))
    (A0 : 0 < A) (Am : A < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ) {a b : ℤ} (ab : a ≤ b)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ T) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T*L)
    (divisors : ∀ z ≤ 4*m^3, (z.divisors.card : ℝ) ≤ T) :
    ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun i j => centeredIntIntervalResidue m a b (c*((i : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      98*(n : ℝ)^(1015/1024 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)^(3/2 : ℝ)) := by
  let N := (n : ℝ)
  let M := (m : ℝ)
  let G := (g : ℝ)
  let H := N^(1015/1024 : ℝ)
  let D := ⌊N^(1/32 : ℝ)⌋₊
  let B := 96*H*T^3*L^2/(M*G^(3/2 : ℝ))
  let J := intIntervalModUnits m 0 S
  have np : 0 < N := zero_lt_one.trans_le n1
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have m1 : 1 ≤ M := show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast m0
  have mp : 0 < M := zero_lt_one.trans_le m1
  have gp : 0 < G := zero_lt_one.trans_le g1
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans L1
  have log0 := Real.log_nonneg m1
  have log2 : 2+Real.log (m : ℝ) ≤ 2*L := by linarith only [L1,logBound]
  have B0 : 0 ≤ B := by unfold B H; positivity
  have jProp (j : ℤ) (hj : j ∈ J) : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hj
  have uniform (h : ZMod m) (_ : h ≠ 0) (good : m.gcd h.val ≤ D) :
      ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar ((-(h*c))*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹))‖ ≤ B := by
    let z := -(h*c)
    let q := m.gcd z.val
    let p := inverseFrequencyPeriod m z
    have product : p*q=m := Nat.div_mul_cancel (Nat.gcd_dvd_left m z.val)
    have p0 : 0 < p := inverse_frequency_period_pos z
    have pr : (0 : ℝ) < p := by exact_mod_cast p0
    have a : (m.gcd h.val : ℝ) ≤ N^(1/32 : ℝ) :=
      (by exact_mod_cast good : (m.gcd h.val : ℝ) ≤ (D : ℝ)).trans (Nat.floor_le (by positivity))
    have qCap : (q : ℝ) ≤ N^(1/16 : ℝ) := calc
      _ ≤ (m.gcd h.val : ℝ)*(m.gcd c.val : ℝ) := by
        change (m.gcd (-(h*c)).val : ℝ) ≤ _
        exact_mod_cast gcd_fourier_phase_product_le h c
      _ ≤ N^(1/32 : ℝ)*N^(1/128 : ℝ) := mul_le_mul a charBound (by positivity) (by positivity)
      _ ≤ _ := by rw [← Real.rpow_add np]; exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
    have long := scaled_long_cofactor_size_for_expanded_product (n := n) (p := p) (q := q) (A := A) (S := S)
      (d := g) (T := 2*T) n1 pr (by simpa only [product] using m1) g1 (by linarith)
      (by simpa only [product] using mHi) (by simpa only [product] using mMid)
      (by simpa only [product] using mLo) qCap xLo xHi aCap
      (by simpa only [product] using cofactorCap)
    have long' : longCofactorSize m p A S (2*T) ≤ 24*(2*T)*H/(M*G^(3/2 : ℝ)) := by
      simpa only [product,H,M,G] using long
    have long0 : 0 ≤ longCofactorSize m p A S (2*T) := by
      unfold longCofactorSize reciprocalBilinearBound inverseFibreBudget
      positivity
    have est := norm_gated_long_cofactor_inverse_le_with_reduced_period z (p := p) le_rfl p0 I J
      (fun j hj => (jProp j hj).1) (fun j hj => (jProp j hj).2) α β lo hi T0 (mul_nonneg T0 L0)
      (by positivity : 0 ≤ 2*T) aw bw
      (fun weight {_} X0 xw => inverse_frequency_fourth_moment_composite_le A0 Am I Icap copI weight X0 xw T1 divisors)
    refine est.trans ?_
    calc
      _ ≤ (2*L)*T*(T*L)*(24*(2*T)*H/(M*G^(3/2 : ℝ))) := by gcongr
      _ = _ := by unfold B; ring
  have est := norm_gated_unit_residue_of_divisor_frequency_bound D I (fun i => (i : ZMod m))
    (fun i hi => (ZMod.isUnit_iff_coprime _ _).mpr (copI i hi)) α β lo hi
    (L := 0) (R := (S : ℤ)) ab B0 uniform
  have lMass : (∑ i ∈ I, ‖α i‖) ≤ (A : ℝ)*T := calc
    _ ≤ ∑ _ ∈ I, T := sum_le_sum aw
    _ = (I.card : ℝ)*T := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (card_le_card Icap).trans_eq (by simp [Nat.card_Icc])) T0
  have jSub : J ⊆ Ioc (0 : ℤ) (S : ℤ) := fun j hj => (jProp j hj).1
  have jSize : (J.card : ℝ) ≤ S := by
    exact_mod_cast (card_le_card jSub).trans_eq (by rw [Int.card_Ioc,sub_zero,Int.toNat_natCast])
  have rMass : (∑ j ∈ J, ‖β j‖) ≤ (S : ℝ)*(T*L) := calc
    _ ≤ ∑ _ ∈ J, T*L := sum_le_sum bw
    _ = (J.card : ℝ)*(T*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right jSize (by positivity)
  have div_m : (m.divisors.card : ℝ) ≤ T := divisors m (by
    have h : m ≤ m^3 := by simpa only [pow_one] using pow_le_pow_right₀ m0 (show 1 ≤ 3 by decide)
    omega)
  have divisorFactor : (m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1) ≤ T*L/N^(1/32 : ℝ) := by
    have d : N^(1/32 : ℝ) ≤ (D : ℝ)+1 := (Nat.lt_floor_add_one (N^(1/32 : ℝ))).le
    calc
      _ ≤ T*L/((D : ℝ)+1) := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) d
  have core : (A : ℝ)*(S : ℝ) ≤ 2*N^(513/512+3/512 : ℝ)/(M*G^2) := by
    apply (le_div_iff₀ (by positivity : 0 < M*G^2)).mpr
    calc
      _ = (A : ℝ)*((S : ℝ)*M*G^2) := by ring
      _ ≤ N^(x+3/512)*(2*N^(513/512-x)) := mul_le_mul aCap cofactorCap (by positivity) (by positivity)
      _ = _ := by
        have sum : N^(x+3/512)*N^(513/512-x) = N^(513/512+3/512 : ℝ) := by rw [← Real.rpow_add np]; congr 1; ring
        calc
          _ = 2*(N^(x+3/512)*N^(513/512-x)) := by ring
          _ = _ := by rw [sum]
  have gpow : G^(3/2 : ℝ) ≤ G^2 := by
    rw [← Real.rpow_natCast G 2]
    exact Real.rpow_le_rpow_of_exponent_le g1 (by norm_num)
  have tail : ((m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1))*
       ((∑ i ∈ I, ‖α i‖)*(∑ j ∈ J, ‖β j‖)) ≤ 2*H*T^3*L^3/(M*G^(3/2 : ℝ)) := by
    calc
      _ ≤ (T*L/N^(1/32 : ℝ))*(((A : ℝ)*T)*((S : ℝ)*(T*L))) := by gcongr
      _ = (T*L/N^(1/32 : ℝ))*(((A : ℝ)*(S : ℝ))*T^2*L) := by ring
      _ ≤ (T*L/N^(1/32 : ℝ))*((2*N^(513/512+3/512 : ℝ)/(M*G^2))*T^2*L) := by gcongr
      _ = 2*N^(500/512 : ℝ)*T^3*L^2/(M*G^2) := by
        have pow : N^(513/512+3/512 : ℝ)/N^(1/32 : ℝ)=N^(500/512 : ℝ) := by rw [← Real.rpow_sub np]; norm_num
        rw [← pow]
        ring
      _ ≤ _ := by
        have h : N^(500/512 : ℝ) ≤ H := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        have l : L^2 ≤ L^3 := pow_le_pow_right₀ L1 (by decide)
        gcongr
  exact est.trans ((add_le_add (mul_le_mul_of_nonneg_right logBound B0) tail).trans_eq (by unfold B H; ring))

end

end B13BoundedStepProductSavingProof

end

/- Weighted unit ratio product interval -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Prime left budget -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

theorem gated_left_weight_mass_le {I : Finset ℕ} {J : Finset ℤ}
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ) {r : ℕ} {T A B : ℝ}
    (A0 : 0 ≤ A) (B0 : 0 ≤ B)
    (dBound : ∀ u ∈ Icc 1 r, (u.divisors.card : ℝ) ≤ T)
    (apos : ∀ a ∈ I, 0 < a) (jnonneg : ∀ j ∈ J, 0 ≤ j)
    (arange : ∀ a ∈ I, ∀ j ∈ J, lo a < j ∧ j ≤ hi a → a*j.toNat ∈ Icc 1 r)
    (aw : ∀ a ∈ I, ‖α a‖ ≤ A) (bw : ∀ j ∈ J, ‖β j‖ ≤ B) :
    (∑ j ∈ J, ‖β j‖*∑ a ∈ I, if lo a < j ∧ j ≤ hi a then ‖α a‖ else 0) ≤
      (r : ℝ)*T*A*B := by
  let P := (J ×ˢ I).filter fun t => lo t.2 < t.1 ∧ t.1 ≤ hi t.2
  let step (t : ℤ × ℕ) := t.2*t.1.toNat
  have weighted : (∑ j ∈ J, ‖β j‖*∑ a ∈ I, if lo a < j ∧ j ≤ hi a then ‖α a‖ else 0) =
      ∑ t ∈ P, ‖β t.1‖*‖α t.2‖ := by
    unfold P
    rw [sum_filter, sum_product]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  have rangeP (t : ℤ × ℕ) (ht : t ∈ P) : step t ∈ Icc 1 r := by
    obtain ⟨hj,ha⟩ := mem_product.mp (mem_filter.mp ht).1
    exact arange t.2 ha t.1 hj (mem_filter.mp ht).2
  have cardP : (#P : ℝ) ≤ (r : ℝ)*T := by
    have grouped : #P = ∑ u ∈ Icc 1 r, #(P.filter fun t => step t = u) :=
      card_eq_sum_card_fiberwise rangeP
    rw [grouped, Nat.cast_sum]
    calc
      _ ≤ ∑ _ ∈ Icc 1 r, T := by
        refine sum_le_sum fun u hu => ?_
        have hU : 0 < u := (mem_Icc.mp hu).1
        have fibre : #(P.filter fun t => step t = u) ≤ u.divisors.card := by
          refine card_le_card_of_injOn (fun (t : ℤ × ℕ) => t.2) ?_ ?_
          · intro t ht
            exact Nat.mem_divisors.mpr ⟨⟨t.1.toNat, (mem_filter.mp ht).2.symm⟩, hU.ne'⟩
          · intro t ht w hw same
            have tmem := mem_product.mp (mem_filter.mp (mem_filter.mp ht).1).1
            have wmem := mem_product.mp (mem_filter.mp (mem_filter.mp hw).1).1
            change t.2 = w.2 at same
            have both : t.2*t.1.toNat = w.2*w.1.toNat :=
              (mem_filter.mp ht).2.trans (mem_filter.mp hw).2.symm
            rw [← same] at both
            have fst := mul_left_cancel₀ (apos _ tmem.2).ne' both
            have fstExact : t.1 = w.1 := by
              rw [← Int.toNat_of_nonneg (jnonneg _ tmem.1), ← Int.toNat_of_nonneg (jnonneg _ wmem.1), fst]
            exact Prod.ext fstExact same
        exact (by exact_mod_cast fibre : (#(P.filter fun t => step t = u) : ℝ) ≤ u.divisors.card).trans
          (dBound u hu)
      _ = _ := by simp [Nat.card_Icc]
  rw [weighted]
  calc
    _ ≤ ∑ _ ∈ P, A*B := by
      refine sum_le_sum fun t ht => ?_
      obtain ⟨hj,ha⟩ := mem_product.mp (mem_filter.mp ht).1
      simpa only [mul_comm] using mul_le_mul (aw t.2 ha) (bw t.1 hj) (norm_nonneg _) A0
    _ = (#P : ℝ)*(A*B) := by simp
    _ ≤ ((r : ℝ)*T)*(A*B) := mul_le_mul_of_nonneg_right cardP (mul_nonneg A0 B0)
    _ = _ := by ring

end

end B13BoundedStepProductSavingProof

end

/- Expanded endpoint bucket -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

theorem expanded_hyperbola_endpoint_bucket_budget {n m g : ℕ}
    (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ)) :
    let cap := ⌊(m : ℝ)*(g : ℝ)*(n : ℝ)^(1/256 : ℝ)⌋₊
    let d := ⌊(m : ℝ)*(n : ℝ)^(-3/1024 : ℝ)⌋₊
    0 < d ∧ ((cap/d+1 : ℕ) : ℝ) ≤ 3*(g : ℝ)*(n : ℝ)^(7/1024 : ℝ) ∧
      (d : ℝ)/(m : ℝ) ≤ (n : ℝ)^(-3/1024 : ℝ) := by
  dsimp only
  let N := (n : ℝ)
  let P := (m : ℝ)
  let G := (g : ℝ)
  let cap := ⌊P*G*N^(1/256 : ℝ)⌋₊
  let d := ⌊P*N^(-3/1024 : ℝ)⌋₊
  have np : 0 < N := zero_lt_one.trans_le n1
  have pp : 0 < P := (Real.rpow_pos_of_pos np _).trans_le mLo
  have gp : 0 < G := zero_lt_one.trans_le g1
  have v1 : 1 ≤ P*N^(-3/1024 : ℝ) := calc
    1 ≤ N^(1/3-3/1024 : ℝ) := Real.one_le_rpow n1 (by norm_num)
    _ = N^(1/3 : ℝ)*N^(-3/1024 : ℝ) := by rw [sub_eq_add_neg,Real.rpow_add np]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right mLo (by positivity)
  have d1 : 1 ≤ d := Nat.le_floor v1
  have dp : (0 : ℝ) < d := by exact_mod_cast d1
  have low : P*N^(-3/1024 : ℝ) ≤ 2*(d : ℝ) := by
    have dR : (1 : ℝ) ≤ d := by exact_mod_cast d1
    have fl := Nat.lt_floor_add_one (P*N^(-3/1024 : ℝ))
    change P*N^(-3/1024 : ℝ) < (d : ℝ)+1 at fl
    linarith only [dR,fl]
  have upper : (d : ℝ) ≤ P*N^(-3/1024 : ℝ) := Nat.floor_le (by positivity)
  have capUp : (cap : ℝ) ≤ P*G*N^(1/256 : ℝ) := Nat.floor_le (by positivity)
  have divided : ((cap/d : ℕ) : ℝ) ≤ (cap : ℝ)/(d : ℝ) :=
    (le_div_iff₀ dp).mpr (by exact_mod_cast Nat.div_mul_le_self cap d)
  have est : (cap : ℝ) ≤ (2*G*N^(7/1024 : ℝ))*(d : ℝ) := calc
    _ ≤ P*G*N^(1/256 : ℝ) := capUp
    _ = (G*N^(7/1024 : ℝ))*(P*N^(-3/1024 : ℝ)) := by
      have r : N^(7/1024 : ℝ)*N^(-3/1024 : ℝ) = N^(1/256 : ℝ) := by rw [← Real.rpow_add np]; norm_num
      calc
        _ = P*G*(N^(7/1024 : ℝ)*N^(-3/1024 : ℝ)) := by rw [r]
        _ = _ := by ring
    _ ≤ (G*N^(7/1024 : ℝ))*(2*(d : ℝ)) := mul_le_mul_of_nonneg_left low (by positivity)
    _ = _ := by ring
  have q := divided.trans ((div_le_iff₀ dp).mpr est)
  have one : 1 ≤ G*N^(7/1024 : ℝ) := one_le_mul_of_one_le_of_one_le g1 (Real.one_le_rpow n1 (by norm_num))
  refine ⟨d1,?_,(div_le_iff₀ pp).mpr (by simpa only [mul_comm] using upper)⟩
  change ((cap/d+1 : ℕ) : ℝ) ≤ 3*G*N^(7/1024 : ℝ)
  push_cast
  linarith only [q,one]

end

end B13BoundedStepProductSavingProof

end

/- Expanded modulus ratio hyperbola -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

set_option maxHeartbeats 1500000 in
theorem norm_expanded_modulus_ratio_hyperbola_le {n m g A S num l r : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/128 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(1/2+x/2-7/256))
    (mMid : (m : ℝ) ≤ (n : ℝ)^(5/8-x/3)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ))
    (gCap : (g : ℝ) ≤ (n : ℝ)^(1/512 : ℝ))
    (xLo : 31/512 ≤ x) (xHi : x ≤ 1/4) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+3/512))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512-x))
    (rCap : (r : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512 : ℝ))
    (endCap : num/(l+1) ≤ ⌊(m : ℝ)*(g : ℝ)*(n : ℝ)^(1/256 : ℝ)⌋₊)
    (A0 : 0 < A) (Am : A < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ)
    (aw : ∀ a ∈ I, ‖α a‖ ≤ T) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T*L)
    (divisors : ∀ z ≤ 4*m^3, (z.divisors.card : ℝ) ≤ T)
    (dR : ∀ z ≤ r, (z.divisors.card : ℝ) ≤ T) :
    let J := intIntervalModUnits m 0 S
    let lo (a : ℕ) : ℤ := (l/a : ℕ)
    let hi (a : ℕ) : ℤ := (r/a : ℕ)
    ‖gatedBilinearSum I J α β lo hi
        (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
          (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      592*(n : ℝ)^(1023/1024 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)) := by
  dsimp only
  let P := (m : ℝ)
  let N := (n : ℝ)
  let G := (g : ℝ)
  let C := G^(1/2 : ℝ)
  let H := N^(1023/1024 : ℝ)
  let J := intIntervalModUnits m 0 S
  let lo (a : ℕ) : ℤ := (l/a : ℕ)
  let hi (a : ℕ) : ℤ := (r/a : ℕ)
  let R := 98*N^(1015/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ))
  let d := ⌊P*N^(-3/1024 : ℝ)⌋₊
  let cap := ⌊P*G*N^(1/256 : ℝ)⌋₊
  have m1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have pp : 0 < P := zero_lt_one.trans_le m1
  have np : 0 < N := zero_lt_one.trans_le n1
  have gp : 0 < G := zero_lt_one.trans_le g1
  have cp : 0 < C := by unfold C; positivity
  have t0 := zero_le_one.trans T1
  have l0 := zero_le_one.trans L1
  have log0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg m1
  have R0 : 0 ≤ R := by unfold R; positivity
  have bound : R ≤ 98*N^(1015/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ)) := le_rfl
  obtain ⟨d0,dcount,dsmall⟩ := expanded_hyperbola_endpoint_bucket_budget n1 g1 mLo
  have rUp : (r : ℝ) ≤ 2*N^(513/512 : ℝ)/(P*G^2) := (le_div_iff₀ (by positivity)).mpr (by
    have h := rCap
    change (r : ℝ)*P*G^2 ≤ 2*N^(513/512 : ℝ) at h
    convert h using 1
    ring)
  have jPos (j : ℤ) (hj : j ∈ J) : 0 < j := by
    have data : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    exact (mem_Ioc.mp data.1).1
  let mass := ∑ j ∈ J, ‖β j‖*∑ a ∈ I, if lo a < j ∧ j ≤ hi a then ‖α a‖ else 0
  have mass0 : 0 ≤ mass := by
    unfold mass
    exact sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (sum_nonneg fun a _ => by split_ifs <;> positivity)
  have massCut : mass ≤ (2*N^(513/512 : ℝ)/(P*G^2))*T^3*L := by
    have b := gated_left_weight_mass_le α β lo hi t0 (mul_nonneg t0 l0)
      (fun u hu => dR u (mem_Icc.mp hu).2) (fun a ha => (mem_Icc.mp (Icap ha)).1)
      (fun j hj => (jPos j hj).le) (fun a ha j hj active => ?_) aw bw
    · refine b.trans ?_
      calc
        _ ≤ (2*N^(513/512 : ℝ)/(P*G^2))*T*T*(T*L) := by gcongr
        _ = _ := by ring
    · have ja : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (jPos j hj).le
      have jR : j.toNat ≤ r/a := by
        have h : (j.toNat : ℤ) ≤ ((r/a : ℕ) : ℤ) := by rw [ja]; exact active.2
        exact_mod_cast h
      have ap := (mem_Icc.mp (Icap ha)).1
      have jn : 0 < j.toNat := by have := jPos j hj; omega
      exact mem_Icc.mpr ⟨mul_pos ap jn,by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ap).mp jR⟩
  have est : ‖gatedBilinearSum I J α β lo hi
      (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
        (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
          ((cap/d+1 : ℕ) : ℝ)*(2*R)+(2*((d : ℝ)/P))*mass := by
    let phase (a : ℕ) (j : ℤ) := c*((a : ZMod m)*(j : ZMod m))⁻¹
    let e (a : ℕ) (j : ℤ) := (num : ℤ)/((a*j.toNat : ℕ) : ℤ)
    rw [gated_bilinear_sum_eq_pair_sum]
    refine norm_product_interval_le_of_ratio_window (num := num) (p := m) I J α β _ (fun a ha => (mem_Icc.mp (Icap ha)).1)
      jPos d0 endCap ?_
    intro u v b t vb bt bracket
    rw [← gated_bilinear_sum_eq_pair_sum]
    refine norm_gated_residue_variable_endpoint_le m I J α β u v vb bt phase e
      (fun a ha j hj gate => (bracket a ha j hj gate).2) ?_ ?_
    · exact norm_gated_composite_expanded_product_fixed_endpoints_le charBound n1 g1 T1 L1 mHi mMid mLo xLo xHi
        logBound aCap cofactorCap A0 Am I Icap copI α β u v vb aw bw divisors
    · apply norm_gated_composite_expanded_product_fixed_endpoints_le charBound n1 g1 T1 L1 mHi mMid mLo xLo xHi
        logBound aCap cofactorCap A0 Am I Icap copI _ _ u v bt ?_ ?_ divisors
      · intro a ha
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (α a))] using aw a ha
      · intro j hj
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (β j))] using bw j hj
  have e1 : ((cap/d+1 : ℕ) : ℝ)*(2*R) ≤ 588*H*T^3*L^3/(P*G) := by
    have Ghalf : G^(3/2 : ℝ) = G*C := by
      unfold C
      rw [mul_comm G,← Real.rpow_add_one gp.ne']
      norm_num
    have CC : C^2 = G := by unfold C; rw [← Real.rpow_mul_natCast gp.le]; norm_num
    have cpow : C ≤ N^(1/1024 : ℝ) := by
      have b := Real.rpow_le_rpow gp.le gCap (by norm_num : (0 : ℝ) ≤ 1/2)
      rw [← Real.rpow_mul np.le] at b
      norm_num at b ⊢
      exact b
    calc
      _ ≤ (3*G*N^(7/1024 : ℝ))*(2*(98*N^(1015/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ)))) := by gcongr
      _ = 588*N^(511/512 : ℝ)*T^3*L^3*C/(P*G) := by
        have add : N^(7/1024 : ℝ)*N^(1015/1024 : ℝ) = N^(511/512 : ℝ) := by
          rw [← Real.rpow_add np]
          norm_num
        calc
          _ = 588*(N^(7/1024 : ℝ)*N^(1015/1024 : ℝ))*T^3*L^3*G/(P*G^(3/2 : ℝ)) := by ring
          _ = _ := by
            have frac : G/(P*(G*C)) = C/(P*G) := by
              rw [← CC]
              field_simp [pp.ne',cp.ne']
            rw [add,Ghalf]
            calc
              _ = (588*N^(511/512 : ℝ)*T^3*L^3)*(G/(P*(G*C))) := by ring
              _ = _ := by rw [frac]; ring
      _ ≤ 588*N^(511/512 : ℝ)*T^3*L^3*N^(1/1024 : ℝ)/(P*G) := by gcongr
      _ = _ := by
        have add : N^(511/512 : ℝ)*N^(1/1024 : ℝ) = H := by
          unfold H
          rw [← Real.rpow_add np]
          norm_num
        calc
          _ = 588*(N^(511/512 : ℝ)*N^(1/1024 : ℝ))*T^3*L^3/(P*G) := by ring
          _ = _ := by rw [add]
  have e2 : (2*((d : ℝ)/P))*mass ≤ 4*H*T^3*L^3/(P*G) := by
    have lg : L ≤ L^3 := by simpa only [pow_one] using pow_le_pow_right₀ L1 (show 1 ≤ 3 by decide)
    have pow : N^(-3/1024 : ℝ)*N^(513/512 : ℝ) = H := by unfold H; rw [← Real.rpow_add np]; norm_num
    calc
      _ ≤ (2*N^(-3/1024 : ℝ))*((2*N^(513/512 : ℝ)/(P*G^2))*T^3*L) := by gcongr
      _ = 4*H*T^3*L/(P*G^2) := by
        calc
          _ = 4*(N^(-3/1024 : ℝ)*N^(513/512 : ℝ))*T^3*L/(P*G^2) := by ring
          _ = _ := by rw [pow]
      _ ≤ 4*H*T^3*L^3/(P*G^2) := by gcongr
      _ ≤ _ := by
        have gPow : G ≤ G^2 := by simpa only [pow_one] using pow_le_pow_right₀ g1 (show 1 ≤ 2 by decide)
        gcongr
  exact est.trans ((add_le_add e1 e2).trans_eq (by ring))

end

end B13BoundedStepProductSavingProof

end

/- Wide noncommon rows -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Common wide mass -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Wide medium budget -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def wideMediumStepCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(7/12 : ℝ)⌋₊

end

end B13BoundedStepProductSavingProof

end

/- Average product overlap -/
section

namespace B13BoundedStepProductSavingProof

open MeasureTheory ContinuousLinearMap
open DyadicMixedB4Geometric DyadicMixedB4ProgressionApprox
open scoped FourierTransform Convolution Classical

noncomputable section

def currentBinEdge (u x : ℕ) : ℝ := (u : ℝ)*((x : ℝ)+1/2)

def progressionOverlap (u v l r p s : ℕ) (x : ℝ) : ℝ :=
  max 0 (min (currentBinEdge u r) (x-currentBinEdge v p) -
    max (currentBinEdge u l) (x-currentBinEdge v s))

end

end B13BoundedStepProductSavingProof

end

/- Full average overlap -/
section

namespace B13BoundedStepProductSavingProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcCenters
open scoped Classical

noncomputable section

def overlapMass (n u v l r p s : ℕ) : ℂ :=
  (progressionOverlap u v l r p s (n : ℝ) : ℂ)*((u : ℂ)⁻¹*(v : ℂ)⁻¹)

end

end B13BoundedStepProductSavingProof

end

/- Integer volume rounding -/
section

namespace B13BoundedStepProductSavingProof

noncomputable section

private theorem abs_max_difference_le {a b c d K : ℝ} (h1 : |a-c| ≤ K) (h2 : |b-d| ≤ K) :
    |max a b-max c d| ≤ K := by
  have upper : max a b ≤ max c d+K :=
    max_le (by linarith only [(abs_le.mp h1).2,le_max_left c d])
      (by linarith only [(abs_le.mp h2).2,le_max_right c d])
  have lower : max c d ≤ max a b+K :=
    max_le (by linarith only [(abs_le.mp h1).1,le_max_left a b])
      (by linarith only [(abs_le.mp h2).1,le_max_right a b])
  exact abs_le.mpr ⟨by linarith only [lower],by linarith only [upper]⟩

private theorem abs_min_difference_le {a b c d K : ℝ} (h1 : |a-c| ≤ K) (h2 : |b-d| ≤ K) :
    |min a b-min c d| ≤ K := by
  have upper : min a b ≤ min c d+K := by
    by_cases h : c ≤ d
    · rw [min_eq_left h]
      linarith only [(abs_le.mp h1).2,min_le_left a b]
    · rw [min_eq_right (le_of_not_ge h)]
      linarith only [(abs_le.mp h2).2,min_le_right a b]
  have lower : min c d ≤ min a b+K := by
    by_cases h : a ≤ b
    · rw [min_eq_left h]
      linarith only [(abs_le.mp h1).1,min_le_left c d]
    · rw [min_eq_right (le_of_not_ge h)]
      linarith only [(abs_le.mp h2).1,min_le_right c d]
  exact abs_le.mpr ⟨by linarith only [lower],by linarith only [upper]⟩

private theorem rounding_mul_bounds (u : ℕ) (hu : 0 < u) (a : ℤ) :
    (a : ℝ)-(u : ℝ) ≤ (u : ℝ)*((a/(u : ℤ) : ℤ) : ℝ) ∧
    (u : ℝ)*((a/(u : ℤ) : ℤ) : ℝ) ≤ (a : ℝ) := by
  have ur : (0 : ℤ) < u := by exact_mod_cast hu
  have low : (0 : ℝ) ≤ ((a % (u : ℤ) : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg a ur.ne'
  have high : (((a % (u : ℤ) : ℤ) : ℝ)) < (u : ℝ) := by exact_mod_cast Int.emod_lt_of_pos a ur
  have exactSum : (((a % (u : ℤ) : ℤ) : ℝ))+(u : ℝ)*((a/(u : ℤ) : ℤ) : ℝ) = (a : ℝ) := by
    exact_mod_cast Int.emod_add_mul_ediv a (u : ℤ)
  exact ⟨by linarith only [exactSum,high],by linarith only [exactSum,low]⟩

private theorem abs_scaled_endpoints_le {n u v l r p s : ℕ} (hu : 0 < u) :
    |max 0 ((u : ℝ)*(pairLeftUpper n u v r p : ℤ) - (u : ℝ)*(pairLeftLower n u v l s : ℤ)) -
      progressionOverlap u v l r p s (n : ℝ)| ≤ 6*((u : ℝ)+(v : ℝ)) := by
  let lower : ℤ := (n : ℤ)-(v : ℤ)*s-1
  let upper : ℤ := (n : ℤ)-(v : ℤ)*((p : ℤ)+1)
  let K := 3*((u : ℝ)+(v : ℝ))
  have u0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have u1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have v0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  have klo : 0 ≤ K := by unfold K; positivity
  have first (i : ℕ) : |(u : ℝ)*(i : ℝ)-currentBinEdge u i| ≤ K := by
    unfold currentBinEdge K
    apply abs_le.mpr
    constructor <;> nlinarith only [u0,v0]
  have low2 : |(u : ℝ)*((lower/(u : ℤ) : ℤ) : ℝ)-((n : ℝ)-currentBinEdge v s)| ≤ K := by
    obtain ⟨lo,hi⟩ := rounding_mul_bounds u hu lower
    have cast : (lower : ℝ) = (n : ℝ)-(v : ℝ)*s-1 := by
      unfold lower
      push_cast
      ring
    rw [cast] at lo hi
    unfold currentBinEdge K
    apply abs_le.mpr
    constructor <;> nlinarith only [lo,hi,u1,v0]
  have high2 : |(u : ℝ)*((upper/(u : ℤ) : ℤ) : ℝ)-((n : ℝ)-currentBinEdge v p)| ≤ K := by
    obtain ⟨lo,hi⟩ := rounding_mul_bounds u hu upper
    have cast : (upper : ℝ) = (n : ℝ)-(v : ℝ)*((p : ℝ)+1) := by
      unfold upper
      push_cast
      ring
    rw [cast] at lo hi
    unfold currentBinEdge K
    apply abs_le.mpr
    constructor <;> nlinarith only [lo,hi,u0,v0]
  have lowerEq : (u : ℝ)*(pairLeftLower n u v l s : ℤ) =
      max ((u : ℝ)*(l : ℝ)) ((u : ℝ)*((lower/(u : ℤ) : ℤ) : ℝ)) := by
    unfold pairLeftLower
    rw [Int.cast_max,Int.cast_natCast,mul_max_of_nonneg _ _ u0]
  have upperEq : (u : ℝ)*(pairLeftUpper n u v r p : ℤ) =
      min ((u : ℝ)*(r : ℝ)) ((u : ℝ)*((upper/(u : ℤ) : ℤ) : ℝ)) := by
    unfold pairLeftUpper
    rw [Int.cast_min,Int.cast_natCast,mul_min_of_nonneg _ _ u0]
  rw [lowerEq,upperEq]
  unfold progressionOverlap
  refine abs_max_difference_le (a := 0) (c := 0) (by
    rw [sub_self,abs_zero]
    positivity) ?_
  have e1 := abs_max_difference_le (first l) low2
  have e2 := abs_min_difference_le (first r) high2
  dsimp only [K] at e1 e2
  apply abs_le.mpr
  constructor <;> linarith only [(abs_le.mp e1).1,(abs_le.mp e1).2,(abs_le.mp e2).1,(abs_le.mp e2).2]

theorem norm_pair_volume_sub_singular_overlap_le {n u v l r p s : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hn : u.gcd v ∣ n) :
    ‖(pairVolume n u v l r p s : ℂ)-((u.gcd v : ℕ) : ℂ)*overlapMass n u v l r p s‖ ≤
      6*(u.gcd v : ℝ)*((u : ℝ)⁻¹+(v : ℝ)⁻¹) := by
  let d := u.gcd v
  let m := v/d
  let ratio := (d : ℝ)/((u : ℝ)*v)
  let a := pairLeftLower n u v l s
  let b := pairLeftUpper n u v r p
  have dPos : 0 < d := Nat.gcd_pos_of_pos_right _ hv
  have mPos : 0 < m := Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right ..)) dPos
  have ur : (0 : ℝ) < u := by exact_mod_cast hu
  have vr : (0 : ℝ) < v := by exact_mod_cast hv
  have mr : (0 : ℝ) < m := by unfold m; exact_mod_cast mPos
  have r0 : 0 ≤ ratio := by unfold ratio; positivity
  have align : (m : ℝ)*(d : ℝ) = v := by
    unfold m d
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right u v)
  have normalize : (m : ℝ)⁻¹ = ratio*(u : ℝ) := by
    unfold ratio
    field_simp
    linear_combination -align
  have vol : pairVolume n u v l r p s = ratio*max 0 ((u : ℝ)*(b : ℝ)-(u : ℝ)*(a : ℝ)) := by
    unfold pairVolume
    rw [ite_eq_left hn]
    change (((max 0 (b-a) : ℤ) : ℝ)/(m : ℝ)) = _
    rw [Int.cast_max,Int.cast_zero,Int.cast_sub,div_eq_mul_inv,normalize,← mul_sub]
    have scaled : (u : ℝ)*max 0 ((b : ℝ)-(a : ℝ)) =
        max 0 ((u : ℝ)*((b : ℝ)-(a : ℝ))) := by
      simpa only [mul_zero] using mul_max_of_nonneg (0 : ℝ) ((b : ℝ)-(a : ℝ)) ur.le
    rw [← scaled]
    ring
  have mass : (d : ℂ)*overlapMass n u v l r p s =
      ((ratio*progressionOverlap u v l r p s (n : ℝ) : ℝ) : ℂ) := by
    unfold overlapMass ratio
    push_cast
    ring
  change ‖(pairVolume n u v l r p s : ℂ)-(d : ℂ)*overlapMass n u v l r p s‖ ≤ _
  rw [vol,mass,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,← mul_sub,abs_mul,abs_of_nonneg r0]
  refine (mul_le_mul_of_nonneg_left (abs_scaled_endpoints_le (n := n) (u := u) (v := v) (l := l)
    (r := r) (p := p) (s := s) hu) r0).trans_eq ?_
  unfold ratio d
  field_simp
  ring

end

end B13BoundedStepProductSavingProof

end

/- Volume rounding family -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

def volumeRoundingFamily (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if gate i j ∧ (u i).gcd (v j) ∣ n then
    a i*b j*((pairVolume n (u i) (v j) (l i) (r i) (p j) (s j) : ℂ) -
      (((u i).gcd (v j) : ℕ) : ℂ)*overlapMass n (u i) (v j) (l i) (r i) (p j) (s j)) else 0

theorem norm_volume_rounding_family_le (n A : ℕ) (hn : 0 < n) (Apos : 0 < A)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    {W : ℝ} (W0 : 0 ≤ W) (uSteps : ∀ i ∈ I, u i ∈ Icc 1 A) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 A)
    (uWeights : ∀ x ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i=x), ‖a i‖) ≤ W)
    (vWeights : ∀ x ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j=x), ‖b j‖) ≤ W) :
    ‖volumeRoundingFamily n I J u l r v p s a b gate‖ ≤
      12*W^2*(A : ℝ)*(1+Real.log (A : ℝ))*(n.divisors.card : ℝ) := by
  let L := 1+Real.log (A : ℝ)
  let K := 12*W^2*(A : ℝ)*L
  let P (i : α) (j : β) := ‖a i‖*‖b j‖*((u i : ℝ)⁻¹+(v j : ℝ)⁻¹)
  let row (d : ℕ) (i : α) (j : β) : ℝ :=
    if d∣u i ∧ d∣v j then 6*(d : ℝ)*P i j else 0
  have Pnon (i : α) (j : β) : 0 ≤ P i j := by unfold P; positivity
  have log0 : 0 ≤ L := add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast Apos))
  have each (i : α) (hi : i ∈ I) (j : β) (hj : j ∈ J) :
      ‖if gate i j ∧ (u i).gcd (v j) ∣ n then
        a i*b j*((pairVolume n (u i) (v j) (l i) (r i) (p j) (s j) : ℂ) -
          (((u i).gcd (v j) : ℕ) : ℂ)*overlapMass n (u i) (v j) (l i) (r i) (p j) (s j)) else 0‖ ≤
      ∑ d ∈ n.divisors,row d i j := by
    by_cases ok : gate i j ∧ (u i).gcd (v j) ∣ n
    · let d := (u i).gcd (v j)
      have hd : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨ok.2,hn.ne'⟩
      have bound := norm_pair_volume_sub_singular_overlap_le (mem_Icc.mp (uSteps i hi)).1
        (mem_Icc.mp (vSteps j hj)).1 ok.2 (l := l i) (r := r i) (p := p j) (s := s j)
      rw [ite_eq_left ok,norm_mul,norm_mul]
      refine (mul_le_mul_of_nonneg_left bound (by positivity)).trans ?_
      have eq : row d i j = 6*(d : ℝ)*P i j := by
        unfold row
        rw [ite_eq_left ⟨Nat.gcd_dvd_left _ _,Nat.gcd_dvd_right _ _⟩]
      calc
        _ = row d i j := by rw [eq]; unfold P d; ring
        _ ≤ _ := single_le_sum (f := fun e : ℕ => row e i j)
          (fun _ _ => by unfold row; split_ifs <;> positivity) hd
    · rw [ite_eq_right ok,norm_zero]
      exact sum_nonneg fun q _ => by unfold row; split_ifs <;> positivity
  have one (d : ℕ) (hd : d ∈ n.divisors) : (∑ i ∈ I,∑ j ∈ J,row d i j) ≤ K := by
    let I' := I.filter (fun i => d∣u i)
    let J' := J.filter (fun j => d∣v j)
    let U0 := ∑ i ∈ I',‖a i‖
    let V0 := ∑ j ∈ J',‖b j‖
    let U1 := ∑ i ∈ I',‖a i‖*(u i : ℝ)⁻¹
    let V1 := ∑ j ∈ J',‖b j‖*(v j : ℝ)⁻¹
    have dp : 0 < d := Nat.pos_of_mem_divisors hd
    have d1 : (1 : ℝ) ≤ d := by exact_mod_cast dp
    have dpR := zero_lt_one.trans_le d1
    have capU0 : U0 ≤ W*((A : ℝ)/d) := by
      have est := divisible_constant_step_mass_le A d I u a W0 uSteps uWeights
      simpa only [divisibleStepMass,mul_one] using est
    have capV0 : V0 ≤ W*((A : ℝ)/d) := by
      have est := divisible_constant_step_mass_le A d J v b W0 vSteps vWeights
      simpa only [divisibleStepMass,mul_one] using est
    have capU1 : U1 ≤ W*((1/(d : ℝ))*L) := by
      have est := divisible_inverse_step_mass_le 1 A d dp I u a W0 uSteps uWeights
      simpa only [divisibleStepMass,Nat.cast_one,one_div] using est
    have capV1 : V1 ≤ W*((1/(d : ℝ))*L) := by
      have est := divisible_inverse_step_mass_le 1 A d dp J v b W0 vSteps vWeights
      simpa only [divisibleStepMass,Nat.cast_one,one_div] using est
    calc
      _ = ∑ i ∈ I',∑ j ∈ J',6*(d : ℝ)*P i j := by
        unfold I' J'
        simp only [sum_filter]
        refine sum_congr rfl fun i _ => ?_
        by_cases h : d∣u i <;> simp [h,row]
      _ = 6*(d : ℝ)*(U1*V0+U0*V1) := by
        unfold U1 U0 V1 V0
        rw [sum_mul_sum,sum_mul_sum,← sum_add_distrib,mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [← sum_add_distrib,mul_sum]
        exact sum_congr rfl fun j _ => by unfold P; ring
      _ ≤ 6*(d : ℝ)*(W*(1/(d : ℝ)*L)*(W*((A : ℝ)/d))+
                      W*((A : ℝ)/d)*(W*(1/(d : ℝ)*L))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · exact mul_le_mul capU1 capV0 (by unfold V0; positivity) (by positivity)
        · exact mul_le_mul capU0 capV1 (by unfold V1; positivity) (by positivity)
      _ = K/(d : ℝ) := by unfold K; field_simp; ring
      _ ≤ K := (div_le_iff₀ dpR).mpr (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left d1 (by unfold K; positivity))
  unfold volumeRoundingFamily
  refine (norm_sum_le _ _).trans ((sum_le_sum fun i _ => norm_sum_le _ _).trans ?_)
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ∑ d ∈ n.divisors,row d i j :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => each i hi j hj
    _ = ∑ d ∈ n.divisors,∑ i ∈ I,∑ j ∈ J,row d i j := by
      calc
        _ = ∑ i ∈ I,∑ d ∈ n.divisors,∑ j ∈ J,row d i j := sum_congr rfl fun i _ => sum_comm
        _ = _ := sum_comm
    _ ≤ ∑ _ ∈ n.divisors,K := sum_le_sum one
    _ = _ := by rw [sum_const,nsmul_eq_mul]; unfold K L; ring

end

end B13BoundedStepProductSavingProof

end

/- Subcritical medium residue -/
section

namespace B13BoundedStepProductSavingProof

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

private theorem harmonic_step_bound (A : ℕ) :
    (∑ u ∈ Icc 1 A, 1/(u : ℝ)) ≤ 1+Real.log A := by
  have eq : (range A).image Nat.succ = Icc 1 A := by
    ext i
    simp only [mem_image, mem_Icc, mem_range, Nat.succ_eq_add_one]
    constructor
    · rintro ⟨k,hk,rfl⟩
      omega
    · intro h
      exact ⟨i-1,by omega,by omega⟩
  rw [← eq, sum_image (fun _ _ _ _ h => Nat.succ.inj h)]
  have eqh : (harmonic A : ℝ) = ∑ i ∈ range A, 1/((i.succ : ℕ) : ℝ) := by
    unfold harmonic
    push_cast
    simp only [one_div]
  rw [← eqh]
  exact_mod_cast harmonic_le_one_add_log A

def smallProductResidueFamily (n P : ℕ) {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (u l r : ι → ℕ) (v p s : κ → ℕ) (a : ι → ℂ) (b : κ → ℂ) (gate : ι → κ → Prop) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if gate i j ∧ u i*v j ≤ P then
    a i*b j*(pairResidueError n (u i) (v j) (l i) (r i) (p j) (s j) : ℂ)
  else 0

theorem norm_small_product_residue_family_le (n P A : ℕ) {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (u l r : ι → ℕ) (v p s : κ → ℕ)
    (a : ι → ℂ) (b : κ → ℂ) (gate : ι → κ → Prop) {W : ℝ} (W0 : 0 ≤ W)
    (lu : ∀ i ∈ I, u i ∈ Icc 1 A) (rv : ∀ j ∈ J, v j ∈ Icc 1 A)
    (lm : ∀ m ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i = m), ‖a i‖) ≤ W)
    (rm : ∀ m ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j = m), ‖b j‖) ≤ W) :
    ‖smallProductResidueFamily n P I J u l r v p s a b gate‖ ≤
      W^2*(P : ℝ)*(1+Real.log A) := by
  have row (i : ι) (hi : i ∈ I) :
      ∑ j ∈ J, ‖if gate i j ∧ u i*v j ≤ P then
        a i*b j*(pairResidueError n (u i) (v j) (l i) (r i) (p j) (s j) : ℂ) else 0‖ ≤
      ‖a i‖*(W*(P : ℝ)*(1/(u i : ℝ))) := by
    let K := J.filter (fun j => u i*v j ≤ P)
    let B := min A (P/u i)
    have up : 0 < u i := (mem_Icc.mp (lu i hi)).1
    have ur : (0 : ℝ) < u i := by exact_mod_cast up
    have Bsteps (j : κ) (hj : j ∈ K) : v j ∈ Icc 1 B := by
      have rj := mem_Icc.mp (rv j (mem_filter.mp hj).1)
      exact mem_Icc.mpr ⟨rj.1,le_min rj.2
        ((Nat.le_div_iff_mul_le up).mpr (by simpa only [Nat.mul_comm] using (mem_filter.mp hj).2))⟩
    have Bmass (m : ℕ) (hm : m ∈ Icc 1 B) : (∑ j ∈ K.filter (fun j => v j = m), ‖b j‖) ≤ W := by
      have hmA : m ∈ Icc 1 A := mem_Icc.mpr
        ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans (min_le_left _ _)⟩
      exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
        (fun _ _ _ => norm_nonneg _)).trans (rm m hmA)
    have sumb : (∑ j ∈ K, ‖b j‖) ≤ W*(B : ℝ) := by
      simpa [Nat.card_Icc] using sum_weighted_steps_le K v b (fun _ => 1) Bsteps
        (fun _ _ => zero_le_one) Bmass
    have Br : (B : ℝ) ≤ (P : ℝ)/(u i : ℝ) := by
      have ndiv : (B : ℝ) ≤ (P/u i : ℕ) := by exact_mod_cast min_le_right A (P/u i)
      exact ndiv.trans ((le_div_iff₀ ur).mpr (by exact_mod_cast Nat.div_mul_le_self P (u i)))
    calc
      _ ≤ ∑ j ∈ J, if u i*v j ≤ P then ‖a i‖*‖b j‖ else 0 := by
        refine sum_le_sum fun j hj => ?_
        by_cases prod : u i*v j ≤ P <;> by_cases g : gate i j <;>
          simp only [prod, g, and_true, and_false, ite_true, ite_false, norm_zero, le_refl]
        · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact (mul_le_mul_of_nonneg_left
            (abs_pair_residue_error_lt_one n (u i) (v j) (l i) (r i) (p j) (s j) (mem_Icc.mp (rv j hj)).1).le
            (by positivity)).trans_eq (mul_one _)
        · positivity
      _ = ‖a i‖*(∑ j ∈ K, ‖b j‖) := by
        unfold K
        rw [mul_sum, sum_filter]
      _ ≤ ‖a i‖*(W*((P : ℝ)/(u i : ℝ))) :=
        mul_le_mul_of_nonneg_left (sumb.trans (mul_le_mul_of_nonneg_left Br W0)) (norm_nonneg _)
      _ = _ := by ring
  unfold smallProductResidueFamily
  refine (norm_sum_le _ _).trans ((sum_le_sum fun i hi => (norm_sum_le _ _).trans (row i hi)).trans ?_)
  let z (m : ℕ) := 1/(m : ℝ)
  have est := sum_weighted_steps_le I u a z lu (fun _ _ => by unfold z; positivity) lm
  have regroup :
      (∑ i ∈ I, ‖a i‖*(W*(P : ℝ)*(1/(u i : ℝ)))) =
        (W*(P : ℝ))*(∑ i ∈ I, ‖a i‖*z (u i)) := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    unfold z
    ring
  rw [regroup]
  calc
    _ ≤ (W*(P : ℝ))*(W*(∑ m ∈ Icc 1 A, z m)) :=
      mul_le_mul_of_nonneg_left est (by positivity)
    _ = W^2*(P : ℝ)*(∑ m ∈ Icc 1 A, z m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_step_bound A) (by positivity)

def subcriticalMediumProductCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(255/256 : ℝ)⌋₊

end

end B13BoundedStepProductSavingProof

end

/- Medium exact partition -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale
open scoped Classical

noncomputable section

def prefixStepGate (n u v : ℕ) : Prop :=
  maximumStep n^2 < u*v ∧ u.gcd v ≤ maximumStep n

instance (n u v : ℕ) : Decidable (prefixStepGate n u v) :=
  inferInstanceAs (Decidable (maximumStep n^2 < u*v ∧ u.gcd v ≤ maximumStep n))

end

end B13BoundedStepProductSavingProof

end

/- Medium large gcd residue -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

theorem divided_step_range_of_dvd {ι : Type*} {I : Finset ι} (u : ι → ℕ)
    {A d : ℕ} (d0 : 0 < d) (range : ∀ i ∈ I, u i ∈ Icc 1 A) :
    ∀ i ∈ I.filter (fun i => d ∣ u i), u i/d ∈ Icc 1 (A/d) := by
  intro i hi
  obtain ⟨base,hdi⟩ := mem_filter.mp hi
  obtain ⟨one,top⟩ := mem_Icc.mp (range i base)
  have du : d ≤ u i := Nat.le_of_dvd one hdi
  exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le d0).mpr (by simpa only [one_mul] using du),
    Nat.div_le_div_right top⟩

theorem norm_divided_step_mass_le {ι : Type*} (I : Finset ι) (u : ι → ℕ)
    (w : ι → ℂ) {A d : ℕ} (d0 : 0 < d) {W : ℝ}
    (mass : ∀ m ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i = m), ‖w i‖) ≤ W) :
    ∀ m ∈ Icc 1 (A/d), (∑ i ∈ (I.filter (fun i => d ∣ u i)).filter (fun i => u i/d = m), ‖w i‖) ≤ W := by
  intro m hm
  have md : m*d ∈ Icc 1 A :=
    mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hm).1 d0, (Nat.le_div_iff_mul_le d0).mp (mem_Icc.mp hm).2⟩
  have subset : (I.filter fun i => d ∣ u i).filter (fun i => u i/d = m) ⊆ I.filter (fun i => u i = m*d) := by
    intro i hi
    obtain ⟨hs,he⟩ := mem_filter.mp hi
    obtain ⟨base,dvd⟩ := mem_filter.mp hs
    exact mem_filter.mpr ⟨base,(Nat.div_mul_cancel dvd).symm.trans (congrArg (·*d) he)⟩
  exact (sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => norm_nonneg _)).trans (mass _ md)

end

end B13BoundedStepProductSavingProof

end

/- Medium proper prime power -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Prime hyperbola saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4PairIntegral DyadicMixedB4TailScale
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def primeHyperbolaFactorFloor (n k : ℕ) : ℕ := ⌊(n : ℝ)^((k : ℝ)/256)⌋₊

def primeHyperbolaFactorLo (n k : ℕ) : ℕ := max (cutoffU n) (primeHyperbolaFactorFloor n k)

def primeHyperbolaFactorBlock (n k : ℕ) : Finset ℕ :=
  Ioc (primeHyperbolaFactorLo n k) (min (lowCut n) (primeHyperbolaFactorFloor n (k+1)))

theorem prime_hyperbola_endpoint_cap_of_size {n p l num : ℕ} (n0 : 0 < n) (p0 : 0 < p)
    (cut : subcriticalMediumProductCap n/p ≤ l) (nBound : num ≤ n) :
    num/(l+1) ≤ ⌊(p : ℝ)*(n : ℝ)^(1/256 : ℝ)⌋₊ := by
  let N := (n : ℝ)
  let P := (p : ℝ)
  let H := N^(1/256 : ℝ)
  have np : 0 < N := show (0 : ℝ) < (n : ℝ) from by exact_mod_cast n0
  have lp : (0 : ℝ) < (l : ℝ)+1 := by positivity
  have large : subcriticalMediumProductCap n < (l+1)*p :=
    (Nat.div_lt_iff_lt_mul p0).mp (Nat.lt_succ_of_le cut)
  have scaled : N^(255/256 : ℝ) ≤ ((l : ℝ)+1)*P := by
    have fl := Nat.lt_floor_add_one (N^(255/256 : ℝ))
    have room : (subcriticalMediumProductCap n : ℝ)+1 ≤ ((l : ℝ)+1)*P := by
      unfold P
      exact_mod_cast Nat.succ_le_of_lt large
    exact fl.le.trans room
  have final : N ≤ ((l : ℝ)+1)*(P*H) := calc
    _ = N^(255/256 : ℝ)*H := by unfold H; rw [← Real.rpow_add np]; norm_num
    _ ≤ (((l : ℝ)+1)*P)*H := mul_le_mul_of_nonneg_right scaled (by positivity)
    _ = _ := by ring
  apply Nat.le_floor
  calc
    _ ≤ N/((l : ℝ)+1) := (le_div_iff₀ lp).mpr (by
      have nat := (Nat.div_mul_le_self num (l+1)).trans nBound
      change ((num/(l+1) : ℕ) : ℝ)*((l : ℝ)+1) ≤ (n : ℝ)
      exact_mod_cast nat)
    _ ≤ P*H := (div_le_iff₀ lp).mpr (by simpa only [mul_comm] using final)

end

end B13BoundedStepProductSavingProof

end

/- Prime hyperbola bridge -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Prime hyperbola short left -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail
open scoped Classical Finset

noncomputable section

def primeHyperbolaShortLeftLo (n p : ℕ) : ℕ :=
  max (leftMediumCap n) (max (maximumStep n^2/p) (subcriticalMediumProductCap n/p))

end

end B13BoundedStepProductSavingProof

end

/- Gcd scaled residue -/
section

namespace B13BoundedStepProductSavingProof

noncomputable section

private theorem int_ediv_scaled_offset (d u x t : ℤ) (d0 : 0 < d) (u0 : 0 < u)
    (t0 : 0 ≤ t) (tSmall : t < d) : (d*x+t)/(d*u) = x/u := by
  let q := x/u
  have du : 0 < d*u := mul_pos d0 u0
  have lo : q*u ≤ x := (Int.le_ediv_iff_mul_le u0).mp le_rfl
  have hi : x < (q+1)*u := (Int.ediv_lt_iff_lt_mul u0).mp (by omega)
  have start : q*(d*u) ≤ d*x+t := calc
    _ = d*(q*u) := by ring
    _ ≤ d*x := mul_le_mul_of_nonneg_left lo d0.le
    _ ≤ _ := le_add_of_nonneg_right t0
  have endpt : d*x+t < (q+1)*(d*u) := calc
    _ < d*x+d := add_lt_add_right tSmall _
    _ = d*(x+1) := by ring
    _ ≤ d*((q+1)*u) := mul_le_mul_of_nonneg_left (Int.add_one_le_iff.mpr hi) d0.le
    _ = _ := by ring
  exact le_antisymm (Int.lt_add_one_iff.mp ((Int.ediv_lt_iff_lt_mul du).mpr endpt))
    ((Int.le_ediv_iff_mul_le du).mpr start)

theorem pair_left_lower_scale {d n u v l s : ℕ} (d0 : 0 < d) (u0 : 0 < u) :
    pairLeftLower (d*n) (d*u) (d*v) l s = pairLeftLower n u v l s := by
  have dp : (0 : ℤ) < d := by exact_mod_cast d0
  have up : (0 : ℤ) < u := by exact_mod_cast u0
  unfold pairLeftLower
  push_cast
  congr 1
  let x := (n : ℤ)-(v : ℤ)*s-1
  have eq : (d : ℤ)*(n : ℤ)-(d : ℤ)*(v : ℤ)*s-1 = (d : ℤ)*x+((d : ℤ)-1) := by unfold x; ring
  rw [eq]
  exact int_ediv_scaled_offset d u x ((d : ℤ)-1) dp up (by omega) (by omega)

theorem pair_left_upper_scale {d n u v r p : ℕ} (d0 : 0 < d) (u0 : 0 < u) :
    pairLeftUpper (d*n) (d*u) (d*v) r p = pairLeftUpper n u v r p := by
  have dp : (0 : ℤ) < d := by exact_mod_cast d0
  have up : (0 : ℤ) < u := by exact_mod_cast u0
  unfold pairLeftUpper
  push_cast
  congr 1
  let x := (n : ℤ)-(v : ℤ)*((p : ℤ)+1)
  have eq : (d : ℤ)*(n : ℤ)-(d : ℤ)*(v : ℤ)*((p : ℤ)+1) = (d : ℤ)*x+0 := by unfold x; ring
  rw [eq]
  exact int_ediv_scaled_offset d u x 0 dp up le_rfl dp

theorem pair_residue_error_eq_div_gcd {n u v l r p s : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hn : u.gcd v ∣ n) :
    let d := u.gcd v
    pairResidueError n u v l r p s = pairResidueError (n/d) (u/d) (v/d) l r p s := by
  dsimp only
  let d := u.gcd v
  let N := n/d
  let U := u/d
  let V := v/d
  have dp : 0 < d := Nat.gcd_pos_of_pos_right u hv
  have U0 : 0 < U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) dp
  have nEq : d*N = n := Nat.mul_div_cancel' hn
  have uEq : d*U = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have vEq : d*V = v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have g1 : U.gcd V = 1 := (Nat.coprime_div_gcd_div_gcd dp).gcd_eq_one
  have lo : pairLeftLower n u v l s = pairLeftLower N U V l s := by
    calc
      _ = pairLeftLower (d*N) (d*U) (d*V) l s := by rw [nEq,uEq,vEq]
      _ = _ := pair_left_lower_scale dp U0
  have hi : pairLeftUpper n u v r p = pairLeftUpper N U V r p := by
    calc
      _ = pairLeftUpper (d*N) (d*U) (d*V) r p := by rw [nEq,uEq,vEq]
      _ = _ := pair_left_upper_scale dp U0
  have rho : pairResidue n u v = pairResidue N U V := by
    unfold pairResidue
    change (N : ℤ)*Nat.gcdA U V % (V : ℤ) =
      ((N/(U.gcd V) : ℕ) : ℤ)*Nat.gcdA (U/(U.gcd V)) (V/(U.gcd V)) % ((V/(U.gcd V) : ℕ) : ℤ)
    rw [g1]
    simp only [Nat.div_one]
  change pairResidueError n u v l r p s = pairResidueError N U V l r p s
  unfold pairResidueError
  rw [ite_eq_left hn,ite_eq_left (show U.gcd V ∣ N by rw [g1]; exact one_dvd _),lo,hi,rho,g1,Nat.div_one]

end

end B13BoundedStepProductSavingProof

end

/- Near product common divisor -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def nearProductCommonDivisorCut (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/512 : ℝ)⌋₊

end

end B13BoundedStepProductSavingProof

end

/- Gcd product factor split -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Extended wide approx -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def extendedWideStepCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(21/32 : ℝ)⌋₊

theorem extended_wide_step_pos {n : ℕ} (hn : 0 < n) : 0 < extendedWideStepCap n :=
  Nat.le_floor (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))

theorem extended_wide_step_le {n : ℕ} (hn : 0 < n) : extendedWideStepCap n ≤ n :=
  Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num))

end

end B13BoundedStepProductSavingProof

end

/- Residue absolute triple mass -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

def prefixSolutionCount (n u v : ℕ) : ℝ :=
  (progressionPairSolutions n u v 0 (n/u) 0 (n/v)).card

theorem progression_pair_solutions_card_le_divisor_fibres {n u v l r b s : ℕ}
    (u0 : 0 < u) (v0 : 0 < v) :
    (progressionPairSolutions n u v l r b s).card ≤
      ((Icc 1 (n-1)).filter (fun t => u ∣ t ∧ v ∣ n-t)).card := by
  refine card_le_card_of_injOn (fun z : ℕ × ℕ => u*z.1) ?_ ?_
  · intro z hz
    obtain ⟨ranges,eq⟩ := mem_filter.mp hz
    change u*z.1+v*z.2=n at eq
    change u*z.1 ∈ (Icc 1 (n-1)).filter (fun t => u ∣ t ∧ v ∣ n-t)
    obtain ⟨xr,yr⟩ := mem_product.mp ranges
    have x0 : 0 < z.1 := (Nat.zero_le _).trans_lt (mem_Ioc.mp xr).1
    have y0 : 0 < z.2 := (Nat.zero_le _).trans_lt (mem_Ioc.mp yr).1
    have a0 := mul_pos u0 x0
    have c0 := mul_pos v0 y0
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨a0,by omega⟩,dvd_mul_right _ _,⟨z.2,by omega⟩⟩
  · intro x hx y hy ex
    have p : x.1 = y.1 := Nat.eq_of_mul_eq_mul_left u0 ex
    have q : v*x.2 = v*y.2 := by
      have left := (mem_filter.mp hx).2
      have right := (mem_filter.mp hy).2
      change u*x.1+v*x.2=n at left
      change u*y.1+v*y.2=n at right
      rw [p] at left
      omega
    exact Prod.ext p (Nat.eq_of_mul_eq_mul_left v0 q)

theorem sum_prefix_solution_count_le {n A : ℕ} {T : ℝ}
    (T0 : 0 ≤ T) (divCount : ∀ t ≤ n, (t.divisors.card : ℝ) ≤ T) :
    (∑ u ∈ Icc 1 A, ∑ v ∈ Icc 1 A, prefixSolutionCount n u v) ≤ (n : ℝ)*T^2 := by
  let K := Icc 1 (n-1)
  let U := Icc 1 A
  let D (t : ℕ) := U.filter (fun u => u ∣ t)
  have divCard {t : ℕ} (t0 : 0 < t) (tn : t ≤ n) : ((D t).card : ℝ) ≤ T := by
    have b : (D t).card ≤ t.divisors.card := card_le_card (fun u hu =>
      Nat.mem_divisors.mpr ⟨(mem_filter.mp hu).2,t0.ne'⟩)
    exact (show ((D t).card : ℝ) ≤ (t.divisors.card : ℝ) by exact_mod_cast b).trans (divCount t tn)
  have cardId (u v : ℕ) :
      (((K.filter (fun t => u ∣ t ∧ v ∣ n-t)).card : ℕ) : ℝ) =
        ∑ t ∈ K, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0 := by
    rw [← sum_filter]
    simp
  have fibres (t : ℕ) :
      (∑ u ∈ U, ∑ v ∈ U, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0) =
        ((D t).card : ℝ)*((D (n-t)).card : ℝ) := by
    have count (z : ℕ) : ((D z).card : ℝ) = ∑ u ∈ U, if u ∣ z then (1 : ℝ) else 0 := by
      rw [← sum_filter]
      simp [D]
    rw [count t,count (n-t),sum_mul_sum]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    by_cases h : u ∣ t <;> by_cases k : v ∣ n-t <;> simp [h,k]
  change (∑ u ∈ U, ∑ v ∈ U, prefixSolutionCount n u v) ≤ (n : ℝ)*T^2
  calc
    _ ≤ ∑ u ∈ U, ∑ v ∈ U, ∑ t ∈ K, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0 := by
      refine sum_le_sum fun u hu => sum_le_sum fun v hv => ?_
      rw [← cardId]
      unfold prefixSolutionCount
      exact_mod_cast progression_pair_solutions_card_le_divisor_fibres
        (mem_Icc.mp hu).1 (mem_Icc.mp hv).1
    _ = ∑ t ∈ K, ∑ u ∈ U, ∑ v ∈ U, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0 := by
      calc
        _ = ∑ u ∈ U, ∑ t ∈ K, ∑ v ∈ U, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0 :=
          sum_congr rfl fun _ _ => sum_comm
        _ = _ := sum_comm
    _ = ∑ t ∈ K, ((D t).card : ℝ)*((D (n-t)).card : ℝ) := sum_congr rfl fun t _ => fibres t
    _ ≤ ∑ _ ∈ K, T^2 := by
      refine sum_le_sum fun t ht => ?_
      obtain ⟨t1,tb⟩ := mem_Icc.mp ht
      rw [pow_two]
      exact mul_le_mul (divCard t1 (by omega)) (divCard (by omega) (Nat.sub_le _ _)) (by positivity) T0
    _ = (#K : ℝ)*T^2 := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have h : #K ≤ n := by unfold K; rw [Nat.card_Icc]; omega
      exact_mod_cast h

theorem pair_volume_le_of_coprime {n u v l r b s : ℕ}
    (u0 : 0 < u) (v0 : 0 < v) (cop : u.Coprime v) (ru : r*u ≤ n) :
    0 ≤ pairVolume n u v l r b s ∧ pairVolume n u v l r b s ≤ (n : ℝ)/((u : ℝ)*(v : ℝ)) := by
  have ue : (0 : ℝ) < u := by exact_mod_cast u0
  have ve : (0 : ℝ) < v := by exact_mod_cast v0
  have cl : (0 : ℤ) ≤ pairLeftLower n u v l s := (Int.natCast_nonneg _).trans (le_max_left _ _)
  have cu : pairLeftUpper n u v r b ≤ (r : ℤ) := min_le_left _ _
  have len : max 0 (pairLeftUpper n u v r b-pairLeftLower n u v l s) ≤ (r : ℤ) :=
    max_le (Int.natCast_nonneg _) ((sub_le_self _ cl).trans cu)
  have L0 : (0 : ℝ) ≤ ((max 0 (pairLeftUpper n u v r b-pairLeftLower n u v l s) : ℤ) : ℝ) := by
    exact_mod_cast (le_max_left 0 (pairLeftUpper n u v r b-pairLeftLower n u v l s))
  have Lr : (((max 0 (pairLeftUpper n u v r b-pairLeftLower n u v l s) : ℤ)) : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast len
  unfold pairVolume
  simp only [cop.gcd_eq_one,one_dvd,ite_true,Nat.div_one]
  refine ⟨div_nonneg L0 ve.le,?_⟩
  calc
    _ ≤ (r : ℝ)/(v : ℝ) := div_le_div_of_nonneg_right Lr ve.le
    _ ≤ ((n : ℝ)/(u : ℝ))/(v : ℝ) := div_le_div_of_nonneg_right
      ((le_div_iff₀ ue).mpr (by exact_mod_cast ru)) ve.le
    _ = _ := by field_simp

theorem norm_pair_residue_le_of_coprime {n u v l r b s : ℕ}
    (u0 : 0 < u) (v0 : 0 < v) (cop : u.Coprime v) :
    ‖(pairResidueError n u v l r b s : ℂ)‖ ≤ prefixSolutionCount n u v+(n : ℝ)/((u : ℝ)*(v : ℝ)) := by
  have hold : ∀ r' ≤ n/u, ‖(pairResidueError n u v l r' b s : ℂ)‖ ≤
      prefixSolutionCount n u v+(n : ℝ)/((u : ℝ)*(v : ℝ)) := by
    intro r' hr
    have vol := pair_volume_le_of_coprime (l := l) (r := r') (b := b) (s := s) u0 v0 cop
      ((Nat.le_div_iff_mul_le u0).mp hr)
    have count : (progressionPairSolutions n u v l r' b s).card ≤
        (progressionPairSolutions n u v 0 (n/u) 0 (n/v)).card := by
      apply card_le_card
      intro z hz
      obtain ⟨base,eq⟩ := mem_filter.mp hz
      obtain ⟨rx,ry⟩ := mem_product.mp base
      have yr : z.2 ≤ n/v := (Nat.le_div_iff_mul_le v0).mpr (by rw [Nat.mul_comm]; omega)
      exact mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp rx).1,(mem_Ioc.mp rx).2.trans hr⟩,
          mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp ry).1,yr⟩⟩,eq⟩
    rw [Complex.norm_real,Real.norm_eq_abs]
    have f : pairResidueError n u v l r' b s =
        ((progressionPairSolutions n u v l r' b s).card : ℝ)-pairVolume n u v l r' b s := by
      rw [progression_pair_count_eq_volume_add_error u0 v0]; ring
    rw [f]
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg vol.1]
      exact add_le_add (by unfold prefixSolutionCount; exact_mod_cast count) vol.2)
  have lim : ((n : ℤ)-(v : ℤ)*((b : ℤ)+1))/(u : ℤ) ≤ ((n/u : ℕ) : ℤ) := by
    rw [Int.natCast_ediv]
    exact Int.ediv_le_ediv (by positivity) (sub_le_self _ (by positivity))
  have pu : pairLeftUpper n u v r b = pairLeftUpper n u v (min r (n/u)) b := by
    unfold pairLeftUpper
    push_cast
    omega
  have eq : pairResidueError n u v l r b s = pairResidueError n u v l (min r (n/u)) b s := by
    unfold pairResidueError
    rw [pu]
  rw [eq]
  exact hold _ (min_le_right _ _)

end

end B13BoundedStepProductSavingProof

end

/- Scaled large gcd mass -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

theorem sum_product_norm_le_of_step_mass {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (u : ι → ℕ) (v : κ → ℕ) (α : ι → ℂ) (β : κ → ℂ) (P : ℕ → ℕ → ℝ)
    {A : ℕ} {W : ℝ} (W0 : 0 ≤ W)
    (lu : ∀ i ∈ I, u i ∈ Icc 1 A) (rv : ∀ j ∈ J, v j ∈ Icc 1 A)
    (lm : ∀ m ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i = m), ‖α i‖) ≤ W)
    (rm : ∀ m ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j = m), ‖β j‖) ≤ W)
    (P0 : ∀ x ∈ Icc 1 A, ∀ y ∈ Icc 1 A, 0 ≤ P x y) :
    (∑ i ∈ I, ∑ j ∈ J, ‖α i‖*‖β j‖*P (u i) (v j)) ≤
      W^2*(∑ x ∈ Icc 1 A, ∑ y ∈ Icc 1 A, P x y) := by
  let F (x : ℕ) := ∑ y ∈ Icc 1 A, P x y
  have F0 (x : ℕ) (hx : x ∈ Icc 1 A) : 0 ≤ F x := sum_nonneg fun y hy => P0 x hx y hy
  calc
    _ = ∑ i ∈ I, ‖α i‖*(∑ j ∈ J, ‖β j‖*P (u i) (v j)) := by
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i ∈ I, ‖α i‖*(W*F (u i)) := by
      refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact sum_norm_mul_le_of_step_mass J v β (P (u i)) rv (P0 (u i) (lu i hi)) rm
    _ = W*(∑ i ∈ I, ‖α i‖*F (u i)) := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring
    _ ≤ W*(W*(∑ x ∈ Icc 1 A, F x)) :=
      mul_le_mul_of_nonneg_left (sum_norm_mul_le_of_step_mass I u α F lu F0 lm) W0
    _ = _ := by unfold F; ring

def prefixResidueMass (n u v : ℕ) : ℝ :=
  prefixSolutionCount n u v+(n : ℝ)/((u : ℝ)*(v : ℝ))

theorem prefix_residue_mass_nonneg (n u v : ℕ) : 0 ≤ prefixResidueMass n u v := by
  unfold prefixResidueMass prefixSolutionCount
  positivity

theorem sum_prefix_residue_mass_le {n A : ℕ} {T : ℝ} (An : A ≤ n)
    (T0 : 0 ≤ T) (divCount : ∀ t ≤ n, (t.divisors.card : ℝ) ≤ T) :
    (∑ u ∈ Icc 1 A, ∑ v ∈ Icc 1 A, prefixResidueMass n u v) ≤ (n : ℝ)*(T^2+(1+Real.log n)^2) := by
  have log0 : 0 ≤ Real.log n := by
    rcases eq_or_ne n 0 with eq | hn
    · simp [eq]
    · exact Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hn)
  have H0 : (0 : ℝ) ≤ ∑ u ∈ Icc 1 A, 1/(u : ℝ) := sum_nonneg fun _ _ => by positivity
  have H : (∑ u ∈ Icc 1 A, 1/(u : ℝ)) ≤ 1+Real.log n := by
    rcases eq_or_ne A 0 with rfl | a0
    · simpa using zero_le_one.trans (le_add_of_nonneg_right log0)
    have ap : (0 : ℝ) < A := by exact_mod_cast Nat.pos_of_ne_zero a0
    calc
      _ = (harmonic A : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        simp [one_div]
      _ ≤ 1+Real.log A := by exact_mod_cast harmonic_le_one_add_log A
      _ ≤ _ := add_le_add_right (Real.log_le_log ap (show (A : ℝ) ≤ (n : ℝ) by exact_mod_cast An)) _
  have hp : (∑ u ∈ Icc 1 A, ∑ v ∈ Icc 1 A, (n : ℝ)/((u : ℝ)*(v : ℝ))) =
      (n : ℝ)*(∑ u ∈ Icc 1 A, 1/(u : ℝ))^2 := by
    rw [pow_two,sum_mul_sum,mul_sum]
    refine sum_congr rfl fun u hu => ?_
    rw [mul_sum]
    refine sum_congr rfl fun v hv => ?_
    have u0 : (0 : ℝ) < u := by exact_mod_cast (mem_Icc.mp hu).1
    have v0 : (0 : ℝ) < v := by exact_mod_cast (mem_Icc.mp hv).1
    field_simp
  unfold prefixResidueMass
  simp_rw [sum_add_distrib]
  rw [hp]
  have h := sum_prefix_solution_count_le (A := A) T0 divCount
  exact (add_le_add h (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ H0 H 2) (by positivity))).trans_eq
    (by rw [mul_add])

def gcdResidueFamily (n D : ℕ) {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (u l r : ι → ℕ) (v b s : κ → ℕ) (α : ι → ℂ) (β : κ → ℂ) (gate : ι → κ → Prop) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, @ite ℂ (gate i j ∧ D < (u i).gcd (v j)) (Classical.propDecidable _)
    (α i*β j*(pairResidueError n (u i) (v j) (l i) (r i) (b j) (s j) : ℂ)) 0

theorem norm_gcd_residue_family_le {n D A : ℕ} (n0 : 0 < n) (An : A ≤ n)
    {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (u l r : ι → ℕ) (v b s : κ → ℕ) (α : ι → ℂ) (β : κ → ℂ) (gate : ι → κ → Prop)
    {W T : ℝ} (W0 : 0 ≤ W) (T0 : 0 ≤ T) (divCount : ∀ t ≤ n, (t.divisors.card : ℝ) ≤ T)
    (lu : ∀ i ∈ I, u i ∈ Icc 1 A) (rv : ∀ j ∈ J, v j ∈ Icc 1 A)
    (lm : ∀ m ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i = m), ‖α i‖) ≤ W)
    (rm : ∀ m ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j = m), ‖β j‖) ≤ W) :
    ‖gcdResidueFamily n D I J u l r v b s α β gate‖ ≤
      T*(W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(1+Real.log n)^2)) := by
  let G := n.divisors.filter (D < ·)
  let g (i : ι) (j : κ) := (u i).gcd (v j)
  let w (i : ι) (j : κ) := α i*β j*(pairResidueError n (u i) (v j) (l i) (r i) (b j) (s j) : ℂ)
  let part (d : ℕ) := ∑ i ∈ I, ∑ j ∈ J, if gate i j ∧ g i j=d then w i j else 0
  have split : gcdResidueFamily n D I J u l r v b s α β gate = ∑ d ∈ G, part d := by
    unfold part
    rw [sum_comm (s := G) (t := I)]
    unfold gcdResidueFamily
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm (s := G) (t := J)]
    refine sum_congr rfl fun j _ => ?_
    have eq (d : ℕ) : (if gate i j ∧ g i j=d then w i j else 0) =
        if g i j=d then (if gate i j then w i j else 0) else 0 := by
      by_cases hg : g i j=d <;> by_cases hG : gate i j <;> simp [hg,hG]
    simp_rw [eq]
    rw [sum_ite_eq]
    by_cases compat : g i j ∣ n
    · have mem : g i j ∈ G ↔ D < g i j := by
        exact ⟨fun h => (mem_filter.mp h).2, fun h =>
          mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨compat,n0.ne'⟩,h⟩⟩
      change (@ite ℂ (gate i j ∧ D < g i j) (Classical.propDecidable _) (w i j) 0) =
        (if g i j ∈ G then if gate i j then w i j else 0 else 0)
      by_cases h : D < g i j
      · simp [h,mem.mpr h]
      · have hmiss : g i j ∉ G := fun bad => h (mem.mp bad)
        simp [h,hmiss]
    · have no : g i j ∉ G := fun h => compat (Nat.mem_divisors.mp (mem_filter.mp h).1).1
      have zeroErr : pairResidueError n (u i) (v j) (l i) (r i) (b j) (s j) = 0 := by
        unfold pairResidueError
        exact ite_eq_right compat
      change (@ite ℂ (gate i j ∧ D < g i j) (Classical.propDecidable _) (w i j) 0) =
        (if g i j ∈ G then if gate i j then w i j else 0 else 0)
      simp [no,w,zeroErr]
  let P (d x y : ℕ) := prefixResidueMass (n/d) x y
  have partBound (d : ℕ) (hd : d ∈ G) : ‖part d‖ ≤ W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(1+Real.log n)^2) := by
    let I' := I.filter fun i => d ∣ u i
    let J' := J.filter fun j => d ∣ v j
    have d0 : 0 < d := (Nat.zero_le _).trans_lt (mem_filter.mp hd).2
    have dn : d ∣ n := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
    have changed : part d = ∑ i ∈ I', ∑ j ∈ J', if gate i j ∧ g i j=d then w i j else 0 := by
      unfold part I' J'
      rw [sum_filter]
      refine sum_congr rfl fun i _ => ?_
      by_cases hi : d ∣ u i
      · rw [ite_eq_left hi,sum_filter]
        refine sum_congr rfl fun j _ => ?_
        by_cases hj : d ∣ v j
        · rw [ite_eq_left hj]
        · have ne : g i j≠d := fun h => hj (h ▸ Nat.gcd_dvd_right (u i) (v j))
          simp [hj,ne]
      · have ne (j : κ) : g i j≠d := fun h => hi (h ▸ Nat.gcd_dvd_left (u i) (v j))
        simp [hi,ne]
    have per (i : ι) (hi : i ∈ I') (j : κ) (hj : j ∈ J') :
        ‖(if gate i j ∧ g i j=d then w i j else 0)‖ ≤ ‖α i‖*‖β j‖*P d (u i/d) (v j/d) := by
      by_cases hg : gate i j ∧ g i j=d
      · rw [ite_eq_left hg]
        unfold w
        simp only [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have u0 := (mem_Icc.mp (lu i (mem_filter.mp hi).1)).1
        have v0 := (mem_Icc.mp (rv j (mem_filter.mp hj).1)).1
        have uu : 0 < u i/d := Nat.div_pos (Nat.le_of_dvd u0 (mem_filter.mp hi).2) d0
        have vv : 0 < v j/d := Nat.div_pos (Nat.le_of_dvd v0 (mem_filter.mp hj).2) d0
        have eq : (u i).gcd (v j)=d := hg.2
        have cop : (u i/d).Coprime (v j/d) := by
          have core : (u i/(u i).gcd (v j)).Coprime (v j/(u i).gcd (v j)) :=
            Nat.coprime_div_gcd_div_gcd (eq.symm ▸ d0)
          rwa [eq] at core
        have scale := pair_residue_error_eq_div_gcd (l := l i) (r := r i) (p := b j) (s := s j)
          u0 v0 (eq.symm ▸ dn)
        dsimp only at scale
        rw [eq] at scale
        rw [scale]
        exact norm_pair_residue_le_of_coprime uu vv cop
      · rw [ite_eq_right hg,norm_zero]
        exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (prefix_residue_mass_nonneg ..)
    have discrete : (∑ x ∈ Icc 1 (A/d), ∑ y ∈ Icc 1 (A/d), P d x y) ≤
        ((n/d : ℕ) : ℝ)*(T^2+(1+Real.log (n/d : ℕ))^2) :=
      sum_prefix_residue_mass_le (Nat.div_le_div_right An) T0
        (fun t ht => divCount t (ht.trans (Nat.div_le_self n d)))
    have dR : (0 : ℝ) < d := by exact_mod_cast d0
    have divR : ((n/d : ℕ) : ℝ) ≤ (n : ℝ)/((D : ℝ)+1) := calc
      _ ≤ (n : ℝ)/(d : ℝ) := (le_div_iff₀ dR).mpr (by exact_mod_cast Nat.div_mul_le_self n d)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by exact_mod_cast Nat.succ_le_of_lt (mem_filter.mp hd).2)
    have logR : Real.log (n/d : ℕ) ≤ Real.log n := Real.log_le_log
      (by exact_mod_cast Nat.div_pos (Nat.le_of_dvd n0 dn) d0) (by exact_mod_cast Nat.div_le_self n d)
    have log0 : 0 ≤ Real.log (n/d : ℕ) := Real.log_nonneg
      (by exact_mod_cast Nat.div_pos (Nat.le_of_dvd n0 dn) d0)
    rw [changed]
    calc
      _ ≤ ∑ i ∈ I', ‖∑ j ∈ J', if gate i j ∧ g i j=d then w i j else 0‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ I', ∑ j ∈ J', ‖α i‖*‖β j‖*P d (u i/d) (v j/d) := by
        exact sum_le_sum fun i hi => (norm_sum_le _ _).trans (sum_le_sum fun j hj => per i hi j hj)
      _ ≤ W^2*(∑ x ∈ Icc 1 (A/d), ∑ y ∈ Icc 1 (A/d), P d x y) :=
        sum_product_norm_le_of_step_mass I' J' (fun i => u i/d) (fun j => v j/d) α β (P d) W0
          (divided_step_range_of_dvd u d0 lu) (divided_step_range_of_dvd v d0 rv)
          (norm_divided_step_mass_le I u α d0 lm) (norm_divided_step_mass_le J v β d0 rm)
          (fun x _ y _ => prefix_residue_mass_nonneg _ x y)
      _ ≤ W^2*(((n/d : ℕ) : ℝ)*(T^2+(1+Real.log (n/d : ℕ))^2)) :=
        mul_le_mul_of_nonneg_left discrete (sq_nonneg _)
      _ ≤ _ := by
        rw [mul_assoc]
        gcongr
  have cardG : (G.card : ℝ) ≤ T :=
    (by exact_mod_cast card_le_card (filter_subset _ n.divisors) : (G.card : ℝ) ≤ n.divisors.card).trans
      (divCount n le_rfl)
  rw [split]
  calc
    _ ≤ ∑ d ∈ G, ‖part d‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ G, W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(1+Real.log n)^2) := sum_le_sum partBound
    _ = (G.card : ℝ)*(W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(1+Real.log n)^2)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right cardG (by positivity)

end

end B13BoundedStepProductSavingProof

end

/- Extended residue layer -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def extendedWaveItems (n : ℕ) {α : Type*} (I : Finset α) (u : α → ℕ) : Finset α :=
  I.filter fun i => u i ≤ extendedWideStepCap n

theorem old_step_cap_le_extended (n : ℕ) : wideMediumStepCap n ≤ extendedWideStepCap n := by
  rcases eq_or_ne n 0 with rfl | n0
  · norm_num [wideMediumStepCap,extendedWideStepCap,Real.zero_rpow]
  · apply Nat.floor_mono
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero n0) (by norm_num)

end

end B13BoundedStepProductSavingProof

end

/- Extended proper prime power -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4PairIntegral DyadicMixedB4TailScale DyadicMixedB4MoebiusGauss
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def extendedProperPowerRightItems (n : ℕ) : Finset RightLowWaveIndex :=
  (extendedWaveItems n ((rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n)) rightLowWaveStep).filter
    (fun j => ¬j.1.Prime ∧ IsPrimePow j.1)

private theorem extended_proper_power_right_data {n : ℕ} {j : RightLowWaveIndex}
    (hj : j ∈ extendedProperPowerRightItems n) :
    j ∈ rightLowWaveItems n ∧ 0 < j.2 ∧ j.2 ≤ cutoffU n ∧ j.1 ≤ rightLargeCofactorCut n := by
  have medium := (mem_filter.mp hj).1
  have cut := (mem_filter.mp medium).1
  have base := (mem_filter.mp cut).1
  have d := mem_Icc.mp (mem_sigma.mp base).2
  have bK := (mem_Ioc.mp (mem_sigma.mp base).1).2.trans (min_le_right _ _)
  exact ⟨base,d.1,d.2.trans (min_le_left _ _),bK⟩

theorem card_extended_proper_power_right_items_le (n : ℕ) :
    #(extendedProperPowerRightItems n) ≤
      (rightLargeCofactorCut n).sqrt*Nat.log 2 (rightLargeCofactorCut n)*cutoffU n := by
  let A := rightLargeCofactorCut n
  let J := extendedProperPowerRightItems n
  let K := properPrimePowersUpTo A ×ˢ Icc 1 (cutoffU n)
  have h : #J ≤ #K := by
    apply card_le_card_of_injOn (fun j : RightLowWaveIndex => (j.1,j.2))
    · intro j hj
      obtain ⟨_,q0,qU,bA⟩ := extended_proper_power_right_data hj
      have prop := (mem_filter.mp hj).2
      exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨prop.2.pos,bA⟩,prop⟩,mem_Icc.mpr ⟨q0,qU⟩⟩
    · rintro ⟨b,d⟩ _ ⟨b',d'⟩ _ eq
      have hb : b=b' := congrArg Prod.fst eq
      have hd : d=d' := congrArg Prod.snd eq
      subst b'
      subst d'
      rfl
  have hK : #K = #(properPrimePowersUpTo A)*cutoffU n := by simp [K,Nat.card_Icc]
  exact h.trans (hK.le.trans (Nat.mul_le_mul_right _ (card_proper_prime_powers_up_to_le A)))

def extendedProperPowerResidueSliceWith (gate : ℕ → ℕ → ℕ → Prop) (n : ℕ) : ℂ :=
  ∑ i ∈ extendedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep,
    ∑ j ∈ extendedProperPowerRightItems n,
      let u := leftBilinearStep i
      let v := rightLowWaveStep j
      @ite ℂ (gate n u v) (Classical.propDecidable _)
        (leftBilinearWeight n i*rightLowWaveWeight j*
          (pairResidueError n u v 0 (n/u) 0 (rightLowWaveUpper n j) : ℂ)) 0

private theorem norm_extended_proper_power_residue_slice_with_le (gate : ℕ → ℕ → ℕ → Prop) {n : ℕ} (n2 : 2 ≤ n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖extendedProperPowerResidueSliceWith gate n‖ ≤ 5*(n : ℝ)^(125/128 : ℝ)*T^3*logBudget n^3 := by
  let A := extendedWideStepCap n
  let K := rightLargeCofactorCut n
  let I := extendedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep
  let J := extendedProperPowerRightItems n
  let L := logBudget n
  let W := T^3*L
  have n0 : 0 < n := by omega
  have nR : (0 : ℝ) < n := by exact_mod_cast n0
  have An : A ≤ n := extended_wide_step_le n0
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have W0 : 0 ≤ W := by unfold W; positivity
  have leftMass : (∑ i ∈ I, ‖leftBilinearWeight n i‖) ≤ W*(A : ℝ) := by
    refine sum_norm_le_of_step_mass I leftBilinearStep (leftBilinearWeight n)
      (fun i hi => mem_Icc.mpr ⟨(mem_Icc.mp (bilateral_left_step_range (mem_filter.mp hi).1)).1,
        (mem_filter.mp hi).2⟩) ?_
    intro m hm
    have range : m ∈ Icc 1 n := mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans An⟩
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_left_step_mass n0 T0 divisors m range)
  have right (j : RightLowWaveIndex) (hj : j ∈ J) : ‖rightLowWaveWeight j‖ ≤ L := by
    obtain ⟨hbase,_,_,_⟩ := extended_proper_power_right_data hj
    have hb := mem_Ioc.mp (mem_sigma.mp hbase).1
    have b0 := (Nat.zero_le _).trans_lt hb.1
    have bn := hb.2.trans (min_le_left _ _)
    have mangoldt : ‖(vonMangoldt j.1 : ℂ)‖ ≤ L := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      exact vonMangoldt_le_log.trans (log_le_logBudget b0 bn)
    rw [rightLowWaveWeight,norm_mul,norm_neg]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (by simpa [moebiusComplex] using norm_moebiusComplex_le_one j.2)).trans mangoldt
  have cardJ : (#J : ℝ) ≤ (K.sqrt : ℝ)*(Nat.log 2 K : ℝ)*(cutoffU n : ℝ) := by
    exact_mod_cast card_extended_proper_power_right_items_le n
  have aCap : (A : ℝ) ≤ (n : ℝ)^(21/32 : ℝ) := Nat.floor_le (by positivity)
  have kCap : (K : ℝ) ≤ (n : ℝ)^(33/64 : ℝ) := Nat.floor_le (by positivity)
  have kN : K ≤ n := Nat.floor_le_of_le
    (Real.rpow_le_self_of_one_le (by exact_mod_cast n0) (by norm_num))
  have sqrtCap : (K.sqrt : ℝ) ≤ (n : ℝ)^(33/128 : ℝ) := by
    have sr : (K.sqrt : ℝ) ≤ Real.sqrt (K : ℝ) :=
      (Real.le_sqrt (by positivity) (by positivity)).mpr (by exact_mod_cast Nat.sqrt_le' K)
    refine sr.trans ((Real.sqrt_le_sqrt kCap).trans_eq ?_)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul nR.le]
    norm_num
  have uCap : (cutoffU n : ℝ) ≤ (n : ℝ)^(1/16 : ℝ) := Nat.floor_le (by positivity)
  have logCap : (Nat.log 2 K : ℝ) ≤ 5*L := by linarith only [natLog_succ_le n2 kN]
  have massR : (∑ j ∈ J, ‖rightLowWaveWeight j‖) ≤ (#J : ℝ)*L := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum right
  let f (i : ℕ × ℕ) (j : RightLowWaveIndex) :=
    let u := leftBilinearStep i
    let v := rightLowWaveStep j
    @ite ℂ (gate n u v) (Classical.propDecidable _)
      (leftBilinearWeight n i*rightLowWaveWeight j*
        (pairResidueError n u v 0 (n/u) 0 (rightLowWaveUpper n j) : ℂ)) 0
  have point (i : ℕ × ℕ) (j : RightLowWaveIndex) (hj : j ∈ J) : ‖f i j‖ ≤
      ‖leftBilinearWeight n i‖*‖rightLowWaveWeight j‖ := by
    have v0 := (mem_Icc.mp (bilateral_right_low_step_range (extended_proper_power_right_data hj).1)).1
    dsimp only [f]
    split_ifs
    · rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (abs_pair_residue_error_lt_one n _ _ _ _ _ _ v0).le
        (by positivity)).trans_eq (mul_one _)
    · simp only [norm_zero]
      positivity
  change ‖∑ i ∈ I, ∑ j ∈ J, f i j‖ ≤ _
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ‖f i j‖ := (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ‖leftBilinearWeight n i‖*‖rightLowWaveWeight j‖ :=
      sum_le_sum fun i _ => sum_le_sum fun j hj => point i j hj
    _ = (∑ i ∈ I, ‖leftBilinearWeight n i‖)*(∑ j ∈ J, ‖rightLowWaveWeight j‖) := (sum_mul_sum ..).symm
    _ ≤ (W*(A : ℝ))*((#J : ℝ)*L) := mul_le_mul leftMass massR (by positivity) (by positivity)
    _ ≤ (W*(A : ℝ))*(((K.sqrt : ℝ)*(Nat.log 2 K : ℝ)*(cutoffU n : ℝ))*L) := by gcongr
    _ ≤ (W*(n : ℝ)^(21/32 : ℝ))*(((n : ℝ)^(33/128 : ℝ)*(5*L)*(n : ℝ)^(1/16 : ℝ))*L) := by gcongr
    _ = 5*((n : ℝ)^(21/32 : ℝ)*(n : ℝ)^(33/128 : ℝ)*(n : ℝ)^(1/16 : ℝ))*T^3*L^3 := by unfold W; ring
    _ = _ := by rw [← Real.rpow_add nR, ← Real.rpow_add nR]; norm_num [L]

theorem extended_proper_power_residue_with_saving (gate : ℕ → ℕ → ℕ → Prop) : saving (extendedProperPowerResidueSliceWith gate) := by
  intro ε he
  obtain ⟨D,D1,dBound⟩ := divisor_envelope_at_power 1024 (by decide)
  let C := 5*D^3
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-(1/64) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/64)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(1/64) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have estimate : ∀ᶠ n : ℕ in atTop, ‖extendedProperPowerResidueSliceWith gate n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, eventually_log_budget_le_power (1/1024) (by norm_num),
      scaled.eventually_lt_const he] with n hn logb small
    have n1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have nr : (0 : ℝ) < n := zero_lt_one.trans_le n1
    have log0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/1024 : ℝ)
    let T := D*X
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1
      (Real.one_le_rpow n1 (by norm_num))
    have exponent : (n : ℝ)^(125/128 : ℝ)*X^6 ≤ (n : ℝ)^(-(1/64) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast nr.le, ← Real.rpow_add nr, ← Real.rpow_add_one nr.ne']
      exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
    calc
      _ ≤ 5*(n : ℝ)^(125/128 : ℝ)*T^3*logBudget n^3 :=
        norm_extended_proper_power_residue_slice_with_le gate hn T1 (dBound n)
      _ ≤ 5*(n : ℝ)^(125/128 : ℝ)*T^3*X^3 := by gcongr
      _ = C*((n : ℝ)^(125/128 : ℝ)*X^6) := by unfold C T; ring
      _ ≤ C*((n : ℝ)^(-(1/64) : ℝ)*(n : ℝ)) :=
        mul_le_mul_of_nonneg_left exponent (by unfold C; positivity)
      _ = (C*(n : ℝ)^(-(1/64) : ℝ))*(n : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
  obtain ⟨N,h⟩ := eventually_atTop.mp estimate
  exact ⟨N,fun n hn _ => h n hn⟩

end

end B13BoundedStepProductSavingProof

end

/- Extended hyperbola rows -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical

noncomputable section

theorem right_low_step_le_proved_medium_cap {n : ℕ} {j : RightLowWaveIndex}
    (hj : j ∈ rightLowWaveItems n) : rightLowWaveStep j ≤ wideMediumStepCap n := by
  have step := mem_Icc.mp (bilateral_right_low_step_range hj)
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast step.1.trans step.2
  have nr := zero_lt_one.trans_le n1
  obtain ⟨p,q⟩ := mem_sigma.mp hj
  have b : (j.1 : ℝ) ≤ (n : ℝ)^(33/64 : ℝ) :=
    (by exact_mod_cast (mem_Ioc.mp p).2.trans (min_le_right _ _) : (j.1 : ℝ) ≤ rightLargeCofactorCut n).trans
      (Nat.floor_le (by positivity))
  have d : (j.2 : ℝ) ≤ (n : ℝ)^(1/16 : ℝ) :=
    (by exact_mod_cast (mem_Icc.mp q).2.trans (min_le_left _ _) : (j.2 : ℝ) ≤ cutoffU n).trans
      (Nat.floor_le (by positivity))
  apply Nat.le_floor
  calc
    (rightLowWaveStep j : ℝ) = (j.2 : ℝ)*(j.1 : ℝ) := by unfold rightLowWaveStep; push_cast; rfl
    _ ≤ (n : ℝ)^(1/16 : ℝ)*(n : ℝ)^(33/64 : ℝ) := mul_le_mul d b (by positivity) (by positivity)
    _ = (n : ℝ)^(37/64 : ℝ) := by rw [← Real.rpow_add nr]; norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)

end

end B13BoundedStepProductSavingProof

end

/- Right divisor solution count -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

theorem progression_pair_solutions_card_le_interval_of_right_divisor {n u v l r b s d : ℕ}
    (u0 : 0 < u) (v0 : 0 < v) (dn : d ∣ n) (dv : d ∣ v) :
    (progressionPairSolutions n u v l r b s).card ≤
      (((Icc 1 (n-1)).filter (fun t => d ∣ t)).filter (fun t => u ∣ t ∧ v ∣ n-t)).card := by
  refine card_le_card_of_injOn (fun z : ℕ × ℕ => u*z.1) ?_ ?_
  · intro z hz
    obtain ⟨ranges,eq⟩ := mem_filter.mp hz
    change u*z.1+v*z.2=n at eq
    change u*z.1 ∈ ((Icc 1 (n-1)).filter (fun t => d ∣ t)).filter (fun t => u ∣ t ∧ v ∣ n-t)
    obtain ⟨xr,yr⟩ := mem_product.mp ranges
    have x0 : 0 < z.1 := (Nat.zero_le _).trans_lt (mem_Ioc.mp xr).1
    have y0 : 0 < z.2 := (Nat.zero_le _).trans_lt (mem_Ioc.mp yr).1
    have a0 := mul_pos u0 x0
    have c0 := mul_pos v0 y0
    have da : d ∣ u*z.1 := by
      have dif : n-v*z.2=u*z.1 := by omega
      rw [← dif]
      exact Nat.dvd_sub dn (dv.trans (dvd_mul_right _ _))
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨a0,by omega⟩,da⟩,dvd_mul_right _ _,⟨z.2,by omega⟩⟩
  · intro x hx y hy ex
    have p : x.1 = y.1 := Nat.eq_of_mul_eq_mul_left u0 ex
    have q : v*x.2 = v*y.2 := by
      have left := (mem_filter.mp hx).2
      have right := (mem_filter.mp hy).2
      change u*x.1+v*x.2=n at left
      change u*y.1+v*y.2=n at right
      rw [p] at left
      omega
    exact Prod.ext p (Nat.eq_of_mul_eq_mul_left v0 q)

theorem sum_prefix_solution_count_with_right_divisor_le {n A d : ℕ} {T : ℝ}
    (d0 : 0 < d) (dn : d ∣ n) (T0 : 0 ≤ T) (divCount : ∀ t ≤ n, (t.divisors.card : ℝ) ≤ T) :
    (∑ u ∈ Icc 1 A, ∑ v ∈ (Icc 1 A).filter (fun v => d ∣ v), prefixSolutionCount n u v) ≤ ((n/d : ℕ) : ℝ)*T^2 := by
  let K := (Icc 1 (n-1)).filter (fun t => d ∣ t)
  let U := Icc 1 A
  let V := U.filter (fun v => d ∣ v)
  let D (t : ℕ) := U.filter (fun u => u ∣ t)
  have divCard {t : ℕ} (t0 : 0 < t) (tn : t ≤ n) : ((D t).card : ℝ) ≤ T := by
    have b : (D t).card ≤ t.divisors.card := card_le_card (fun u hu =>
      Nat.mem_divisors.mpr ⟨(mem_filter.mp hu).2,t0.ne'⟩)
    exact (show ((D t).card : ℝ) ≤ (t.divisors.card : ℝ) by exact_mod_cast b).trans (divCount t tn)
  have cardId (u v : ℕ) :
      (((K.filter (fun t => u ∣ t ∧ v ∣ n-t)).card : ℕ) : ℝ) =
        ∑ t ∈ K, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0 := by
    rw [← sum_filter]
    simp
  have fibres (t : ℕ) :
      (∑ u ∈ U, ∑ v ∈ U, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0) =
        ((D t).card : ℝ)*((D (n-t)).card : ℝ) := by
    have count (z : ℕ) : ((D z).card : ℝ) = ∑ u ∈ U, if u ∣ z then (1 : ℝ) else 0 := by
      rw [← sum_filter]
      simp [D]
    rw [count t,count (n-t),sum_mul_sum]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    by_cases h : u ∣ t <;> by_cases k : v ∣ n-t <;> simp [h,k]
  change (∑ u ∈ U, ∑ v ∈ V, prefixSolutionCount n u v) ≤ ((n/d : ℕ) : ℝ)*T^2
  calc
    _ ≤ ∑ u ∈ U, ∑ v ∈ V, ∑ t ∈ K, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0 := by
      refine sum_le_sum fun u hu => sum_le_sum fun v hv => ?_
      rw [← cardId]
      unfold prefixSolutionCount
      have vdata := mem_filter.mp hv
      exact_mod_cast progression_pair_solutions_card_le_interval_of_right_divisor
        (mem_Icc.mp hu).1 (mem_Icc.mp vdata.1).1 dn vdata.2
    _ ≤ ∑ u ∈ U, ∑ v ∈ U, ∑ t ∈ K, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0 := by
      refine sum_le_sum (fun u _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_)
      intro v hv hnot
      exact sum_nonneg fun t _ => by split_ifs <;> positivity
    _ = ∑ t ∈ K, ∑ u ∈ U, ∑ v ∈ U, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0 := by
      calc
        _ = ∑ u ∈ U, ∑ t ∈ K, ∑ v ∈ U, if u ∣ t ∧ v ∣ n-t then (1 : ℝ) else 0 :=
          sum_congr rfl fun _ _ => sum_comm
        _ = _ := sum_comm
    _ = ∑ t ∈ K, ((D t).card : ℝ)*((D (n-t)).card : ℝ) := sum_congr rfl fun t _ => fibres t
    _ ≤ ∑ _ ∈ K, T^2 := by
      refine sum_le_sum fun t ht => ?_
      obtain ⟨t1,tb⟩ := mem_Icc.mp (mem_filter.mp ht).1
      rw [pow_two]
      exact mul_le_mul (divCard t1 (by omega)) (divCard (by omega) (Nat.sub_le _ _)) (by positivity) T0
    _ = (#K : ℝ)*T^2 := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have h : #K ≤ n/d := by
        have b : #K ≤ #(Icc 1 (n/d)) := by
          refine card_le_card_of_injOn (fun a : ℕ => a/d) ?_ ?_
          · intro a ha
            have range := mem_Icc.mp (mem_filter.mp ha).1
            have dA := (mem_filter.mp ha).2
            exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd range.1 dA) d0,
              Nat.div_le_div_right (range.2.trans (Nat.sub_le _ _))⟩
          · intro a ha b hb eq
            have same := congrArg (fun z : ℕ => z*d) eq
            simpa only [Nat.div_mul_cancel (mem_filter.mp ha).2,Nat.div_mul_cancel (mem_filter.mp hb).2] using same
        simpa [Nat.card_Icc] using b
      exact_mod_cast h

end

end B13BoundedStepProductSavingProof

end

/- Right divisor volume mass -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Geometric DyadicMixedB4GcdHarmonic DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical Finset

noncomputable section

theorem pair_volume_le_of_gcd_cap {n u v l r b s G : ℕ}
    (u0 : 0 < u) (v0 : 0 < v) (gCap : u.gcd v ≤ G) (ru : r*u ≤ n) :
    0 ≤ pairVolume n u v l r b s ∧
      pairVolume n u v l r b s ≤ (G : ℝ)*(n : ℝ)/((u : ℝ)*(v : ℝ)) := by
  let g := u.gcd v
  let d := v/g
  have ue : (0 : ℝ) < u := by exact_mod_cast u0
  have g0 : 0 < g := Nat.gcd_pos_of_pos_right u v0
  have gR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast g0
  have d0 : 0 < d := Nat.div_pos (Nat.le_of_dvd v0 (Nat.gcd_dvd_right u v)) g0
  have de : (0 : ℝ) < (d : ℝ) := by exact_mod_cast d0
  have mul : (d : ℝ)*(g : ℝ)=(v : ℝ) := by
    change ((v/(u.gcd v) : ℕ) : ℝ)*(u.gcd v : ℝ)=(v : ℝ)
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right u v)
  have cl : (0 : ℤ) ≤ pairLeftLower n u v l s := (Int.natCast_nonneg _).trans (le_max_left _ _)
  have cu : pairLeftUpper n u v r b ≤ (r : ℤ) := min_le_left _ _
  have len : max 0 (pairLeftUpper n u v r b-pairLeftLower n u v l s) ≤ (r : ℤ) :=
    max_le (Int.natCast_nonneg _) ((sub_le_self _ cl).trans cu)
  have L0 : (0 : ℝ) ≤ ((max 0 (pairLeftUpper n u v r b-pairLeftLower n u v l s) : ℤ) : ℝ) := by
    exact_mod_cast (le_max_left 0 (pairLeftUpper n u v r b-pairLeftLower n u v l s))
  have Lr : (((max 0 (pairLeftUpper n u v r b-pairLeftLower n u v l s) : ℤ)) : ℝ) ≤ (r : ℝ) := by exact_mod_cast len
  unfold pairVolume
  split_ifs
  · refine ⟨div_nonneg L0 de.le,?_⟩
    calc
      _ ≤ (r : ℝ)/(d : ℝ) := div_le_div_of_nonneg_right Lr de.le
      _ ≤ ((n : ℝ)/(u : ℝ))/(d : ℝ) := div_le_div_of_nonneg_right
        ((le_div_iff₀ ue).mpr (by exact_mod_cast ru)) de.le
      _ = (g : ℝ)*(n : ℝ)/((u : ℝ)*(v : ℝ)) := by rw [← mul]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast gCap) (by positivity)) (by positivity)
  · exact ⟨le_rfl,by positivity⟩

theorem norm_pair_residue_le_count_add_capped_volume {n u v p s G : ℕ}
    (u0 : 0 < u) (v0 : 0 < v) (gCap : u.gcd v ≤ G) :
    ‖(pairResidueError n u v 0 (n/u) p s : ℂ)‖ ≤
      prefixSolutionCount n u v+(G : ℝ)*(n : ℝ)/((u : ℝ)*(v : ℝ)) := by
  have vol := pair_volume_le_of_gcd_cap (l := 0) (r := n/u) (b := p) (s := s) u0 v0 gCap (Nat.div_mul_le_self n u)
  have count : (progressionPairSolutions n u v 0 (n/u) p s).card ≤
      (progressionPairSolutions n u v 0 (n/u) 0 (n/v)).card := by
    apply card_le_card
    intro z hz
    obtain ⟨base,eq⟩ := mem_filter.mp hz
    obtain ⟨rx,ry⟩ := mem_product.mp base
    have yr : z.2 ≤ n/v := (Nat.le_div_iff_mul_le v0).mpr (by rw [Nat.mul_comm]; omega)
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨rx,mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp ry).1,yr⟩⟩,eq⟩
  rw [Complex.norm_real,Real.norm_eq_abs]
  have f : pairResidueError n u v 0 (n/u) p s =
      ((progressionPairSolutions n u v 0 (n/u) p s).card : ℝ)-pairVolume n u v 0 (n/u) p s := by
    rw [progression_pair_count_eq_volume_add_error u0 v0]
    ring
  rw [f]
  exact (abs_sub _ _).trans (by
    rw [abs_of_nonneg (by positivity),abs_of_nonneg vol.1]
    exact add_le_add (by unfold prefixSolutionCount; exact_mod_cast count) vol.2)

private theorem inverse_step_sum_le_logBudget {A n : ℕ} (An : A ≤ n) :
    (∑ u ∈ Icc 1 A, (u : ℝ)⁻¹) ≤ logBudget n := by
  by_cases a0 : A=0
  · simpa [a0] using zero_le_one.trans (one_le_logBudget n)
  have ap : (0 : ℝ) < A := by exact_mod_cast Nat.pos_of_ne_zero a0
  calc
    _ = (harmonic A : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; rfl
    _ ≤ 1+Real.log A := by exact_mod_cast harmonic_le_one_add_log A
    _ ≤ _ := by
      unfold logBudget
      have ac : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast An
      linarith only [Real.log_le_log ap (show (A : ℝ) ≤ (n : ℝ)+2 by linarith)]

theorem sum_right_divisor_mass_le {n A d G : ℕ} (An : A ≤ n) (d0 : 0 < d) (dn : d ∣ n)
    {T : ℝ} (T0 : 0 ≤ T) (divCount : ∀ z ≤ n, (z.divisors.card : ℝ) ≤ T) :
    (∑ u ∈ Icc 1 A, ∑ v ∈ (Icc 1 A).filter (fun v => d ∣ v),
      (prefixSolutionCount n u v+(G : ℝ)*(n : ℝ)/((u : ℝ)*(v : ℝ)))) ≤
        ((n : ℝ)/(d : ℝ))*(T^2+(G : ℝ)*logBudget n^2) := by
  let L := logBudget n
  have L0 : 0 ≤ L := zero_le_one.trans (one_le_logBudget n)
  let U := Icc 1 A
  let V := U.filter (fun v => d ∣ v)
  have dp : (0 : ℝ) < d := by exact_mod_cast d0
  have nn : ((n/d : ℕ) : ℝ) ≤ (n : ℝ)/(d : ℝ) :=
    (le_div_iff₀ dp).mpr (by exact_mod_cast Nat.div_mul_le_self n d)
  have aMass : (∑ u ∈ U, (u : ℝ)⁻¹) ≤ L := inverse_step_sum_le_logBudget An
  have bMass : (∑ v ∈ V, (v : ℝ)⁻¹) ≤ ((d : ℝ)⁻¹)*L := by
    unfold V U
    rw [sum_inverse_multiples d A d0]
    exact mul_le_mul_of_nonneg_left (inverse_step_sum_le_logBudget ((Nat.div_le_self A d).trans An)) (by positivity)
  have eq : (∑ u ∈ U, ∑ v ∈ V, (G : ℝ)*(n : ℝ)/((u : ℝ)*(v : ℝ))) =
      (G : ℝ)*(n : ℝ)*(∑ u ∈ U, (u : ℝ)⁻¹)*(∑ v ∈ V, (v : ℝ)⁻¹) := by
    rw [mul_assoc ((G : ℝ)*(n : ℝ)),sum_mul_sum,mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [div_eq_mul_inv,mul_inv_rev,mul_comm ((v : ℝ)⁻¹)]
  change (∑ u ∈ U, ∑ v ∈ V, (prefixSolutionCount n u v+(G : ℝ)*(n : ℝ)/((u : ℝ)*(v : ℝ)))) ≤ _
  simp_rw [sum_add_distrib]
  rw [eq]
  have cnt := sum_prefix_solution_count_with_right_divisor_le (A := A) d0 dn T0 divCount
  have massA0 : 0 ≤ ∑ u ∈ U, (u : ℝ)⁻¹ := sum_nonneg fun _ _ => by positivity
  have massB0 : 0 ≤ ∑ v ∈ V, (v : ℝ)⁻¹ := sum_nonneg fun _ _ => by positivity
  calc
    _ ≤ ((n/d : ℕ) : ℝ)*T^2+((G : ℝ)*(n : ℝ))*L*((d : ℝ)⁻¹*L) := by gcongr
    _ ≤ ((n : ℝ)/(d : ℝ))*T^2+((G : ℝ)*(n : ℝ))*L*((d : ℝ)⁻¹*L) := by gcongr
    _ = _ := by unfold L; ring

end

end B13BoundedStepProductSavingProof

end

/- Large right divisor residue -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical Finset

noncomputable section

def largeRightDivisorResidueFamily (n D G : ℕ) {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (u : ι → ℕ) (v p s : κ → ℕ)
    (α : ι → ℂ) (β : κ → ℂ) (gate : ι → κ → Prop) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J,
    @ite ℂ (gate i j ∧ (u i).gcd (v j) ≤ G ∧ D < (v j).gcd n) (Classical.propDecidable _)
      (α i*β j*(pairResidueError n (u i) (v j) 0 (n/u i) (p j) (s j) : ℂ)) 0

theorem norm_large_right_divisor_residue_family_le {n D G A : ℕ} (n0 : 0 < n) (An : A ≤ n)
    {ι κ : Type*} (I : Finset ι) (J : Finset κ) (u : ι → ℕ) (v p s : κ → ℕ)
    (α : ι → ℂ) (β : κ → ℂ) (gate : ι → κ → Prop)
    {W T : ℝ} (W0 : 0 ≤ W) (T0 : 0 ≤ T) (divCount : ∀ z ≤ n, (z.divisors.card : ℝ) ≤ T)
    (lu : ∀ i ∈ I, u i ∈ Icc 1 A) (rv : ∀ j ∈ J, v j ∈ Icc 1 A)
    (lm : ∀ m ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i = m), ‖α i‖) ≤ W)
    (rm : ∀ m ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j = m), ‖β j‖) ≤ W) :
    ‖largeRightDivisorResidueFamily n D G I J u v p s α β gate‖ ≤
      T*(W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(G : ℝ)*logBudget n^2)) := by
  let K := n.divisors.filter (D < ·)
  let F (d x y : ℕ) : ℝ :=
    if d ∣ y then prefixSolutionCount n x y+(G : ℝ)*(n : ℝ)/((x : ℝ)*(y : ℝ)) else 0
  let term (i : ι) (j : κ) : ℂ :=
    @ite ℂ (gate i j ∧ (u i).gcd (v j) ≤ G ∧ D < (v j).gcd n) (Classical.propDecidable _)
      (α i*β j*(pairResidueError n (u i) (v j) 0 (n/u i) (p j) (s j) : ℂ)) 0
  have F0 (d x y : ℕ) : 0 ≤ F d x y := by
    unfold F
    split_ifs
    · unfold prefixSolutionCount
      positivity
    · exact le_rfl
  have per (i : ι) (hi : i ∈ I) (j : κ) (hj : j ∈ J) :
      ‖term i j‖ ≤ ∑ d ∈ K, ‖α i‖*‖β j‖*F d (u i) (v j) := by
    by_cases sel : gate i j ∧ (u i).gcd (v j) ≤ G ∧ D < (v j).gcd n
    · unfold term
      rw [ite_eq_left sel,norm_mul,norm_mul]
      let d := (v j).gcd n
      have dn : d ∣ n := Nat.gcd_dvd_right (v j) n
      have dv : d ∣ v j := Nat.gcd_dvd_left (v j) n
      have mem : d ∈ K := mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dn,n0.ne'⟩,sel.2.2⟩
      have est := norm_pair_residue_le_count_add_capped_volume (n := n) (p := p j) (s := s j)
        (mem_Icc.mp (lu i hi)).1 (mem_Icc.mp (rv j hj)).1 sel.2.1
      have b : ‖(pairResidueError n (u i) (v j) 0 (n/u i) (p j) (s j) : ℂ)‖ ≤ F d (u i) (v j) := by
        unfold F
        rwa [ite_eq_left dv]
      exact (mul_le_mul_of_nonneg_left b (by positivity)).trans
        (single_le_sum (fun z _ => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (F0 _ _ _)) mem)
    · unfold term
      rw [ite_eq_right sel,norm_zero]
      exact sum_nonneg fun d _ => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (F0 _ _ _)
  have dBound (d : ℕ) (hd : d ∈ K) :
      (∑ i ∈ I, ∑ j ∈ J, ‖α i‖*‖β j‖*F d (u i) (v j)) ≤
        W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(G : ℝ)*logBudget n^2) := by
    obtain ⟨base,above⟩ := mem_filter.mp hd
    have dn := (Nat.mem_divisors.mp base).1
    have d0 : 0 < d := (Nat.zero_le _).trans_lt above
    have dp : (0 : ℝ) < d := by exact_mod_cast d0
    have dR : (D : ℝ)+1 ≤ (d : ℝ) := by exact_mod_cast Nat.succ_le_of_lt above
    have cmp : (n : ℝ)/(d : ℝ) ≤ (n : ℝ)/((D : ℝ)+1) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) dR
    have h := sum_product_norm_le_of_step_mass I J u v α β (F d) W0 lu rv lm rm
      (fun x _ y _ => F0 d x y)
    refine h.trans ?_
    unfold F
    simp_rw [← sum_filter]
    calc
      _ ≤ W^2*(((n : ℝ)/(d : ℝ))*(T^2+(G : ℝ)*logBudget n^2)) :=
        mul_le_mul_of_nonneg_left (sum_right_divisor_mass_le (G := G) An d0 dn T0 divCount) (sq_nonneg _)
      _ ≤ _ := by rw [mul_assoc]; gcongr
  have kc : (K.card : ℝ) ≤ T :=
    (by exact_mod_cast card_le_card (filter_subset _ n.divisors) : (K.card : ℝ) ≤ n.divisors.card).trans
      (divCount n le_rfl)
  change ‖∑ i ∈ I, ∑ j ∈ J, term i j‖ ≤ _
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ‖term i j‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ∑ d ∈ K, ‖α i‖*‖β j‖*F d (u i) (v j) :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => per i hi j hj
    _ = ∑ d ∈ K, ∑ i ∈ I, ∑ j ∈ J, ‖α i‖*‖β j‖*F d (u i) (v j) := by
      calc
        _ = ∑ i ∈ I, ∑ d ∈ K, ∑ j ∈ J, ‖α i‖*‖β j‖*F d (u i) (v j) :=
          sum_congr rfl fun _ _ => sum_comm
        _ = _ := sum_comm
    _ ≤ ∑ _ ∈ K, W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(G : ℝ)*logBudget n^2) :=
      sum_le_sum dBound
    _ = (K.card : ℝ)*(W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(G : ℝ)*logBudget n^2)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right kc (by positivity)

end

end B13BoundedStepProductSavingProof

end

/- Extended target divisor cut -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical Finset

noncomputable section

def targetDivisorCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/128 : ℝ)⌋₊

end

end B13BoundedStepProductSavingProof

end

/- Gcd capped interval error -/
section

namespace B13BoundedStepProductSavingProof

open DyadicMixedB4Scale
open scoped Classical

noncomputable section

theorem coprime_capped_interval_residue_eq_two_centered {n u v lo s : ℕ} [NeZero v]
    (hu : 0 < u) (ord : lo < s) (sv : v*s ≤ n) (cop : u.Coprime v) :
    let z := (n : ZMod v)*(u : ZMod v)⁻¹
    (pairResidueError n u v 0 (n/u) lo s : ℂ) =
      centeredIntIntervalResidue v 0 (((n-v*(lo+1) : ℕ) : ℤ)/(u : ℤ)) z -
        centeredIntIntervalResidue v 0 ((((n-v*s)-1 : ℕ) : ℤ)/(u : ℤ)) z := by
  dsimp only
  let a := (((n-v*s)-1 : ℕ) : ℤ)/(u : ℤ)
  let b := ((n-v*(lo+1) : ℕ) : ℤ)/(u : ℤ)
  let z := (n : ZMod v)*(u : ZMod v)⁻¹
  have vp : 0 < v := Nat.pos_of_ne_zero (NeZero.ne v)
  have up : (0 : ℤ) < u := by exact_mod_cast hu
  have small : v*(lo+1) ≤ v*s := Nat.mul_le_mul_left v (Nat.succ_le_of_lt ord)
  have hvn : v*(lo+1) ≤ n := small.trans sv
  have decomp : (((n-v*s : ℕ) : ℤ)) = (n : ℤ)-(v : ℤ)*(s : ℤ) := by
    rw [Int.ofNat_sub sv,Nat.cast_mul]
  have lower : pairLeftLower n u v 0 (s) = a := by
    unfold pairLeftLower a
    rw [Nat.cast_zero,← decomp]
    by_cases zero : (n-v*s) = 0
    · rw [zero,Nat.zero_sub,Nat.cast_zero,Int.zero_ediv]
      apply max_eq_left
      apply Int.lt_add_one_iff.mp
      rw [zero_add,Int.ediv_lt_iff_lt_mul up,one_mul]
      omega
    · have rem1 : 1 ≤ (n-v*s) := Nat.pos_of_ne_zero zero
      rw [Int.ofNat_sub rem1,Nat.cast_one]
      apply max_eq_right
      have remInt : (1 : ℤ) ≤ ((n-v*s) : ℕ) := by exact_mod_cast rem1
      exact Int.ediv_nonneg (sub_nonneg.mpr remInt) up.le
  have upper : pairLeftUpper n u v (n/u) lo = b := by
    unfold pairLeftUpper b
    rw [Int.natCast_ediv,Int.ofNat_sub hvn,Nat.cast_mul,Nat.cast_add,Nat.cast_one,min_eq_right]
    exact Int.ediv_le_ediv up (sub_le_self _ (by positivity))
  have rin : n-v*s ≤ n-v*(lo+1) := Nat.sub_le_sub_left small n
  have order : a ≤ b := by
    unfold a b
    exact Int.ediv_le_ediv up (by exact_mod_cast (Nat.sub_le _ _).trans rin)
  have a0 : 0 ≤ a := by unfold a; exact Int.ediv_nonneg (by positivity) up.le
  rw [pair_residue_error_eq_centered_of_coprime cop (by rw [lower,upper]; exact order),lower,upper]
  change centeredIntIntervalResidue v a b z =
    centeredIntIntervalResidue v 0 b z-centeredIntIntervalResidue v 0 a z
  unfold centeredIntIntervalResidue
  rw [int_interval_residue_count_add v a0 order]
  push_cast
  ring

theorem divided_capped_interval_residue_eq_two_centered {n u v lo s : ℕ}
    (u0 : 0 < u) (v0 : 0 < v) (ord : lo < s) (sv : v*s ≤ n) (gn : u.gcd v ∣ n) :
    let g := u.gcd v
    let N := n/g
    let U := u/g
    let V := v/g
    let z := (N : ZMod V)*(U : ZMod V)⁻¹
    (pairResidueError n u v 0 (n/u) lo s : ℂ) =
      centeredIntIntervalResidue V 0 (((N-V*(lo+1) : ℕ) : ℤ)/(U : ℤ)) z -
        centeredIntIntervalResidue V 0 (((N-V*s-1 : ℕ) : ℤ)/(U : ℤ)) z := by
  dsimp only
  let g := u.gcd v
  let N := n/g
  let U := u/g
  let V := v/g
  have g0 : 0 < g := Nat.gcd_pos_of_pos_right u v0
  have U0 : 0 < U := Nat.div_pos (Nat.le_of_dvd u0 (Nat.gcd_dvd_left u v)) g0
  have V0 : 0 < V := Nat.div_pos (Nat.le_of_dvd v0 (Nat.gcd_dvd_right u v)) g0
  let _ : NeZero V := ⟨V0.ne'⟩
  have VS : V*s ≤ N := (Nat.le_div_iff_mul_le g0).mpr (by
    unfold V
    rw [mul_right_comm (v/g) s g,Nat.div_mul_cancel (Nat.gcd_dvd_right u v)]
    exact sv)
  have cop : U.Coprime V := Nat.coprime_div_gcd_div_gcd g0
  have eq : N/U=n/u := by
    unfold N U
    rw [Nat.div_div_eq_div_mul,Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)]
  have h := pair_residue_error_eq_div_gcd (l := 0) (r := n/u) (p := lo) (s := s) u0 v0 gn
  dsimp only at h
  rw [h]
  change (pairResidueError N U V 0 (n/u) lo s : ℂ) = _
  rw [← eq]
  exact coprime_capped_interval_residue_eq_two_centered U0 ord VS cop

end

end B13BoundedStepProductSavingProof

end

/- Expanded high divided hyperbola windows -/
section

namespace B13BoundedStepProductSavingProof

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

end B13BoundedStepProductSavingProof

end

/- Reciprocal tuple denominators -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

def reciprocalNumerator {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℕ) (sign : ι → ℤ) : ℤ :=
  ∑ i ∈ s, sign i * ((∏ j ∈ s.erase i, a j : ℕ) : ℤ)

theorem reciprocal_numerator_eq_zero_of_small_congruence {ι : Type*} [DecidableEq ι]
    {m A : ℕ} [NeZero m] (s : Finset ι) (a : ι → ℕ) (sign : ι → ℤ)
    (small : s.card*A^(s.card-1) < m)
    (aTop : ∀ i ∈ s, a i ≤ A) (aUnit : ∀ i ∈ s, IsUnit (a i : ZMod m))
    (signs : ∀ i ∈ s, sign i = 1 ∨ sign i = -1)
    (rel : ∑ i ∈ s, (sign i : ZMod m)*(a i : ZMod m)⁻¹ = 0) :
    reciprocalNumerator s a sign = 0 := by
  let v (i : ι) := ∏ j ∈ s.erase i, a j
  have cast (i : ι) (hi : i ∈ s) :
      (v i : ZMod m) = (∏ j ∈ s, (a j : ZMod m))*(a i : ZMod m)⁻¹ := by
    have hp := prod_erase_mul s (fun j => (a j : ZMod m)) hi
    rw [← hp, mul_assoc, mul_comm (a i : ZMod m), ZMod.inv_mul_of_unit _ (aUnit i hi), mul_one]
    simp only [v,Nat.cast_prod]
  have modZero : (reciprocalNumerator s a sign : ZMod m) = 0 := by
    unfold reciprocalNumerator
    push_cast
    rw [← mul_zero (∏ j ∈ s, (a j : ZMod m)), ← rel, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [show (∏ j ∈ s.erase i, (a j : ZMod m)) = (v i : ZMod m) by simp only [v,Nat.cast_prod],cast i hi]
    ring
  have bound (i : ι) (hi : i ∈ s) : v i ≤ A^(s.card-1) := by
    calc
      _ ≤ ∏ _ ∈ s.erase i, A := prod_le_prod fun j hj => aTop j (mem_of_mem_erase hj)
      _ = _ := by simp only [prod_const,card_erase_of_mem hi]
  have absLimit : |reciprocalNumerator s a sign| ≤ ((s.card*A^(s.card-1) : ℕ) : ℤ) := by
    unfold reciprocalNumerator
    refine (abs_sum_le_sum_abs ..).trans ?_
    calc
      _ ≤ ∑ _ ∈ s, ((A^(s.card-1) : ℕ) : ℤ) := by
        refine sum_le_sum fun i hi => ?_
        have h : (v i : ℤ) ≤ ((A^(s.card-1) : ℕ) : ℤ) := by exact_mod_cast bound i hi
        change |sign i * (v i : ℤ)| ≤ _
        rcases signs i hi with e | e <;> simpa [e] using h
      _ = _ := by rw [sum_const,nsmul_eq_mul]; push_cast; rfl
  have absNat : (reciprocalNumerator s a sign).natAbs ≤ s.card*A^(s.card-1) := by
    rw [← Int.natCast_natAbs] at absLimit
    exact_mod_cast absLimit
  have d := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp modZero
  have dd : m ∣ (reciprocalNumerator s a sign).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr d
  apply Int.natAbs_eq_zero.mp
  by_contra k
  exact (not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero k) dd)) (absNat.trans_lt small)

theorem reciprocal_numerator_zero_denom_divides_others {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {a : ι → ℕ} {sign : ι → ℤ}
    (signs : ∀ i ∈ s, sign i = 1 ∨ sign i = -1)
    (eq : reciprocalNumerator s a sign = 0) {i : ι} (hi : i ∈ s) :
    a i ∣ ∏ j ∈ s.erase i, a j := by
  let f (k : ι) : ℤ := sign k * ((∏ j ∈ s.erase k, a j : ℕ) : ℤ)
  have hh : (∑ j ∈ s.erase i, f j)+f i = 0 :=
    (sum_erase_add s f hi).trans eq
  have other : (a i : ℤ) ∣ ∑ j ∈ s.erase i, f j := by
    refine dvd_sum fun j hj => ?_
    have h := mem_erase.mp hj
    have div : a i ∣ ∏ k ∈ s.erase j, a k :=
      dvd_prod_of_mem a (mem_erase.mpr ⟨h.1.symm,hi⟩)
    have cd : (a i : ℤ) ∣ ((∏ k ∈ s.erase j, a k : ℕ) : ℤ) := by exact_mod_cast div
    exact dvd_mul_of_dvd_right cd _
  have e : f i = -(∑ j ∈ s.erase i, f j) := by linarith only [hh]
  have d : (a i : ℤ) ∣ f i := by rw [e]; exact dvd_neg.mpr other
  change (a i : ℤ) ∣ sign i * ((∏ j ∈ s.erase i, a j : ℕ) : ℤ) at d
  apply Int.natCast_dvd_natCast.mp
  rcases signs i hi with h | h <;> simp [h] at d ⊢ <;> exact d

theorem lcm_square_dvd_product_of_reciprocal_numerator_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℕ) (sign : ι → ℤ)
    (a0 : ∀ i ∈ s, a i ≠ 0) (signs : ∀ i ∈ s, sign i = 1 ∨ sign i = -1)
    (eq : reciprocalNumerator s a sign = 0) :
    (s.lcm a)^2 ∣ ∏ i ∈ s, a i := by
  rcases s.eq_empty_or_nonempty with empty | nonempty
  · simp [empty]
  have l0 : s.lcm a ≠ 0 := lcm_ne_zero_iff.mpr a0
  have p0 : (∏ i ∈ s, a i) ≠ 0 := prod_ne_zero_iff.mpr a0
  apply (Nat.factorization_le_iff_dvd (pow_ne_zero 2 l0) p0).mp
  intro p
  rw [Nat.factorization_pow,Finsupp.nsmul_apply]
  change 2*(s.lcm a).factorization p ≤ _
  rw [Finset.factorization_lcm a0]
  obtain ⟨i,hi,top⟩ := exists_mem_eq_sup s nonempty fun j => (a j).factorization p
  have div := reciprocal_numerator_zero_denom_divides_others signs eq hi
  have rest0 : (∏ j ∈ s.erase i, a j) ≠ 0 := prod_ne_zero_iff.mpr fun j hj => a0 j (mem_of_mem_erase hj)
  have exp := (Nat.factorization_le_iff_dvd (a0 i hi) rest0).mpr div p
  rw [Nat.factorization_prod_apply (fun j hj => a0 j (mem_of_mem_erase hj))] at exp
  rw [top,Nat.factorization_prod_apply a0,← sum_erase_add s (fun j => (a j).factorization p) hi]
  omega

end

end B13BoundedStepProductSavingProof

end

/- Reciprocal tuple energy -/
section

namespace B13BoundedStepProductSavingProof

open Finset Fintype
open scoped Classical Finset

noncomputable section

def reciprocalTuples (I : Finset ℕ) (k : ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun _ => I

def reciprocalTupleKey (m k : ℕ) (x : Fin k → ℕ) : ZMod m :=
  ∑ i, (x i : ZMod m)⁻¹

def reciprocalTupleCollisions (m : ℕ) (I : Finset ℕ) (k : ℕ) :
    Finset ((Fin k → ℕ) × (Fin k → ℕ)) :=
  ((reciprocalTuples I k) ×ˢ (reciprocalTuples I k)).filter
    (fun x => reciprocalTupleKey m k x.1 = reciprocalTupleKey m k x.2)

theorem reciprocal_tuple_collisions_card_le {m A k D : ℕ} [NeZero m]
    (small : (2*k)*A^(2*k-1) < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ a ∈ I, a.Coprime m)
    (divisors : ∀ z ≤ A^k, z.divisors.card ≤ D) :
    (reciprocalTupleCollisions m I k).card ≤ A^k*D^(2*k) := by
  let ι := Fin k ⊕ Fin k
  let Q := reciprocalTupleCollisions m I k
  let signs : ι → ℤ := Sum.elim (fun _ => 1) (fun _ => -1)
  let entries (x : (Fin k → ℕ) × (Fin k → ℕ)) : ι → ℕ := Sum.elim x.1 x.2
  let top (x : (Fin k → ℕ) × (Fin k → ℕ)) := (univ : Finset ι).lcm (entries x)
  let choices (z : ℕ) := Fintype.piFinset (fun _ : ι => z.divisors)
  let Z := (Icc 1 (A^k)).sigma choices
  have nι : (univ : Finset ι).card = 2*k := by
    simp [ι, two_mul]
  have good (x : (Fin k → ℕ) × (Fin k → ℕ)) (hx : x ∈ Q) (i : ι) : entries x i ∈ I := by
    have mem := mem_product.mp (mem_filter.mp hx).1
    cases i with
    | inl j => exact Fintype.mem_piFinset.mp mem.1 j
    | inr j => exact Fintype.mem_piFinset.mp mem.2 j
  have topBound (x : (Fin k → ℕ) × (Fin k → ℕ)) (hx : x ∈ Q) : top x ∈ Icc 1 (A^k) := by
    let a := entries x
    let S := (univ : Finset ι)
    have unit (i : ι) : IsUnit (a i : ZMod m) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (copI _ (good x hx i))
    have range (i : ι) : a i ∈ Icc 1 A := Icap (good x hx i)
    have sg (i : ι) : signs i = 1 ∨ signs i = -1 := by cases i <;> simp [signs]
    have rel : ∑ i ∈ S, (signs i : ZMod m)*(a i : ZMod m)⁻¹ = 0 := by
      unfold S
      rw [Fintype.sum_sum_type]
      simp only [a, entries, signs, Sum.elim_inl, Sum.elim_inr, Int.cast_one, Int.cast_neg,
        one_mul, neg_mul, sum_neg_distrib, add_neg_eq_zero]
      exact (mem_filter.mp hx).2
    have solution := reciprocal_numerator_eq_zero_of_small_congruence S a signs
      (by simpa only [S,nι] using small)
      (fun i _ => (mem_Icc.mp (range i)).2) (fun i _ => unit i) (fun i _ => sg i) rel
    have a0 (i : ι) : a i ≠ 0 := (Nat.zero_lt_one.trans_le (mem_Icc.mp (range i)).1).ne'
    have L0 : 0 < top x := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr fun i _ => a0 i)
    have bound : (top x)^2 ≤ (A^k)^2 := calc
      _ ≤ ∏ i ∈ S, a i := Nat.le_of_dvd (Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr fun i _ => a0 i))
        (lcm_square_dvd_product_of_reciprocal_numerator_zero S a signs (fun i _ => a0 i)
          (fun i _ => sg i) solution)
      _ ≤ ∏ _ ∈ S, A := prod_le_prod fun i _ => (mem_Icc.mp (range i)).2
      _ = _ := by simp only [S,prod_const,nι,← pow_mul,Nat.mul_comm k 2]
    have cap : top x ≤ A^k := by
      by_contra! high
      exact (not_lt_of_ge bound) (pow_lt_pow_left₀ high (Nat.zero_le _) (by decide))
    exact mem_Icc.mpr ⟨L0,cap⟩
  have lc (x : (Fin k → ℕ) × (Fin k → ℕ)) (hx : x ∈ Q) : (⟨top x, entries x⟩ : Σ z : ℕ, ι → ℕ) ∈ Z := by
    have b := topBound x hx
    refine mem_sigma.mpr ⟨b,Fintype.mem_piFinset.mpr fun i => ?_⟩
    exact Nat.mem_divisors.mpr ⟨dvd_lcm (mem_univ i),
      (Nat.zero_lt_one.trans_le (mem_Icc.mp b).1).ne'⟩
  have embed : Q.card ≤ Z.card := by
    refine card_le_card_of_injOn (fun x => (⟨top x, entries x⟩ : Σ z : ℕ, ι → ℕ)) lc
      fun x _ y _ eq => ?_
    have e : entries x = entries y := congrArg (fun z : Σ _ : ℕ, ι → ℕ => z.2) eq
    exact Prod.ext (funext fun j => congrFun e (Sum.inl j)) (funext fun j => congrFun e (Sum.inr j))
  have c (z : ℕ) (hz : z ∈ Icc 1 (A^k)) : (choices z).card ≤ D^(2*k) := by
    unfold choices
    rw [Fintype.card_piFinset,Finset.prod_const,nι]
    exact pow_le_pow_left₀ (Nat.zero_le _) (divisors z (mem_Icc.mp hz).2) _
  calc
    _ ≤ Z.card := embed
    _ = ∑ z ∈ Icc 1 (A^k), (choices z).card := Finset.card_sigma _ _
    _ ≤ ∑ _ ∈ Icc 1 (A^k), D^(2*k) := sum_le_sum c
    _ = _ := by simp

theorem reciprocal_tuple_energy_eq_collision_count (m k : ℕ) [NeZero m] (I : Finset ℕ) :
    (∑ z : ZMod m, (((reciprocalTuples I k).filter (fun x => reciprocalTupleKey m k x=z)).card)^2) =
    (reciprocalTupleCollisions m I k).card := by
  let X := reciprocalTuples I k
  let Q := reciprocalTupleCollisions m I k
  let key (x : (Fin k → ℕ) × (Fin k → ℕ)) := reciprocalTupleKey m k x.1
  let Xz (z : ZMod m) := X.filter (fun x => reciprocalTupleKey m k x=z)
  have split (z : ZMod m) : Q.filter (fun x => key x=z) = Xz z ×ˢ Xz z := by
    ext x
    simp only [Q,reciprocalTupleCollisions,mem_filter,mem_product,Xz,X,key]
    constructor
    · rintro ⟨⟨⟨h1,h2⟩,eq⟩,ea⟩
      exact ⟨⟨h1,ea⟩,h2,eq.symm.trans ea⟩
    · rintro ⟨⟨h1,ea⟩,h2,eb⟩
      exact ⟨⟨⟨h1,h2⟩,ea.trans eb.symm⟩,ea⟩
  have H := sum_fiberwise_of_maps_to (s := Q) (t := univ) (g := key)
      (fun x _ => mem_univ (key x)) (fun _ => 1 : _ → ℕ)
  change (∑ z : ZMod m, (Xz z).card^2) = Q.card
  simpa [split,nsmul_eq_mul,card_product,pow_two] using H

end

end B13BoundedStepProductSavingProof

end

/- Reciprocal tuple even moment -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

private theorem std_add_char_sum {ι : Type*} {m : ℕ} [NeZero m] (s : Finset ι) (f : ι → ZMod m) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ht => simp [ha,ht,AddChar.map_add_eq_mul]

theorem inverse_frequency_even_moment_small_le {m A k D : ℕ} [NeZero m]
    (small : (2*k)*A^(2*k-1) < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ a ∈ I, a.Coprime m)
    (divisors : ∀ z ≤ A^k, z.divisors.card ≤ D)
    (weight : ℕ → ℂ) {W : ℝ} (W0 : 0 ≤ W) (wBound : ∀ a ∈ I, ‖weight a‖ ≤ W) :
    (∑ x : ZMod m, ‖inverseFrequencySum m I weight x‖^(2*k)) ≤
      (m : ℝ)*(A : ℝ)^k*(D : ℝ)^(2*k)*W^(2*k) := by
  let X := reciprocalTuples I k
  let key := reciprocalTupleKey m k
  let fibres (z : ZMod m) := X.filter (fun x => key x=z)
  let coef (z : ZMod m) : ℂ := ∑ x ∈ fibres z, ∏ i, weight (x i)
  let H := inverseFrequencySum m I weight
  have expand (x : ZMod m) : (H x)^k =
      ∑ z : ZMod m, coef z*ZMod.stdAddChar (x*z) := by
    unfold H inverseFrequencySum
    rw [Finset.sum_pow']
    change (∑ a ∈ X, ∏ i, weight (a i)*ZMod.stdAddChar (x*(a i : ZMod m)⁻¹)) = _
    calc
      _ = ∑ a ∈ X, (∏ i, weight (a i))*ZMod.stdAddChar (x*key a) := by
        refine sum_congr rfl fun a _ => ?_
        rw [prod_mul_distrib]
        congr 1
        unfold key reciprocalTupleKey
        rw [mul_sum,std_add_char_sum]
      _ = _ := by
        rw [← sum_fiberwise_of_maps_to (fun a _ => mem_univ (key a))]
        refine sum_congr rfl fun z _ => ?_
        unfold coef
        rw [sum_mul]
        exact sum_congr rfl fun a ha => by rw [(mem_filter.mp ha).2]
  have energy : (∑ z : ZMod m, ((fibres z).card : ℝ)^2) ≤ (A : ℝ)^k*(D : ℝ)^(2*k) := by
    have bound := reciprocal_tuple_collisions_card_le small I Icap copI divisors
    have eq := reciprocal_tuple_energy_eq_collision_count m k I
    have h : (∑ z : ZMod m, (fibres z).card^2) ≤ A^k*D^(2*k) := eq.trans_le bound
    exact_mod_cast h
  have coefBound (z : ZMod m) : ‖coef z‖ ≤ ((fibres z).card : ℝ)*W^k := by
    unfold coef
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ fibres z, W^k := by
        refine sum_le_sum fun a ha => ?_
        have hbase : a ∈ X := (mem_filter.mp ha).1
        rw [norm_prod]
        calc
          _ ≤ ∏ _ : Fin k, W := prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
            wBound _ (Fintype.mem_piFinset.mp hbase i)
          _ = W^k := by simp
      _ = _ := by simp
  have energyCoef : (∑ z : ZMod m, ‖coef z‖^2) ≤ (A : ℝ)^k*(D : ℝ)^(2*k)*W^(2*k) := by
    calc
      _ ≤ ∑ z : ZMod m, (((fibres z).card : ℝ)^2)*W^(2*k) := by
        refine sum_le_sum fun z _ => ?_
        calc
          _ ≤ (((fibres z).card : ℝ)*W^k)^2 := pow_le_pow_left₀ (norm_nonneg _) (coefBound z) 2
          _ = _ := by rw [mul_pow,← pow_mul,Nat.mul_comm k 2]
      _ = (∑ z : ZMod m, (((fibres z).card : ℝ)^2))*W^(2*k) := (sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right energy (pow_nonneg W0 _)
  change (∑ x : ZMod m, ‖H x‖^(2*k)) ≤ _
  calc
    _ = ∑ x : ZMod m, ‖∑ z : ZMod m, coef z*ZMod.stdAddChar (x*z)‖^2 := by
      refine sum_congr rfl fun x _ => ?_
      rw [← expand,norm_pow,← pow_mul,Nat.mul_comm k 2]
    _ = (m : ℝ)*(∑ z : ZMod m, ‖coef z‖^2) := cyclic_weighted_parseval coef
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left energyCoef (by positivity : (0 : ℝ) ≤ m)

end

end B13BoundedStepProductSavingProof

end

/- Rectangular frequency moment -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

def rectangularMomentEnvelope (r K : ℕ) (B : ℝ) : ℝ :=
  (((K : ℝ)^(r-1 : ℕ))*B)^(1/(r : ℝ) : ℝ)

theorem rectangular_moment_envelope_nonneg (r K : ℕ) {B : ℝ} (B0 : 0 ≤ B) :
    0 ≤ rectangularMomentEnvelope r K B := by unfold rectangularMomentEnvelope; positivity

theorem rectangular_moment_envelope_mono_card {r J K : ℕ} {B : ℝ}
    (B0 : 0 ≤ B) (leJK : J ≤ K) :
    rectangularMomentEnvelope r J B ≤ rectangularMomentEnvelope r K B := by
  unfold rectangularMomentEnvelope
  apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by exact_mod_cast leJK) _) B0

theorem norm_rectangular_frequency_sum_le_of_moment {p r : ℕ} [NeZero p] (r0 : 0 < r)
    (I : Finset ℕ) {ι : Type*} (J : Finset ι) (freq : ι → ZMod p) (injective : Set.InjOn freq J)
    (α : ℕ → ℂ) (β : ι → ℂ) {W V B : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (B0 : 0 ≤ B)
    (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (moment : (∑ x : ZMod p, ‖inverseFrequencySum p I α x‖^r) ≤ B*W^r) :
    ‖∑ j ∈ J, β j*inverseFrequencySum p I α (freq j)‖ ≤
      W*V*rectangularMomentEnvelope r J.card B := by
  let f (j : ι) := ‖inverseFrequencySum p I α (freq j)‖
  let D := ((J.card : ℝ)^(r-1 : ℕ))*B
  have D0 : 0 ≤ D := by unfold D; positivity
  have rR : 1 ≤ (r : ℝ) := by exact_mod_cast r0
  have rc : (((r-1 : ℕ) : ℝ)) = (r : ℝ)-1 := by
    rw [Nat.cast_sub r0, Nat.cast_one]
  have hsum : (∑ j ∈ J, f j)^r ≤ (J.card : ℝ)^(r-1 : ℕ)*(∑ j ∈ J, f j^r) := by
    have e := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg J (f := f) rR (fun _ _ => norm_nonneg _)
    rw [← rc] at e
    simpa only [Real.rpow_natCast] using e
  have complete : (∑ j ∈ J, f j^r) ≤ B*W^r := by
    calc
      _ = ∑ x ∈ J.image freq, ‖inverseFrequencySum p I α x‖^r := by
        rw [sum_image (fun x hx y hy h => injective hx hy h)]
      _ ≤ ∑ x : ZMod p, ‖inverseFrequencySum p I α x‖^r :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
      _ ≤ _ := moment
  have triangle : ‖∑ j ∈ J, β j*inverseFrequencySum p I α (freq j)‖ ≤ V*(∑ j ∈ J, f j) := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (bw j hj) (norm_nonneg _)
  have power : (D^(1/(r : ℝ) : ℝ))^r = D := by
    calc
      _ = (D^(1/(r : ℝ) : ℝ))^(r : ℝ) := (Real.rpow_natCast _ r).symm
      _ = _ := by
        rw [← Real.rpow_mul D0, one_div_mul_cancel (zero_lt_one.trans_le rR).ne',Real.rpow_one]
  change _ ≤ W*V*D^(1/(r : ℝ) : ℝ)
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) r0.ne').mp
  calc
    _ ≤ (V*(∑ j ∈ J, f j))^r := pow_le_pow_left₀ (norm_nonneg _) triangle r
    _ = V^r*(∑ j ∈ J, f j)^r := mul_pow _ _ _
    _ ≤ V^r*(((J.card : ℝ)^(r-1 : ℕ))*(B*W^r)) :=
      mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left complete (by positivity))) (by positivity)
    _ = (W*V*D^(1/(r : ℝ) : ℝ))^r := by
      rw [mul_pow,mul_pow,power]
      unfold D
      ring

end

end B13BoundedStepProductSavingProof

end

/- Gated frequency moment -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

private theorem moment_indicator_eq_interval_residue_count {p : ℕ} [NeZero p] {a b j : ℤ}
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

theorem norm_gated_frequency_sum_le_of_moment {p r S : ℕ} [NeZero p] (r0 : 0 < r)
    (Sp : S ≤ p) (I : Finset ℕ) (J : Finset ℤ) (Jrange : J ⊆ Ioc 0 (S : ℤ))
    (ψ : ℤ → ZMod p) (ψinj : Set.InjOn ψ J)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {W V B : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (B0 : 0 ≤ B)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ W) (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (moment : ∀ (weight : ℕ → ℂ) {X : ℝ}, 0 ≤ X → (∀ i ∈ I, ‖weight i‖ ≤ X) →
      (∑ x : ZMod p, ‖inverseFrequencySum p I weight x‖^r) ≤ B*X^r) :
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹))‖ ≤
      (2+Real.log p)*W*V*rectangularMomentEnvelope r J.card B := by
  let H := (univ : Finset (ZMod p)).filter (fun h => h ≠ 0)
  let a (i : ℕ) := max 0 (min (lo i) (S : ℤ))
  let b (i : ℕ) := max (a i) (min (hi i) (S : ℤ))
  let atZero (i : ℕ) : ℂ := ((b i-a i : ℤ) : ℂ)/(p : ℂ)
  let coeff (h : ZMod p) (i : ℕ) := intIntervalFourierCoefficient p (a i) (b i) h
  let βh (h : ZMod p) (j : ℤ) := β j*ZMod.stdAddChar (-(h*(j : ZMod p)))
  let G (h : ZMod p) := ∑ j ∈ J, βh h j*inverseFrequencySum p I (fun i => α i*coeff h i) (ψ j)
  let F := ∑ j ∈ J, β j*inverseFrequencySum p I (fun i => α i*atZero i) (ψ j)
  let Q := rectangularMomentEnvelope r J.card B
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
    rw [moment_indicator_eq_interval_residue_count (left0 i) (rightcap i) (jRange hj),
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
    refine norm_rectangular_frequency_sum_le_of_moment r0 I J ψ ψinj _ _ W0 V0 B0 bw
      (moment _ W0 ?_)
    intro i hiI
    rw [norm_mul]
    exact (mul_le_mul (aw i hiI) (az i) (norm_nonneg _) W0).trans_eq (mul_one _)
  have gLe (h : ZMod p) (hh : h ∈ H) : ‖G h‖ ≤ d h*(W*V*Q) := by
    have h0 := (mem_filter.mp hh).2
    have d0 : 0 ≤ d h := by unfold d; positivity
    have est := norm_rectangular_frequency_sum_le_of_moment r0 I J ψ ψinj
      (fun i => α i*coeff h i) (βh h) (mul_nonneg W0 d0) V0 B0
      (by
        intro j hj
        rw [show ‖βh h j‖ = ‖β j‖ by simp [βh]]
        exact bw j hj)
      (moment _ (mul_nonneg W0 d0) (by
        intro i hiI
        rw [norm_mul]
        exact mul_le_mul (aw i hiI) (norm_int_interval_fourier_coefficient_le p (a i) (b i) h0)
          (norm_nonneg _) W0))
    change ‖G h‖ ≤ (W*d h)*V*Q at est
    exact est.trans_eq (by ring)
  rw [exactSum]
  have Q0 : 0 ≤ Q := rectangular_moment_envelope_nonneg r J.card B0
  calc
    _ ≤ ‖F‖+‖∑ h ∈ H, G h‖ := norm_add_le _ _
    _ ≤ W*V*Q+∑ h ∈ H, d h*(W*V*Q) :=
      (add_le_add) fLe ((norm_sum_le _ _).trans (sum_le_sum gLe))
    _ ≤ W*V*Q+(1+Real.log p)*(W*V*Q) := by
      rw [← sum_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (sum_inv_min_val_le p) (by positivity))
    _ = _ := by unfold Q; ring

theorem norm_gated_translated_frequency_sum_le_of_moment {p r S : ℕ} [NeZero p] (r0 : 0 < r)
    (Sp : S ≤ p) (L : ℤ) (I : Finset ℕ) (J : Finset ℤ) (Jrange : J ⊆ Ioc L (L+(S : ℤ)))
    (ψ : ℤ → ZMod p) (ψinj : Set.InjOn ψ J)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {W V B : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (B0 : 0 ≤ B)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ W) (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (moment : ∀ (weight : ℕ → ℂ) {X : ℝ}, 0 ≤ X → (∀ i ∈ I, ‖weight i‖ ≤ X) →
      (∑ x : ZMod p, ‖inverseFrequencySum p I weight x‖^r) ≤ B*X^r) :
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹))‖ ≤
      (2+Real.log p)*W*V*rectangularMomentEnvelope r J.card B := by
  let shift (j : ℤ) := j-L
  let unshift (j : ℤ) := j+L
  let K := J.image shift
  have identity (j : ℤ) : unshift (shift j) = j := by dsimp only [shift,unshift]; omega
  have unshift_mem {j : ℤ} (hj : j ∈ K) : unshift j ∈ J := by
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hj
    simpa only [identity] using ht
  have shift_inj : Function.Injective shift := by
    intro x y eq
    change x-L=y-L at eq
    omega
  have Kspan : K ⊆ Ioc (0 : ℤ) (S : ℤ) := by
    intro j hj
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hj
    have tr := mem_Ioc.mp (Jrange ht)
    exact mem_Ioc.mpr ⟨by unfold shift; omega,by unfold shift; omega⟩
  have inj : Set.InjOn (ψ ∘ unshift) K := by
    intro a ha b hb eq
    have same := ψinj (unshift_mem ha) (unshift_mem hb) eq
    change a+L=b+L at same
    omega
  have wt (j : ℤ) (hj : j ∈ K) : ‖(β ∘ unshift) j‖ ≤ V := bw _ (unshift_mem hj)
  have est := norm_gated_frequency_sum_le_of_moment r0 Sp I K Kspan (ψ ∘ unshift) inj
    α (β ∘ unshift) (fun i => lo i-L) (fun i => hi i-L) W0 V0 B0 aw wt moment
  have eq : gatedBilinearSum I K α (β ∘ unshift) (fun i => lo i-L) (fun i => hi i-L)
      (fun i j => ZMod.stdAddChar ((ψ ∘ unshift) j*(i : ZMod p)⁻¹)) =
      gatedBilinearSum I J α β lo hi (fun i j => ZMod.stdAddChar (ψ j*(i : ZMod p)⁻¹)) := by
    unfold gatedBilinearSum K
    rw [sum_image (fun a _ b _ h => shift_inj h)]
    refine sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply,identity]
    apply congrArg (β j * ·)
    refine sum_congr rfl fun i _ => ?_
    have shifted : lo i-L < shift j ∧ shift j ≤ hi i-L ↔ lo i < j ∧ j ≤ hi i := by
      unfold shift
      omega
    simp only [shifted]
  rw [eq, show K.card = J.card from card_image_of_injective J shift_inj] at est
  exact est

theorem norm_gated_inverse_on_reduced_span_of_moment {m r S : ℕ} [NeZero m]
    (r0 : 0 < r) (c : ZMod m) (cap : S ≤ inverseFrequencyPeriod m c)
    (L : ℤ) (I : Finset ℕ) (J : Finset ℤ) (Jrange : J ⊆ Ioc L (L+(S : ℤ)))
    (units : ∀ j ∈ J, IsUnit (j : ZMod m))
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ)
    {W V B : ℝ} (W0 : 0 ≤ W) (V0 : 0 ≤ V) (B0 : 0 ≤ B)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ W) (bw : ∀ j ∈ J, ‖β j‖ ≤ V)
    (moment : ∀ (weight : ℕ → ℂ) {X : ℝ}, 0 ≤ X → (∀ i ∈ I, ‖weight i‖ ≤ X) →
      (∑ x : ZMod m, ‖inverseFrequencySum m I weight x‖^r) ≤ B*X^r) :
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar (c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹))‖ ≤
      (2+Real.log m)*W*V*rectangularMomentEnvelope r J.card B := by
  let ψ (j : ℤ) := c*(j : ZMod m)⁻¹
  have inj : Set.InjOn ψ J := unit_inverse_frequency_injOn_interval c L cap J Jrange units
  have Sm : S ≤ m := cap.trans (Nat.div_le_self _ _)
  have phase (i : ℕ) (j : ℤ) : c*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹ = ψ j*(i : ZMod m)⁻¹ := by
    unfold ψ
    ring
  simp only [phase]
  exact norm_gated_translated_frequency_sum_le_of_moment r0 Sm L I J Jrange ψ inj α β lo hi W0 V0 B0 aw bw moment

end

end B13BoundedStepProductSavingProof

end

/- Sixth moment expanded budget -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

theorem sixth_moment_expanded_envelope_le {n m g A S : ℕ} {x T : ℝ}
    (n1 : 1 ≤ (n : ℝ)) (m1 : 1 ≤ (m : ℝ)) (g1 : 1 ≤ (g : ℝ)) (T0 : 0 ≤ T)
    (xLo : 31/512 ≤ x) (mHi : (m : ℝ) ≤ (n : ℝ)^(133/256 : ℝ))
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+3/512))
    (sCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512-x)) :
    rectangularMomentEnvelope 6 S ((m : ℝ)*(A : ℝ)^3*T^6) ≤
      2*(n : ℝ)^(1015/1024 : ℝ)*T/((m : ℝ)*(g : ℝ)^(3/2 : ℝ)) := by
  let N := (n : ℝ)
  let M := (m : ℝ)
  let G := (g : ℝ)
  let V := (S : ℝ)
  let C := (A : ℝ)
  let Y := V*M*G^2
  let H := N^(1015/1024 : ℝ)
  let Q := rectangularMomentEnvelope 6 S (M*C^3*T^6)
  have np : 0 < N := zero_lt_one.trans_le n1
  have mp := zero_lt_one.trans_le m1
  have gp := zero_lt_one.trans_le g1
  have C0 : 0 ≤ C := by unfold C; positivity
  have V0 : 0 ≤ V := by unfold V; positivity
  have Q0 : 0 ≤ Q := rectangular_moment_envelope_nonneg _ _ (by positivity)
  have formula : Q*(M*G^(5/3 : ℝ)) = Y^(5/6 : ℝ)*M^(1/3 : ℝ)*C^(1/2 : ℝ)*T := by
    change ((V^5*(M*C^3*T^6))^(1/6 : ℝ))*(M*G^(5/3 : ℝ)) = _
    rw [Real.mul_rpow (by positivity : 0 ≤ V^5) (by positivity : 0 ≤ M*C^3*T^6),
      Real.mul_rpow (by positivity : 0 ≤ M*C^3) (by positivity : 0 ≤ T^6),
      Real.mul_rpow mp.le (by positivity : 0 ≤ C^3)]
    rw [← Real.rpow_natCast_mul V0 5, ← Real.rpow_natCast_mul C0 3, ← Real.rpow_natCast_mul T0 6]
    norm_num only [show ((5 : ℕ) : ℝ)*(1/6 : ℝ) = 5/6 by norm_num,
      show ((3 : ℕ) : ℝ)*(1/6 : ℝ) = 1/2 by norm_num,
      show ((6 : ℕ) : ℝ)*(1/6 : ℝ) = 1 by norm_num, Real.rpow_one]
    unfold Y
    rw [Real.mul_rpow (by positivity : 0 ≤ V*M) (by positivity : 0 ≤ G^2),
      Real.mul_rpow V0 mp.le,← Real.rpow_natCast_mul gp.le]
    have merge : M^(5/6 : ℝ)*M^(1/3 : ℝ) = M^(1/6 : ℝ)*M := by
      rw [← Real.rpow_add mp]
      nth_rw 2 [← Real.rpow_one M]
      rw [← Real.rpow_add mp]
      congr 1
      norm_num
    have eg : ((2 : ℕ) : ℝ)*(5/6 : ℝ) = 5/3 := by norm_num
    rw [eg]
    calc
      _ = V^(5/6 : ℝ)*(M^(1/6 : ℝ)*M)*G^(5/3 : ℝ)*C^(1/2 : ℝ)*T := by ring
      _ = _ := by rw [← merge]; ring
  have yLimit : Y^(5/6 : ℝ) ≤ 2*N^((513/512-x)*(5/6)) := by
    calc
      _ ≤ (2*N^(513/512-x))^(5/6 : ℝ) := Real.rpow_le_rpow (by positivity) sCap (by norm_num)
      _ = (2 : ℝ)^(5/6 : ℝ)*N^((513/512-x)*(5/6)) := by rw [Real.mul_rpow (by norm_num) (by positivity),Real.rpow_mul np.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by positivity)
  have mLimit : M^(1/3 : ℝ) ≤ N^((133/256 : ℝ)*(1/3)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow mp.le mHi (by norm_num)
  have cLimit : C^(1/2 : ℝ) ≤ N^((x+3/512)*(1/2)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow C0 aCap (by norm_num)
  have bound : Q*(M*G^(5/3 : ℝ)) ≤ 2*H*T := by
    rw [formula]
    calc
      _ ≤ (2*N^((513/512-x)*(5/6)))*N^((133/256 : ℝ)*(1/3))*N^((x+3/512)*(1/2))*T := by gcongr
      _ = 2*N^((513/512-x)*(5/6)+(133/256)*(1/3)+(x+3/512)*(1/2))*T := by
        rw [Real.rpow_add np,Real.rpow_add np]
        ring
      _ ≤ _ := by
        have exp : N^((513/512-x)*(5/6)+(133/256)*(1/3)+(x+3/512)*(1/2)) ≤ H :=
          Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo])
        gcongr
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < M*G^(3/2 : ℝ))).mpr
  have gCmp : G^(3/2 : ℝ) ≤ G^(5/3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le g1 (by norm_num)
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left gCmp mp.le) Q0).trans bound

end

end B13BoundedStepProductSavingProof

end

/- Sixth moment expanded fixed residue -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

theorem norm_gated_sixth_moment_expanded_fixed_endpoints_le {n m g A S : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/128 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (large : (2 : ℝ) ≤ (n : ℝ)^(1/64 : ℝ))
    (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(133/256 : ℝ)) (mLo : (n : ℝ)^(255/512 : ℝ) ≤ (m : ℝ))
    (xLo : 31/512 ≤ x) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+3/512))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512-x))
    (small : 6*A^5 < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ) {a b : ℤ} (ab : a ≤ b)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ T) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T*L)
    (divisors : ∀ z ≤ max m (A^3), (z.divisors.card : ℝ) ≤ T) :
    ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun i j => centeredIntIntervalResidue m a b (c*((i : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      6*(n : ℝ)^(1015/1024 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)^(3/2 : ℝ)) := by
  let N := (n : ℝ)
  let M := (m : ℝ)
  let G := (g : ℝ)
  let H := N^(1015/1024 : ℝ)
  let D := ⌊N^(1/32 : ℝ)⌋₊
  let B := 4*H*T^3*L^2/(M*G^(3/2 : ℝ))
  let J := intIntervalModUnits m 0 S
  have np : 0 < N := zero_lt_one.trans_le n1
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have m1 : 1 ≤ M := show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast m0
  have mp : 0 < M := zero_lt_one.trans_le m1
  have gp : 0 < G := zero_lt_one.trans_le g1
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans L1
  have log0 := Real.log_nonneg m1
  have log2 : 2+Real.log (m : ℝ) ≤ 2*L := by linarith only [L1,logBound]
  have B0 : 0 ≤ B := by unfold B H; positivity
  have jProp (j : ℤ) (hj : j ∈ J) : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hj
  have uniform (h : ZMod m) (_ : h ≠ 0) (good : m.gcd h.val ≤ D) :
      ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar ((-(h*c))*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹))‖ ≤ B := by
    let z := -(h*c)
    let q := m.gcd z.val
    let p := inverseFrequencyPeriod m z
    have product : p*q=m := Nat.div_mul_cancel (Nat.gcd_dvd_left m z.val)
    have p0 : 0 < p := inverse_frequency_period_pos z
    have pr : (0 : ℝ) < p := by exact_mod_cast p0
    have a : (m.gcd h.val : ℝ) ≤ N^(1/32 : ℝ) :=
      (by exact_mod_cast good : (m.gcd h.val : ℝ) ≤ (D : ℝ)).trans (Nat.floor_le (by positivity))
    have qCap : (q : ℝ) ≤ N^(5/128 : ℝ) := calc
      _ ≤ (m.gcd h.val : ℝ)*(m.gcd c.val : ℝ) := by
        change (m.gcd (-(h*c)).val : ℝ) ≤ _
        exact_mod_cast gcd_fourier_phase_product_le h c
      _ ≤ N^(1/32 : ℝ)*N^(1/128 : ℝ) := mul_le_mul a charBound (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add np]; norm_num
    have q0 := Nat.gcd_pos_of_pos_left z.val m0
    have per : S ≤ p := by
      have G1 : 1 ≤ G^2 := one_le_pow₀ g1
      have scaled : ((S : ℝ)*(q : ℝ))*(M*G^2) ≤ M*(M*G^2) := calc
        _ = ((S : ℝ)*M*G^2)*(q : ℝ) := by ring
        _ ≤ (2*N^(513/512-x))*N^(5/128 : ℝ) := mul_le_mul cofactorCap qCap (by positivity) (by positivity)
        _ ≤ (N^(1/64 : ℝ)*N^(513/512-x))*N^(5/128 : ℝ) := by gcongr
        _ = N^(513/512-x+5/128+1/64) := by
          rw [Real.rpow_add np,Real.rpow_add np]
          ring
        _ ≤ N^(255/256 : ℝ) := Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo])
        _ = N^(255/512 : ℝ)*N^(255/512 : ℝ) := by rw [← Real.rpow_add np]; norm_num
        _ ≤ M*M := mul_le_mul mLo mLo (by positivity) mp.le
        _ ≤ _ := by
          have b := mul_le_mul_of_nonneg_left G1 (by positivity : 0 ≤ M*M)
          simpa only [mul_one,mul_assoc] using b
      have goodSq : (S : ℝ)*(q : ℝ) ≤ M := (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < M*G^2)).mp scaled
      have nat : S*q ≤ m := by
        change (S : ℝ)*(q : ℝ) ≤ (m : ℝ) at goodSq
        exact_mod_cast goodSq
      rw [← product] at nat
      exact Nat.le_of_mul_le_mul_right nat q0
    let K := M*(A : ℝ)^3*T^6
    have K0 : 0 ≤ K := by unfold K; positivity
    have dTop : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le T0
    have evenMoment (weight : ℕ → ℂ) {X : ℝ} (X0 : 0 ≤ X) (xw : ∀ i ∈ I, ‖weight i‖ ≤ X) :
        (∑ x : ZMod m, ‖inverseFrequencySum m I weight x‖^6) ≤ K*X^6 := by
      have use := inverse_frequency_even_moment_small_le (k := 3) (D := ⌊T⌋₊)
        (show 2*3*A^(2*3-1) < m from small) I Icap copI
        (fun y hy => Nat.le_floor (divisors y (hy.trans (le_max_right _ _)))) weight X0 xw
      refine use.trans ?_
      unfold K M
      gcongr
    have est := norm_gated_inverse_on_reduced_span_of_moment (r := 6) (by decide) z
      (show S ≤ inverseFrequencyPeriod m z from per) 0 I J
      (fun j hj => by simpa only [zero_add] using (jProp j hj).1)
      (fun j hj => (jProp j hj).2) α β lo hi T0 (mul_nonneg T0 L0) K0 aw bw evenMoment
    have size : J.card ≤ S :=
      (card_le_card (fun j hj => (jProp j hj).1)).trans_eq (by rw [Int.card_Ioc,sub_zero,Int.toNat_natCast])
    calc
      _ ≤ (2+Real.log m)*T*(T*L)*rectangularMomentEnvelope 6 J.card K := est
      _ ≤ (2*L)*T*(T*L)*rectangularMomentEnvelope 6 S K :=
        mul_le_mul (by gcongr) (rectangular_moment_envelope_mono_card K0 size)
          (rectangular_moment_envelope_nonneg _ _ K0) (by positivity)
      _ ≤ (2*L)*T*(T*L)*(2*H*T/(M*G^(3/2 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (sixth_moment_expanded_envelope_le n1 m1 g1 T0 xLo mHi aCap cofactorCap)
        positivity
      _ = B := by unfold B; ring
  have est := norm_gated_unit_residue_of_divisor_frequency_bound D I (fun i => (i : ZMod m))
    (fun i hi => (ZMod.isUnit_iff_coprime _ _).mpr (copI i hi)) α β lo hi
    (L := 0) (R := (S : ℤ)) ab B0 uniform
  have lMass : (∑ i ∈ I, ‖α i‖) ≤ (A : ℝ)*T := calc
    _ ≤ ∑ _ ∈ I, T := sum_le_sum aw
    _ = (I.card : ℝ)*T := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (card_le_card Icap).trans_eq (by simp [Nat.card_Icc])) T0
  have jSub : J ⊆ Ioc (0 : ℤ) (S : ℤ) := fun j hj => (jProp j hj).1
  have jSize : (J.card : ℝ) ≤ S := by
    exact_mod_cast (card_le_card jSub).trans_eq (by rw [Int.card_Ioc,sub_zero,Int.toNat_natCast])
  have rMass : (∑ j ∈ J, ‖β j‖) ≤ (S : ℝ)*(T*L) := calc
    _ ≤ ∑ _ ∈ J, T*L := sum_le_sum bw
    _ = (J.card : ℝ)*(T*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right jSize (by positivity)
  have div_m : (m.divisors.card : ℝ) ≤ T := divisors m (le_max_left _ _)
  have divisorFactor : (m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1) ≤ T*L/N^(1/32 : ℝ) := by
    have d : N^(1/32 : ℝ) ≤ (D : ℝ)+1 := (Nat.lt_floor_add_one (N^(1/32 : ℝ))).le
    calc
      _ ≤ T*L/((D : ℝ)+1) := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) d
  have core : (A : ℝ)*(S : ℝ) ≤ 2*N^(513/512+3/512 : ℝ)/(M*G^2) := by
    apply (le_div_iff₀ (by positivity : 0 < M*G^2)).mpr
    calc
      _ = (A : ℝ)*((S : ℝ)*M*G^2) := by ring
      _ ≤ N^(x+3/512)*(2*N^(513/512-x)) := mul_le_mul aCap cofactorCap (by positivity) (by positivity)
      _ = _ := by
        have sum : N^(x+3/512)*N^(513/512-x) = N^(513/512+3/512 : ℝ) := by rw [← Real.rpow_add np]; congr 1; ring
        calc
          _ = 2*(N^(x+3/512)*N^(513/512-x)) := by ring
          _ = _ := by rw [sum]
  have gpow : G^(3/2 : ℝ) ≤ G^2 := by
    rw [← Real.rpow_natCast G 2]
    exact Real.rpow_le_rpow_of_exponent_le g1 (by norm_num)
  have tail : ((m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1))*
       ((∑ i ∈ I, ‖α i‖)*(∑ j ∈ J, ‖β j‖)) ≤ 2*H*T^3*L^3/(M*G^(3/2 : ℝ)) := by
    calc
      _ ≤ (T*L/N^(1/32 : ℝ))*(((A : ℝ)*T)*((S : ℝ)*(T*L))) := by gcongr
      _ = (T*L/N^(1/32 : ℝ))*(((A : ℝ)*(S : ℝ))*T^2*L) := by ring
      _ ≤ (T*L/N^(1/32 : ℝ))*((2*N^(513/512+3/512 : ℝ)/(M*G^2))*T^2*L) := by gcongr
      _ = 2*N^(500/512 : ℝ)*T^3*L^2/(M*G^2) := by
        have pow : N^(513/512+3/512 : ℝ)/N^(1/32 : ℝ)=N^(500/512 : ℝ) := by rw [← Real.rpow_sub np]; norm_num
        rw [← pow]
        ring
      _ ≤ _ := by
        have h : N^(500/512 : ℝ) ≤ H := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        have l : L^2 ≤ L^3 := pow_le_pow_right₀ L1 (by decide)
        gcongr
  exact est.trans ((add_le_add (mul_le_mul_of_nonneg_right logBound B0) tail).trans_eq (by unfold B H; ring))

end

end B13BoundedStepProductSavingProof

end

/- Sixth moment expanded ratio hyperbola -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

set_option maxHeartbeats 1500000 in
theorem norm_sixth_moment_expanded_ratio_hyperbola_le {n m g A S num l r : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/128 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (large : (2 : ℝ) ≤ (n : ℝ)^(1/64 : ℝ))
    (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(133/256 : ℝ))
    (mLo : (n : ℝ)^(255/512 : ℝ) ≤ (m : ℝ))
    (gCap : (g : ℝ) ≤ (n : ℝ)^(1/512 : ℝ))
    (xLo : 31/512 ≤ x) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+3/512))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512-x))
    (rCap : (r : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512 : ℝ))
    (endCap : num/(l+1) ≤ ⌊(m : ℝ)*(g : ℝ)*(n : ℝ)^(1/256 : ℝ)⌋₊)
    (small : 6*A^5 < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ)
    (aw : ∀ a ∈ I, ‖α a‖ ≤ T) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T*L)
    (divisors : ∀ z ≤ max m (A^3), (z.divisors.card : ℝ) ≤ T)
    (dR : ∀ z ≤ r, (z.divisors.card : ℝ) ≤ T) :
    let J := intIntervalModUnits m 0 S
    let lo (a : ℕ) : ℤ := (l/a : ℕ)
    let hi (a : ℕ) : ℤ := (r/a : ℕ)
    ‖gatedBilinearSum I J α β lo hi
        (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
          (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      592*(n : ℝ)^(1023/1024 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)) := by
  dsimp only
  let P := (m : ℝ)
  let N := (n : ℝ)
  let G := (g : ℝ)
  let C := G^(1/2 : ℝ)
  let H := N^(1023/1024 : ℝ)
  let J := intIntervalModUnits m 0 S
  let lo (a : ℕ) : ℤ := (l/a : ℕ)
  let hi (a : ℕ) : ℤ := (r/a : ℕ)
  let R := 98*N^(1015/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ))
  let d := ⌊P*N^(-3/1024 : ℝ)⌋₊
  let cap := ⌊P*G*N^(1/256 : ℝ)⌋₊
  have m1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have pp : 0 < P := zero_lt_one.trans_le m1
  have np : 0 < N := zero_lt_one.trans_le n1
  have gp : 0 < G := zero_lt_one.trans_le g1
  have cp : 0 < C := by unfold C; positivity
  have t0 := zero_le_one.trans T1
  have l0 := zero_le_one.trans L1
  have log0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg m1
  have R0 : 0 ≤ R := by unfold R; positivity
  have bound : R ≤ 98*N^(1015/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ)) := le_rfl
  have mThird : N^(1/3 : ℝ) ≤ P :=
    (Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : (1/3 : ℝ) ≤ 255/512)).trans mLo
  obtain ⟨d0,dcount,dsmall⟩ := expanded_hyperbola_endpoint_bucket_budget n1 g1 mThird
  have rUp : (r : ℝ) ≤ 2*N^(513/512 : ℝ)/(P*G^2) := (le_div_iff₀ (by positivity)).mpr (by
    have h := rCap
    change (r : ℝ)*P*G^2 ≤ 2*N^(513/512 : ℝ) at h
    convert h using 1
    ring)
  have jPos (j : ℤ) (hj : j ∈ J) : 0 < j := by
    have data : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    exact (mem_Ioc.mp data.1).1
  let mass := ∑ j ∈ J, ‖β j‖*∑ a ∈ I, if lo a < j ∧ j ≤ hi a then ‖α a‖ else 0
  have mass0 : 0 ≤ mass := by
    unfold mass
    exact sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (sum_nonneg fun a _ => by split_ifs <;> positivity)
  have massCut : mass ≤ (2*N^(513/512 : ℝ)/(P*G^2))*T^3*L := by
    have b := gated_left_weight_mass_le α β lo hi t0 (mul_nonneg t0 l0)
      (fun u hu => dR u (mem_Icc.mp hu).2) (fun a ha => (mem_Icc.mp (Icap ha)).1)
      (fun j hj => (jPos j hj).le) (fun a ha j hj active => ?_) aw bw
    · refine b.trans ?_
      calc
        _ ≤ (2*N^(513/512 : ℝ)/(P*G^2))*T*T*(T*L) := by gcongr
        _ = _ := by ring
    · have ja : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (jPos j hj).le
      have jR : j.toNat ≤ r/a := by
        have h : (j.toNat : ℤ) ≤ ((r/a : ℕ) : ℤ) := by rw [ja]; exact active.2
        exact_mod_cast h
      have ap := (mem_Icc.mp (Icap ha)).1
      have jn : 0 < j.toNat := by have := jPos j hj; omega
      exact mem_Icc.mpr ⟨mul_pos ap jn,by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ap).mp jR⟩
  have est : ‖gatedBilinearSum I J α β lo hi
      (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
        (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
          ((cap/d+1 : ℕ) : ℝ)*(2*R)+(2*((d : ℝ)/P))*mass := by
    let phase (a : ℕ) (j : ℤ) := c*((a : ZMod m)*(j : ZMod m))⁻¹
    let e (a : ℕ) (j : ℤ) := (num : ℤ)/((a*j.toNat : ℕ) : ℤ)
    rw [gated_bilinear_sum_eq_pair_sum]
    refine norm_product_interval_le_of_ratio_window (num := num) (p := m) I J α β _ (fun a ha => (mem_Icc.mp (Icap ha)).1)
      jPos d0 endCap ?_
    intro u v b t vb bt bracket
    rw [← gated_bilinear_sum_eq_pair_sum]
    refine norm_gated_residue_variable_endpoint_le m I J α β u v vb bt phase e
      (fun a ha j hj gate => (bracket a ha j hj gate).2) ?_ ?_
    · refine (norm_gated_sixth_moment_expanded_fixed_endpoints_le charBound n1 large g1 T1 L1 mHi mLo xLo
        logBound aCap cofactorCap small I Icap copI α β u v vb aw bw divisors).trans ?_
      unfold R P G N
      gcongr <;> norm_num
    · refine (norm_gated_sixth_moment_expanded_fixed_endpoints_le charBound n1 large g1 T1 L1 mHi mLo xLo
        logBound aCap cofactorCap small I Icap copI _ _ u v bt ?_ ?_ divisors).trans ?_
      · intro a ha
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (α a))] using aw a ha
      · intro j hj
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (β j))] using bw j hj
      · unfold R P G N
        gcongr <;> norm_num
  have e1 : ((cap/d+1 : ℕ) : ℝ)*(2*R) ≤ 588*H*T^3*L^3/(P*G) := by
    have Ghalf : G^(3/2 : ℝ) = G*C := by
      unfold C
      rw [mul_comm G,← Real.rpow_add_one gp.ne']
      norm_num
    have CC : C^2 = G := by unfold C; rw [← Real.rpow_mul_natCast gp.le]; norm_num
    have cpow : C ≤ N^(1/1024 : ℝ) := by
      have b := Real.rpow_le_rpow gp.le gCap (by norm_num : (0 : ℝ) ≤ 1/2)
      rw [← Real.rpow_mul np.le] at b
      norm_num at b ⊢
      exact b
    calc
      _ ≤ (3*G*N^(7/1024 : ℝ))*(2*(98*N^(1015/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ)))) := by gcongr
      _ = 588*N^(511/512 : ℝ)*T^3*L^3*C/(P*G) := by
        have add : N^(7/1024 : ℝ)*N^(1015/1024 : ℝ) = N^(511/512 : ℝ) := by
          rw [← Real.rpow_add np]
          norm_num
        calc
          _ = 588*(N^(7/1024 : ℝ)*N^(1015/1024 : ℝ))*T^3*L^3*G/(P*G^(3/2 : ℝ)) := by ring
          _ = _ := by
            have frac : G/(P*(G*C)) = C/(P*G) := by
              rw [← CC]
              field_simp [pp.ne',cp.ne']
            rw [add,Ghalf]
            calc
              _ = (588*N^(511/512 : ℝ)*T^3*L^3)*(G/(P*(G*C))) := by ring
              _ = _ := by rw [frac]; ring
      _ ≤ 588*N^(511/512 : ℝ)*T^3*L^3*N^(1/1024 : ℝ)/(P*G) := by gcongr
      _ = _ := by
        have add : N^(511/512 : ℝ)*N^(1/1024 : ℝ) = H := by
          unfold H
          rw [← Real.rpow_add np]
          norm_num
        calc
          _ = 588*(N^(511/512 : ℝ)*N^(1/1024 : ℝ))*T^3*L^3/(P*G) := by ring
          _ = _ := by rw [add]
  have e2 : (2*((d : ℝ)/P))*mass ≤ 4*H*T^3*L^3/(P*G) := by
    have lg : L ≤ L^3 := by simpa only [pow_one] using pow_le_pow_right₀ L1 (show 1 ≤ 3 by decide)
    have pow : N^(-3/1024 : ℝ)*N^(513/512 : ℝ) = H := by unfold H; rw [← Real.rpow_add np]; norm_num
    calc
      _ ≤ (2*N^(-3/1024 : ℝ))*((2*N^(513/512 : ℝ)/(P*G^2))*T^3*L) := by gcongr
      _ = 4*H*T^3*L/(P*G^2) := by
        calc
          _ = 4*(N^(-3/1024 : ℝ)*N^(513/512 : ℝ))*T^3*L/(P*G^2) := by ring
          _ = _ := by rw [pow]
      _ ≤ 4*H*T^3*L^3/(P*G^2) := by gcongr
      _ ≤ _ := by
        have gPow : G ≤ G^2 := by simpa only [pow_one] using pow_le_pow_right₀ g1 (show 1 ≤ 2 by decide)
        gcongr
  exact est.trans ((add_le_add e1 e2).trans_eq (by ring))

end

end B13BoundedStepProductSavingProof

end

/- Swapped capped residue endpoints -/
section

namespace B13BoundedStepProductSavingProof

open scoped Classical

noncomputable section

theorem swapped_capped_coprime_residue_two_prefixes {n u v b : ℕ} [NeZero u]
    (u0 : 0 < u) (uv : u < v) (un : u ≤ n) (cop : v.Coprime u) :
    let F (t : ℤ) := centeredIntIntervalResidue u 0 t ((n : ZMod u)*(v : ZMod u)⁻¹)
    let a := (n-u)/v
    (pairResidueError n v u b (n/v) 0 (n/u) : ℂ) =
      if b ≤ a then F (a : ℤ)-F (b : ℤ) else 0 := by
  dsimp only
  let a := (n-u)/v
  let z := (n : ZMod u)*(v : ZMod u)⁻¹
  have v0 : 0 < v := u0.trans uv
  have vZ : (0 : ℤ) < v := by exact_mod_cast v0
  have rem : (n : ℤ)-(u : ℤ)*(n/u : ℕ) = (n % u : ℕ) := by
    have h : ((n % u : ℕ) : ℤ)+(u : ℤ)*(n/u : ℕ) = (n : ℤ) := by exact_mod_cast Nat.mod_add_div n u
    linarith only [h]
  have lower : pairLeftLower n v u b (n/u) = b := by
    unfold pairLeftLower
    rw [rem]
    refine max_eq_left (le_trans ?_ (by positivity : (0 : ℤ) ≤ b))
    apply Int.lt_add_one_iff.mp
    rw [zero_add,Int.ediv_lt_iff_lt_mul vZ,one_mul]
    have rlo : (n % u : ℤ) < (v : ℤ) := by exact_mod_cast (Nat.mod_lt n u0).trans uv
    omega
  have upper : pairLeftUpper n v u (n/v) 0 = (a : ℤ) := by
    unfold pairLeftUpper a
    simp only [Nat.cast_zero,zero_add,mul_one]
    rw [← Int.ofNat_sub un,← Int.natCast_ediv, min_eq_right]
    exact_mod_cast Nat.div_le_div_right (Nat.sub_le n u)
  have b0 : 0 ≤ (b : ℤ) := by positivity
  by_cases order : b ≤ a
  · have active : pairLeftLower n v u b (n/u) ≤ pairLeftUpper n v u (n/v) 0 := by
      rw [lower,upper]
      exact_mod_cast order
    rw [ite_eq_left order,pair_residue_error_eq_centered_of_coprime cop active,lower,upper]
    change centeredIntIntervalResidue u (b : ℤ) (a : ℤ) z =
      centeredIntIntervalResidue u 0 (a : ℤ) z-centeredIntIntervalResidue u 0 (b : ℤ) z
    unfold centeredIntIntervalResidue
    rw [int_interval_residue_count_add u b0 (by exact_mod_cast order)]
    push_cast
    ring
  · have inactive : ¬pairLeftLower n v u b (n/u) ≤ pairLeftUpper n v u (n/v) 0 := by
      rw [lower,upper]
      exact_mod_cast order
    have order' : ¬b ≤ (n-u)/v := order
    simp [pairResidueError,cop.gcd_eq_one,order',inactive]

theorem swapped_capped_residue_two_prefixes {n u v b : ℕ}
    (u0 : 0 < u) (uv : u < v) (un : u ≤ n) (gn : v.gcd u ∣ n) :
    let g := v.gcd u
    let N := n/g
    let U := u/g
    let V := v/g
    let F (t : ℤ) := centeredIntIntervalResidue U 0 t ((N : ZMod U)*(V : ZMod U)⁻¹)
    let a := (N-U)/V
    (pairResidueError n v u b (n/v) 0 (n/u) : ℂ) =
      if b ≤ a then F (a : ℤ)-F (b : ℤ) else 0 := by
  dsimp only
  let g := v.gcd u
  let N := n/g
  let U := u/g
  let V := v/g
  have v0 := u0.trans uv
  have g0 : 0 < g := Nat.gcd_pos_of_pos_right v u0
  have gu : g ∣ u := Nat.gcd_dvd_right v u
  have gv : g ∣ v := Nat.gcd_dvd_left v u
  have up : 0 < U := Nat.div_pos (Nat.le_of_dvd u0 gu) g0
  let _ : NeZero U := ⟨up.ne'⟩
  have order : U < V := by
    by_contra! h
    have p := Nat.mul_le_mul_right g h
    change (v/g)*g ≤ (u/g)*g at p
    rw [Nat.div_mul_cancel gv,Nat.div_mul_cancel gu] at p
    exact (not_le_of_gt uv) p
  have uq : N/U=n/u := by
    unfold N U
    rw [Nat.div_div_eq_div_mul,Nat.mul_div_cancel' gu]
  have vq : N/V=n/v := by
    unfold N V
    rw [Nat.div_div_eq_div_mul,Nat.mul_div_cancel' gv]
  have h := pair_residue_error_eq_div_gcd (l := b) (r := n/v) (p := 0) (s := n/u) v0 u0 gn
  dsimp only at h
  rw [h]
  change (pairResidueError N V U b (n/v) 0 (n/u) : ℂ) = _
  rw [← uq,← vq]
  exact swapped_capped_coprime_residue_two_prefixes up order (Nat.div_le_div_right un)
    (Nat.coprime_div_gcd_div_gcd g0)

end

end B13BoundedStepProductSavingProof

end

/- Right low above root -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical

noncomputable section

theorem right_low_full_upper_of_root_le {n : ℕ} {j : RightLowWaveIndex}
    (hj : j ∈ rightLowWaveItems n) (high : n ≤ (rightLowWaveStep j)^2) :
    rightLowWaveUpper n j = n/rightLowWaveStep j := by
  let N := (n : ℝ)
  let D := (j.2 : ℝ)
  let P := (j.1 : ℝ)
  have step := mem_Icc.mp (bilateral_right_low_step_range hj)
  have n0 : 0 < n := step.1.trans step.2
  have n1 : 1 ≤ N := by change (1 : ℝ) ≤ (n : ℝ); exact_mod_cast n0
  have np : 0 < N := zero_lt_one.trans_le n1
  have core := mem_sigma.mp hj
  have p0 : 0 < P := by
    change (0 : ℝ) < (j.1 : ℝ)
    exact_mod_cast ((Nat.zero_le (cutoffU n)).trans_lt (mem_Ioc.mp core.1).1)
  have divTop : j.2 ≤ cutoffU n := (mem_Icc.mp core.2).2.trans (min_le_left _ _)
  have dTop : D ≤ N^(1/16 : ℝ) :=
    (show D ≤ (cutoffU n : ℝ) by
      change (j.2 : ℝ) ≤ (cutoffU n : ℝ)
      exact_mod_cast divTop).trans (Nat.floor_le (by positivity))
  have square : N ≤ (D*P)^2 := by
    change (n : ℝ) ≤ ((j.2 : ℝ)*(j.1 : ℝ))^2
    rw [← Nat.cast_mul]
    exact_mod_cast high
  have rootLe : N^(1/2 : ℝ) ≤ D*P := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_left (by positivity)).mpr square
  have pLow : N^(7/16 : ℝ) ≤ P := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (1/16 : ℝ))).mp
    calc
      N^(7/16 : ℝ)*N^(1/16 : ℝ) = N^(1/2 : ℝ) := by rw [← Real.rpow_add np]; norm_num
      _ ≤ D*P := rootLe
      _ ≤ P*N^(1/16 : ℝ) := by rw [mul_comm D P]; exact mul_le_mul_of_nonneg_left dTop p0.le
  have cof : n/j.1 ≤ upperCut n := by
    change n/j.1 ≤ ⌊N^(2/3 : ℝ)⌋₊
    apply Nat.le_floor
    calc
      ((n/j.1 : ℕ) : ℝ) ≤ N/P := Nat.cast_div_le
      _ ≤ N/N^(7/16 : ℝ) := div_le_div_of_nonneg_left np.le (by positivity) pLow
      _ = N^(9/16 : ℝ) := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub np]; norm_num
      _ ≤ N^(2/3 : ℝ) := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
  unfold rightLowWaveUpper
  exact min_eq_right (right_low_full_prefix_of_cofactor_bound cof)

theorem right_low_target_gcd_dvd_short_factor {n : ℕ} {j : RightLowWaveIndex}
    (hp : j.1.Prime) (hpn : ¬j.1 ∣ n) : (rightLowWaveStep j).gcd n ∣ j.2 := by
  let G := (rightLowWaveStep j).gcd n
  have h : G.Coprime j.1 := by
    apply (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro dvd
    exact hpn (dvd.trans (Nat.gcd_dvd_right (rightLowWaveStep j) n))
  exact h.dvd_of_dvd_mul_right (Nat.gcd_dvd_left (rightLowWaveStep j) n)

theorem right_low_residue_above_root_eq_single_prefix {n u : ℕ} {j : RightLowWaveIndex}
    (hj : j ∈ rightLowWaveItems n) (high : n ≤ (rightLowWaveStep j)^2)
    (larger : u < rightLowWaveStep j) (u0 : 0 < u) (un : u ≤ n)
    (hd : (rightLowWaveStep j).gcd u ∣ n) :
    let v := rightLowWaveStep j
    let g := v.gcd u
    let m := u/g
    let z := (n/g : ℕ)
    (pairResidueError n v u 0 (rightLowWaveUpper n j) 0 (n/u) : ℂ) =
      centeredIntIntervalResidue m 0 (((z-m)/(v/g) : ℕ) : ℤ)
        ((z : ZMod m)*((v/g : ℕ) : ZMod m)⁻¹) := by
  rw [right_low_full_upper_of_root_le hj high]
  have h := swapped_capped_residue_two_prefixes (b := 0) u0 larger un hd
  dsimp only at h ⊢
  rw [if_pos (Nat.zero_le _)] at h
  rw [h]
  simp [centeredIntIntervalResidue, intIntervalResidueCount]

end

end B13BoundedStepProductSavingProof

end

/- Short low divided hyperbola windows -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

set_option maxHeartbeats 2300000 in
def shortLowModulusCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(133/256 : ℝ)⌋₊

end

end B13BoundedStepProductSavingProof

end

/- Moderate low divided hyperbola windows -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

set_option maxHeartbeats 2300000 in
def moderateLowDividedHyperbolaCofactorCap (n r₀ g e k : ℕ) : ℕ :=
  (r₀/g)/(primeHyperbolaFactorLo n k/e+1)

set_option maxHeartbeats 2300000 in
def moderateLowDividedHyperbolaPrefix (n m g e k l₀ r₀ num : ℕ) : ℂ :=
  let v := m/g
  let l := l₀/g
  let r := r₀/g
  gatedBilinearSum (expandedHighDividedHyperbolaFactors n m g e k)
    (intIntervalModUnits v 0 (moderateLowDividedHyperbolaCofactorCap n r₀ g e k))
    (fun a => (leftBandMoebius n (e*a) : ℂ))
    (fun j => (leftBilinearFactor n ((g/e)*j.toNat) : ℂ))
    (fun a => (l/a : ℕ)) (fun a => (r/a : ℕ))
    (fun a j => centeredIntIntervalResidue v 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
      ((n/g : ℕ)*((a : ZMod v)*(j : ZMod v))⁻¹))

set_option maxHeartbeats 2300000 in
def moderateLowDividedHyperbolaWindow (n m g e k l₀ r₀ : ℕ) : ℂ :=
  let v := m/g
  moderateLowDividedHyperbolaPrefix n m g e k l₀ r₀ (n/g-v) -
    moderateLowDividedHyperbolaPrefix n m g e k l₀ r₀ (n/g-v*(n/m)-1)

set_option maxHeartbeats 2300000 in
theorem norm_moderate_low_divided_hyperbola_prefix_le {n m g e k l₀ r₀ num : ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (hsq : n ≤ m^2) (modCap : m ≤ shortLowModulusCap n)
    (charTop : m.gcd n ≤ targetDivisorCap n)
    (rUpper : r₀ ≤ extendedWideStepCap n) (rProd : r₀*m ≤ expandedHyperbolaProductCap n)
    (lLower : subcriticalMediumProductCap n/m ≤ l₀)
    (gpos : 0 < g) (gn : g ∣ n) (gm : g ∣ m) (gSmall : g ≤ nearProductCommonDivisorCut n)
    (e0 : 0 < e) (eg : e ∣ g) (hk : k ∈ Icc 16 63)
    (ns : 1 < n) (huge : (6 : ℝ) < (n : ℝ)^(1/512 : ℝ)) (numN : num ≤ n/g)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖moderateLowDividedHyperbolaPrefix n m g e k l₀ r₀ num‖ ≤
      592*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3/(m : ℝ) := by
  let v := m/g
  let N := (n : ℝ)
  let M := (m : ℝ)
  let V := (v : ℝ)
  let G := (g : ℝ)
  let E := (e : ℝ)
  let y := (k : ℝ)/256
  let x := y-1/512
  let A := primeHyperbolaFactorFloor n (k+1)/e
  let aLo := primeHyperbolaFactorLo n k
  let S := moderateLowDividedHyperbolaCofactorCap n r₀ g e k
  let I := expandedHighDividedHyperbolaFactors n m g e k
  let J := intIntervalModUnits v 0 S
  let mLo := l₀
  let mHi := r₀
  let l := mLo/g
  let r := mHi/g
  let L := logBudget n
  let α (a : ℕ) : ℂ := leftBandMoebius n (e*a)
  let β (j : ℤ) : ℂ := leftBilinearFactor n ((g/e)*j.toNat)
  have v0 : 0 < v := Nat.div_pos (Nat.le_of_dvd m0 gm) gpos
  let _ : NeZero v := ⟨v0.ne'⟩
  have vprod : v*g=m := Nat.div_mul_cancel gm
  have npNat : 0 < n := zero_lt_one.trans ns
  have nr : 1 < N := show (1 : ℝ) < (n : ℝ) from by exact_mod_cast ns
  have np : 0 < N := zero_lt_one.trans nr
  have gp : 0 < G := show (0 : ℝ) < (g : ℝ) from by exact_mod_cast gpos
  have G1 : 1 ≤ G := show (1 : ℝ) ≤ (g : ℝ) from by exact_mod_cast gpos
  have vN : v ≤ n := (by simpa only [mul_one] using Nat.mul_le_mul_left v (show 1 ≤ g from gpos) : v ≤ v*g).trans
    (by rw [vprod]; exact mN)
  have vEq : V*G=M := by
    change (v : ℝ)*(g : ℝ) = (m : ℝ)
    exact_mod_cast vprod
  have origHi : M ≤ N^(133/256 : ℝ) :=
    (show M ≤ (shortLowModulusCap n : ℝ) by
      change (m : ℝ) ≤ (shortLowModulusCap n : ℝ)
      exact_mod_cast modCap).trans
      (Nat.floor_le (by positivity))
  have castGcd : (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ N^(1/128 : ℝ) := by
    have vd : v ∣ m := ⟨g,vprod.symm⟩
    have nd : n/g ∣ n := ⟨g,(Nat.div_mul_cancel gn).symm⟩
    have d : v.gcd (n/g) ∣ m.gcd n := Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans vd) ((Nat.gcd_dvd_right _ _).trans nd)
    have relation := (gcd_val_nat_cast_le_gcd (m := v) (n/g)).trans
      ((Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ npNat) d).trans charTop)
    exact (show (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ (targetDivisorCap n : ℝ) by
      exact_mod_cast relation).trans (Nat.floor_le (by positivity))
  have vTop : V ≤ N^(133/256 : ℝ) := by
    have h : V ≤ M := by
      rw [← vEq]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left G1 (by positivity : 0 ≤ V)
    exact h.trans origHi
  have gCap : G ≤ N^(1/512 : ℝ) :=
    (by exact_mod_cast gSmall : (g : ℝ) ≤ nearProductCommonDivisorCut n).trans (Nat.floor_le (by positivity))
  have eCap : E ≤ N^(1/512 : ℝ) :=
    (by exact_mod_cast Nat.le_of_dvd gpos eg : (e : ℝ) ≤ g).trans gCap
  have mLower : N^(1/2 : ℝ) ≤ M := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_left (by positivity)).mpr
    change (n : ℝ) ≤ (m : ℝ)^2
    exact_mod_cast hsq
  have vLower : N^(255/512 : ℝ) ≤ V := by
    apply (mul_le_mul_iff_left₀ gp).mp
    calc
      _ ≤ N^(255/512 : ℝ)*N^(1/512 : ℝ) :=
        mul_le_mul_of_nonneg_left gCap (by positivity)
      _ = N^(1/2 : ℝ) := by rw [← Real.rpow_add np]; norm_num
      _ ≤ M := mLower
      _ = _ := vEq.symm
  have vLo : N^(1/3 : ℝ) < V :=
    (Real.rpow_lt_rpow_of_exponent_lt nr (by norm_num : (1/3 : ℝ) < 255/512)).trans_le vLower
  have kmin : (16 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
  have kmax : (k : ℝ) ≤ 63 := by exact_mod_cast (mem_Icc.mp hk).2
  have xLo : 31/512 ≤ x := by unfold x y; linarith
  have xHi : x ≤ 1/4 := by unfold x y; linarith
  have aFormula : primeHyperbolaFactorFloor n (k+1) = ⌊N^(x+3/512)⌋₊ := by
    unfold primeHyperbolaFactorFloor N x y
    rw [Nat.cast_add,Nat.cast_one,add_div]
    congr 2
    ring
  have aCap : (A : ℝ) ≤ N^(x+3/512) :=
    (by exact_mod_cast Nat.div_le_self (primeHyperbolaFactorFloor n (k+1)) e :
      (A : ℝ) ≤ (primeHyperbolaFactorFloor n (k+1) : ℝ)).trans (by rw [aFormula]; exact Nat.floor_le (by positivity))
  have A1 : 0 < A := by
    change 1 ≤ primeHyperbolaFactorFloor n (k+1)/e
    apply (Nat.le_div_iff_mul_le e0).mpr
    rw [one_mul,aFormula]
    exact Nat.le_floor (eCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by linarith)))
  have aQ : (A : ℝ) ≤ N^(1/4 : ℝ) :=
    aCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by unfold x y; linarith))
  have Av : A < v := by
    have h := aQ.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt nr (by norm_num : (1/4 : ℝ) < 1/3)).trans vLo)
    change (A : ℝ) < (v : ℝ) at h
    exact_mod_cast h
  have Icap : I ⊆ Icc 1 A := by
    intro a ha
    have h := mem_Ioc.mp (mem_filter.mp ha).1
    exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt h.1,h.2.trans (Nat.div_le_div_right (min_le_right (lowCut n) _))⟩
  have copI (a : ℕ) (ha : a ∈ I) : a.Coprime v := (mem_filter.mp ha).2.2
  have rN : mHi ≤ n := rUpper.trans (extended_wide_step_le npNat)
  have rG : r*g ≤ mHi := Nat.div_mul_le_self mHi g
  have sR : S ≤ r := Nat.div_le_self _ _
  have rp : r*v*g^2 ≤ expandedHyperbolaProductCap n := calc
    _ = (r*g)*(v*g) := by ring
    _ = (r*g)*m := by rw [vprod]
    _ ≤ mHi*m := Nat.mul_le_mul_right m rG
    _ ≤ _ := rProd
  have rCap : (r : ℝ)*V*G^2 ≤ 2*N^(513/512 : ℝ) := by
    calc
      _ ≤ (expandedHyperbolaProductCap n : ℝ) := by
        change (r : ℝ)*(v : ℝ)*(g : ℝ)^2 ≤ (expandedHyperbolaProductCap n : ℝ)
        exact_mod_cast rp
      _ ≤ _ := by
        unfold expandedHyperbolaProductCap
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
  have cofactorFloor : N^x ≤ (aLo/e : ℕ)+1 := by
    have more : aLo < (aLo/e+1)*e := (Nat.div_lt_iff_lt_mul e0).mp (Nat.lt_succ_self _)
    have rank : (primeHyperbolaFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*E := by
      have le : primeHyperbolaFactorFloor n k+1 ≤ (aLo/e+1)*e :=
        Nat.succ_le_of_lt ((le_max_right _ _).trans_lt more)
      change (primeHyperbolaFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*(e : ℝ)
      exact_mod_cast le
    have ground : N^y ≤ (((aLo/e : ℕ) : ℝ)+1)*E := (Nat.lt_floor_add_one (N^y)).le.trans rank
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (1/512 : ℝ))).mp
    calc
      _ = N^y := by rw [← Real.rpow_add np]; unfold x; simp
      _ ≤ (((aLo/e : ℕ) : ℝ)+1)*E := ground
      _ ≤ _ := mul_le_mul_of_nonneg_left eCap (by positivity)
  have sCap : (S : ℝ)*V*G^2 ≤ 2*N^(513/512-x) := by
    have cut : S*(aLo/e+1) ≤ r := Nat.div_mul_le_self r (aLo/e+1)
    have scaled : (S : ℝ)*(((aLo/e : ℕ) : ℝ)+1) ≤ (r : ℝ) := by exact_mod_cast cut
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np x)).mp
    calc
      _ ≤ ((S : ℝ)*V*G^2)*(((aLo/e : ℕ) : ℝ)+1) :=
        mul_le_mul_of_nonneg_left cofactorFloor (by positivity)
      _ = ((S : ℝ)*(((aLo/e : ℕ) : ℝ)+1))*V*G^2 := by ring
      _ ≤ (r : ℝ)*V*G^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right scaled (by positivity)) (by positivity)
      _ ≤ 2*N^(513/512 : ℝ) := rCap
      _ = (2*N^(513/512-x))*N^x := by rw [mul_assoc,← Real.rpow_add np,sub_add_cancel]
  have endCap : num/(l+1) ≤ ⌊V*G*N^(1/256 : ℝ)⌋₊ := by
    have endOrig := prime_hyperbola_endpoint_cap_of_size npNat m0 lLower (le_rfl : n ≤ n)
    have s : mLo+1 ≤ (l+1)*g := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul gpos).mp (Nat.lt_succ_self (mLo/g)))
    rw [vEq]
    calc
      _ ≤ (n/g)/(l+1) := Nat.div_le_div_right numN
      _ = n/((l+1)*g) := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm g (l+1)]
      _ ≤ n/(mLo+1) := Nat.div_le_div_left s (Nat.succ_pos _)
      _ ≤ _ := endOrig
  have divN (z : ℕ) (h : z ≤ n) : (z.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ ns.le (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors z (h.trans nn)
  have divV (z : ℕ) (h : z ≤ 4*v^3) : (z.divisors.card : ℝ) ≤ T :=
    divisors z (h.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left vN 3)))
  have divR (z : ℕ) (h : z ≤ r) : (z.divisors.card : ℝ) ≤ T :=
    divN z (h.trans ((Nat.div_le_self _ _).trans rN))
  have aw (a : ℕ) (ha : a ∈ I) : ‖α a‖ ≤ T := by
    have h := (mem_Ioc.mp (mem_filter.mp ha).1).2
    have eLe : e*a ≤ lowCut n := by
      have h' := (Nat.le_div_iff_mul_le e0).mp h
      exact (by simpa only [Nat.mul_comm] using h'.trans (min_le_left _ _) : e*a ≤ lowCut n)
    have lowN : lowCut n ≤ n := by
      have h : (lowCut n : ℝ) ≤ (n : ℝ) :=
        (Nat.floor_le (by positivity)).trans (Real.rpow_le_self_of_one_le nr.le (by norm_num))
      exact_mod_cast h
    exact (norm_leftBandMoebius_le n _).trans (divN _ (eLe.trans lowN))
  have bw (j : ℤ) (hj : j ∈ J) : ‖β j‖ ≤ T*L := by
    have data : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod v) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    have jR : j.toNat ≤ r := (show j.toNat ≤ S by have := (mem_Ioc.mp data.1).2; omega).trans sR
    have h : (g/e)*j.toNat ≤ n := calc
      _ ≤ g*r := Nat.mul_le_mul (Nat.div_le_self g e) jR
      _ ≤ mHi := by simpa only [Nat.mul_comm] using rG
      _ ≤ _ := rN
    exact norm_left_bilinear_factor_bound h divN
  have logBound : 1+Real.log V ≤ L := by
    have pv : 0 < V := show (0 : ℝ) < (v : ℝ) from by exact_mod_cast v0
    have up : V ≤ (n : ℝ)+2 := by
      change (v : ℝ) ≤ (n : ℝ)+2
      exact_mod_cast vN.trans (by omega : n≤n+2)
    unfold L logBudget
    linarith only [Real.log_le_log pv up]
  change ‖moderateLowDividedHyperbolaPrefix n m g e k l₀ r₀ num‖ ≤ 592*N^(1023/1024 : ℝ)*T^3*L^3/M
  by_cases smallBand : k ≤ 24
  · have smallK : (k : ℝ) ≤ 24 := by exact_mod_cast smallBand
    have aSmall : (A : ℝ) ≤ N^(25/256 : ℝ) :=
      aCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by unfold x y; linarith only [smallK]))
    have aPow : (A : ℝ)^5 ≤ N^(125/256 : ℝ) := by
      calc
        _ ≤ (N^(25/256 : ℝ))^5 := pow_le_pow_left₀ (by positivity) aSmall _
        _ = _ := by rw [← Real.rpow_mul_natCast np.le]; norm_num
    have large : (2 : ℝ) ≤ N^(1/64 : ℝ) :=
      (show (2 : ℝ) ≤ 6 by norm_num).trans
        (huge.le.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by norm_num)))
    have small : 6*A^5 < v := by
      have hs : (6 : ℝ)*(A : ℝ)^5 < V := calc
        _ ≤ 6*N^(125/256 : ℝ) := mul_le_mul_of_nonneg_left aPow (by norm_num)
        _ < N^(1/512 : ℝ)*N^(125/256 : ℝ) :=
          mul_lt_mul_of_pos_right huge (by positivity)
        _ ≤ N^(255/512 : ℝ) := by
          rw [← Real.rpow_add np]
          exact Real.rpow_le_rpow_of_exponent_le nr.le (by norm_num)
        _ ≤ _ := vLower
      change (6 : ℝ)*(A : ℝ)^5 < (v : ℝ) at hs
      exact_mod_cast hs
    have dA (z : ℕ) (hz : z ≤ max v (A^3)) : (z.divisors.card : ℝ) ≤ T := by
      have v3 : v ≤ v^3 := by simpa only [pow_one] using pow_le_pow_right₀ v0 (show 1 ≤ 3 by decide)
      exact divV z (hz.trans ((max_le v3 (Nat.pow_le_pow_left Av.le 3)).trans (by omega)))
    have b := norm_sixth_moment_expanded_ratio_hyperbola_le (m := v) (c := ((n/g : ℕ) : ZMod v)) (g := g)
      castGcd nr.le large G1 T1 (one_le_logBudget n) vTop vLower gCap xLo logBound
      aCap sCap rCap endCap small I Icap copI α β aw bw dA divR
    exact b.trans_eq (by rw [vEq])
  · have kBig : (25 : ℝ) ≤ k := by exact_mod_cast (show 25 ≤ k by omega)
    have vHi : V ≤ N^(1/2+x/2-7/256) :=
      vTop.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by unfold x y; linarith only [kBig]))
    have vMid : V ≤ N^(5/8-x/3) :=
      vTop.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by linarith only [xHi]))
    have b := norm_expanded_modulus_ratio_hyperbola_le (m := v) (c := ((n/g : ℕ) : ZMod v)) (g := g)
      castGcd nr.le G1 T1 (one_le_logBudget n) vHi vMid vLo.le gCap xLo xHi logBound aCap sCap rCap endCap
      A1 Av I Icap copI α β aw bw divV divR
    exact b.trans_eq (by rw [vEq])

set_option maxHeartbeats 2300000 in
theorem norm_moderate_low_divided_hyperbola_window_le {n m g e k l₀ r₀ : ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (hsq : n ≤ m^2) (modCap : m ≤ shortLowModulusCap n)
    (charTop : m.gcd n ≤ targetDivisorCap n)
    (rUpper : r₀ ≤ extendedWideStepCap n) (rProd : r₀*m ≤ expandedHyperbolaProductCap n)
    (lLower : subcriticalMediumProductCap n/m ≤ l₀)
    (gpos : 0 < g) (gn : g ∣ n) (gm : g ∣ m) (gSmall : g ≤ nearProductCommonDivisorCut n)
    (e0 : 0 < e) (eg : e ∣ g) (hk : k ∈ Icc 16 63)
    (ns : 1 < n) (huge : (6 : ℝ) < (n : ℝ)^(1/512 : ℝ)) {T : ℝ} (T1 : 1 ≤ T)
    (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖moderateLowDividedHyperbolaWindow n m g e k l₀ r₀‖ ≤
      1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3/(m : ℝ) := by
  unfold moderateLowDividedHyperbolaWindow
  dsimp only
  refine (norm_sub_le _ _).trans ?_
  let v := m/g
  let hi := v*(n/m)
  have h₁ := norm_moderate_low_divided_hyperbola_prefix_le (num := n/g-v) m0 mN hsq modCap
    charTop rUpper rProd lLower gpos gn gm gSmall e0 eg hk ns huge
    (Nat.sub_le (n/g) v) T1 divisors
  have h₂ := norm_moderate_low_divided_hyperbola_prefix_le (num := n/g-hi-1) m0 mN hsq modCap
    charTop rUpper rProd lLower gpos gn gm gSmall e0 eg hk ns huge
    ((Nat.sub_le (n/g-hi) 1).trans (Nat.sub_le (n/g) hi)) T1 divisors
  exact (add_le_add h₁ h₂).trans_eq (by ring)

end

end B13BoundedStepProductSavingProof

end

/- Factor capped interval error -/
section

namespace B13BoundedStepProductSavingProof

noncomputable section

theorem pair_residue_error_eq_zero_of_right_interval_empty {n u v l r lo s : ℕ}
    (u0 : 0 < u) (v0 : 0 < v) (endpoints : s ≤ lo) : pairResidueError n u v l r lo s = 0 := by
  have cs : (s : ℤ) ≤ (lo : ℤ) := by exact_mod_cast endpoints
  have cv : (1 : ℤ) ≤ (v : ℤ) := by exact_mod_cast v0
  have cu : (0 : ℤ) < u := by exact_mod_cast u0
  have lo1 : (v : ℤ)*s+1 ≤ (v : ℤ)*((lo : ℤ)+1) := by
    have h := mul_le_mul_of_nonneg_left cs (zero_le_one.trans cv)
    linarith
  have reg : pairLeftUpper n u v r lo ≤ pairLeftLower n u v l s := by
    unfold pairLeftUpper pairLeftLower
    exact (min_le_right _ _).trans ((Int.ediv_le_ediv cu (by linarith only [lo1])).trans (le_max_right _ _))
  unfold pairResidueError
  by_cases compat : u.gcd v ∣ n
  · rw [ite_eq_left compat]
    by_cases balance : pairLeftLower n u v l s ≤ pairLeftUpper n u v r lo
    · have eq := le_antisymm balance reg
      rw [ite_eq_left balance,eq,sub_self,zero_div]
    · exact ite_eq_right balance
  · exact ite_eq_right compat

theorem left_factor_capped_interval_residue_eq_normalized {n a j v lo s : ℕ}
    (a0 : 0 < a) (j0 : 0 < j) (v0 : 0 < v) (ord : lo < s) (sv : v*s ≤ n) (dn : (a*j).gcd v ∣ n) :
    let d := (a*j).gcd v
    let e := a.gcd d
    let U := (a/e)*(j/(d/e))
    let V := v/d
    let N := n/d
    let z := (N : ZMod V)*(U : ZMod V)⁻¹
    (pairResidueError n (a*j) v 0 (n/(a*j)) lo s : ℂ) =
      centeredIntIntervalResidue V 0 (((N-V*(lo+1) : ℕ) : ℤ)/(U : ℤ)) z -
        centeredIntIntervalResidue V 0 (((N-V*s-1 : ℕ) : ℤ)/(U : ℤ)) z := by
  dsimp only
  let d := (a*j).gcd v
  let e := a.gcd d
  let V := v/d
  let N := n/d
  let F (x : ℕ) : ℂ :=
    let z := (N : ZMod V)*(x : ZMod V)⁻¹
    centeredIntIntervalResidue V 0 (((N-V*(lo+1) : ℕ) : ℤ)/(x : ℤ)) z -
      centeredIntIntervalResidue V 0 (((N-V*s-1 : ℕ) : ℤ)/(x : ℤ)) z
  have d0 : 0 < d := Nat.gcd_pos_of_pos_right _ v0
  have uEq : (a*j)/d = (a/e)*(j/(d/e)) :=
    (divide_left_product_of_gcd d0 (Nat.gcd_dvd_left (a*j) v)).2
  change (pairResidueError n (a*j) v 0 (n/(a*j)) lo s : ℂ) = F ((a/e)*(j/(d/e)))
  calc
    _ = F ((a*j)/d) := divided_capped_interval_residue_eq_two_centered (mul_pos a0 j0) v0 ord sv dn
    _ = _ := congrArg F uEq

end

end B13BoundedStepProductSavingProof

end

/- High divided hyperbola selection -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical Finset

noncomputable section

theorem high_step_le_medium_of_square_le {n m : ℕ} (m0 : 0 < m) (sq : m^2 ≤ n) :
    m ≤ wideMediumStepCap n := by
  have n1 : 1 ≤ n := by
    have q := Nat.mul_pos m0 m0
    rw [← pow_two] at q
    omega
  have nr : (1 : ℝ) ≤ n := by exact_mod_cast n1
  apply Nat.le_floor
  calc
    (m : ℝ) ≤ (n : ℝ)^(1/2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.le_sqrt (by positivity) (by positivity)).mpr (by exact_mod_cast sq)
    _ ≤ (n : ℝ)^(7/12 : ℝ) := Real.rpow_le_rpow_of_exponent_le nr (by norm_num)

end

end B13BoundedStepProductSavingProof

end

/- Old high residue partition -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

def highResidueTerm (n : ℕ) (i : ℕ × ℕ) (j : RightHighWaveIndex) : ℂ :=
  leftBilinearWeight n i*rightHighWaveWeight n j*
    (pairResidueError n (leftBilinearStep i) (rightHighWaveStep j) 0
      (n/leftBilinearStep i) (rightHighWaveLower n j) (n/rightHighWaveStep j) : ℂ)

def highResidueSum (n : ℕ) (gate : (ℕ × ℕ) → RightHighWaveIndex → Prop) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ rightHighWaveItems n,
    if gate i j then highResidueTerm n i j else 0

end

end B13BoundedStepProductSavingProof

end

/- Expanded high divided hyperbola row bound -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def expandedHighDividedHyperbolaDivisors (n m : ℕ) : Finset ℕ :=
  n.divisors.filter fun g => g ≤ nearProductCommonDivisorCut n ∧ g ≤ maximumStep n ∧ g ∣ m

end

end B13BoundedStepProductSavingProof

end

/- Expanded high divided hyperbola selection -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical Finset

noncomputable section

theorem square_le_implies_step_le_expanded_high_cap {n m : ℕ} (m0 : 0 < m) (sq : m^2 ≤ n) :
    m ≤ expandedHighModulusCap n := by
  have n1 : 1 ≤ n := by
    have q := Nat.mul_pos m0 m0
    rw [← pow_two] at q
    omega
  have nr : (1 : ℝ) ≤ n := by exact_mod_cast n1
  apply Nat.le_floor
  calc
    (m : ℝ) ≤ (n : ℝ)^(1/2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.le_sqrt (by positivity) (by positivity)).mpr (by exact_mod_cast sq)
    _ ≤ (n : ℝ)^(515/1024 : ℝ) := Real.rpow_le_rpow_of_exponent_le nr (by norm_num)

end

end B13BoundedStepProductSavingProof

end

/- Residue direction swap -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

private theorem min_sub_reflected_max (x a b : ℝ) : min a (x-b) = x-max b (x-a) := by
  by_cases h : a ≤ x-b
  · rw [min_eq_left h,max_eq_right (show b ≤ x-a by linarith only [h])]
    ring
  · rw [min_eq_right (le_of_not_ge h),max_eq_left (show x-a ≤ b by linarith only [lt_of_not_ge h])]

private theorem max_sub_reflected_min (x a b : ℝ) : max a (x-b) = x-min b (x-a) := by
  by_cases h : a ≤ x-b
  · rw [max_eq_right h,min_eq_left (show b ≤ x-a by linarith only [h])]
  · rw [max_eq_left (le_of_not_ge h),min_eq_right (show x-a ≤ b by linarith only [lt_of_not_ge h])]
    ring

theorem progression_overlap_swap (u v l r p s : ℕ) (x : ℝ) :
    progressionOverlap u v l r p s x = progressionOverlap v u p s l r x := by
  unfold progressionOverlap
  rw [min_sub_reflected_max x (currentBinEdge u r) (currentBinEdge v p),
    max_sub_reflected_min x (currentBinEdge u l) (currentBinEdge v s)]
  congr 1
  ring

theorem overlap_mass_swap (n u v l r p s : ℕ) :
    overlapMass n u v l r p s = overlapMass n v u p s l r := by
  unfold overlapMass
  rw [progression_overlap_swap, mul_comm ((u : ℂ)⁻¹) ((v : ℂ)⁻¹)]

theorem card_progression_pair_swap (n u v l r p s : ℕ) :
    (progressionPairSolutions n u v l r p s).card =
      (progressionPairSolutions n v u p s l r).card := by
  let swap (i : ℕ × ℕ) := (i.2,i.1)
  have swapTwice (i : ℕ × ℕ) : swap (swap i) = i := by cases i; rfl
  have swapInj : Function.Injective swap := fun _ _ h => by
    simpa only [swapTwice] using congrArg swap h
  have image : (progressionPairSolutions n u v l r p s).image swap =
      progressionPairSolutions n v u p s l r := by
    ext i
    have mem {x : ℕ × ℕ} : swap x ∈ progressionPairSolutions n v u p s l r ↔
        x ∈ progressionPairSolutions n u v l r p s := by
      simp only [progressionPairSolutions,mem_filter,mem_product,swap]
      rw [add_comm (v*x.2)]
      tauto
    constructor
    · intro hx
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
      exact mem.mpr hj
    · intro hi
      refine mem_image.mpr ⟨swap i,?_,swapTwice i⟩
      exact mem.mp (swapTwice i ▸ hi)
  rw [← image,card_image_of_injective _ swapInj]

theorem residue_error_swap_diff_eq_volume_diff {n u v l r p s : ℕ} (hu : 0 < u) (hv : 0 < v) :
    pairResidueError n u v l r p s - pairResidueError n v u p s l r =
      pairVolume n v u p s l r - pairVolume n u v l r p s := by
  have e := congrArg (fun t : ℕ => (t : ℝ)) (card_progression_pair_swap n u v l r p s)
  rw [progression_pair_count_eq_volume_add_error hu hv, progression_pair_count_eq_volume_add_error hv hu] at e
  linarith only [e]

end

end B13BoundedStepProductSavingProof

end

/- Large left divisor residue -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical Finset

noncomputable section

private theorem prefix_solution_count_swap (n u v : ℕ) :
    prefixSolutionCount n u v = prefixSolutionCount n v u := by
  unfold prefixSolutionCount
  exact_mod_cast card_progression_pair_swap n u v 0 (n/u) 0 (n/v)

def largeLeftDivisorResidueFamily (n D G : ℕ) {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (u : ι → ℕ) (v p s : κ → ℕ)
    (α : ι → ℂ) (β : κ → ℂ) (gate : ι → κ → Prop) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J,
    @ite ℂ (gate i j ∧ (u i).gcd (v j) ≤ G ∧ D < (u i).gcd n) (Classical.propDecidable _)
      (α i*β j*(pairResidueError n (u i) (v j) 0 (n/u i) (p j) (s j) : ℂ)) 0

theorem norm_large_left_divisor_residue_family_le {n D G A : ℕ} (n0 : 0 < n) (An : A ≤ n)
    {ι κ : Type*} (I : Finset ι) (J : Finset κ) (u : ι → ℕ) (v p s : κ → ℕ)
    (α : ι → ℂ) (β : κ → ℂ) (gate : ι → κ → Prop)
    {W T : ℝ} (W0 : 0 ≤ W) (T0 : 0 ≤ T) (divCount : ∀ z ≤ n, (z.divisors.card : ℝ) ≤ T)
    (lu : ∀ i ∈ I, u i ∈ Icc 1 A) (rv : ∀ j ∈ J, v j ∈ Icc 1 A)
    (lm : ∀ m ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i = m), ‖α i‖) ≤ W)
    (rm : ∀ m ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j = m), ‖β j‖) ≤ W) :
    ‖largeLeftDivisorResidueFamily n D G I J u v p s α β gate‖ ≤
      T*(W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(G : ℝ)*logBudget n^2)) := by
  let K := n.divisors.filter (D < ·)
  let F (d x y : ℕ) : ℝ :=
    if d ∣ y then prefixSolutionCount n x y+(G : ℝ)*(n : ℝ)/((x : ℝ)*(y : ℝ)) else 0
  let term (i : ι) (j : κ) : ℂ :=
    @ite ℂ (gate i j ∧ (u i).gcd (v j) ≤ G ∧ D < (u i).gcd n) (Classical.propDecidable _)
      (α i*β j*(pairResidueError n (u i) (v j) 0 (n/u i) (p j) (s j) : ℂ)) 0
  have F0 (d x y : ℕ) : 0 ≤ F d x y := by
    unfold F
    split_ifs
    · unfold prefixSolutionCount
      positivity
    · exact le_rfl
  have per (i : ι) (hi : i ∈ I) (j : κ) (hj : j ∈ J) :
      ‖term i j‖ ≤ ∑ d ∈ K, ‖α i‖*‖β j‖*F d (v j) (u i) := by
    by_cases sel : gate i j ∧ (u i).gcd (v j) ≤ G ∧ D < (u i).gcd n
    · unfold term
      rw [ite_eq_left sel,norm_mul,norm_mul]
      let d := (u i).gcd n
      have dn : d ∣ n := Nat.gcd_dvd_right (u i) n
      have dv : d ∣ u i := Nat.gcd_dvd_left (u i) n
      have mem : d ∈ K := mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dn,n0.ne'⟩,sel.2.2⟩
      have est := norm_pair_residue_le_count_add_capped_volume (n := n) (p := p j) (s := s j)
        (mem_Icc.mp (lu i hi)).1 (mem_Icc.mp (rv j hj)).1 sel.2.1
      have b : ‖(pairResidueError n (u i) (v j) 0 (n/u i) (p j) (s j) : ℂ)‖ ≤ F d (v j) (u i) := by
        unfold F
        rw [ite_eq_left dv, prefix_solution_count_swap n (v j) (u i), mul_comm (v j : ℝ) (u i : ℝ)]
        exact est
      exact (mul_le_mul_of_nonneg_left b (by positivity)).trans
        (single_le_sum (fun z _ => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (F0 _ _ _)) mem)
    · unfold term
      rw [ite_eq_right sel,norm_zero]
      exact sum_nonneg fun d _ => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (F0 _ _ _)
  have dBound (d : ℕ) (hd : d ∈ K) :
      (∑ i ∈ I, ∑ j ∈ J, ‖α i‖*‖β j‖*F d (v j) (u i)) ≤
        W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(G : ℝ)*logBudget n^2) := by
    obtain ⟨base,above⟩ := mem_filter.mp hd
    have dn := (Nat.mem_divisors.mp base).1
    have d0 : 0 < d := (Nat.zero_le _).trans_lt above
    have dp : (0 : ℝ) < d := by exact_mod_cast d0
    have dR : (D : ℝ)+1 ≤ (d : ℝ) := by exact_mod_cast Nat.succ_le_of_lt above
    have cmp : (n : ℝ)/(d : ℝ) ≤ (n : ℝ)/((D : ℝ)+1) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) dR
    have h := sum_product_norm_le_of_step_mass I J u v α β (fun x y => F d y x) W0 lu rv lm rm
      (fun x _ y _ => F0 d y x)
    refine h.trans ?_
    rw [sum_comm]
    unfold F
    simp_rw [← sum_filter]
    calc
      _ ≤ W^2*(((n : ℝ)/(d : ℝ))*(T^2+(G : ℝ)*logBudget n^2)) :=
        mul_le_mul_of_nonneg_left (sum_right_divisor_mass_le (G := G) An d0 dn T0 divCount) (sq_nonneg _)
      _ ≤ _ := by rw [mul_assoc]; gcongr
  have kc : (K.card : ℝ) ≤ T :=
    (by exact_mod_cast card_le_card (filter_subset _ n.divisors) : (K.card : ℝ) ≤ n.divisors.card).trans
      (divCount n le_rfl)
  change ‖∑ i ∈ I, ∑ j ∈ J, term i j‖ ≤ _
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ‖term i j‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ∑ d ∈ K, ‖α i‖*‖β j‖*F d (v j) (u i) :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => per i hi j hj
    _ = ∑ d ∈ K, ∑ i ∈ I, ∑ j ∈ J, ‖α i‖*‖β j‖*F d (v j) (u i) := by
      calc
        _ = ∑ i ∈ I, ∑ d ∈ K, ∑ j ∈ J, ‖α i‖*‖β j‖*F d (v j) (u i) :=
          sum_congr rfl fun _ _ => sum_comm
        _ = _ := sum_comm
    _ ≤ ∑ _ ∈ K, W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(G : ℝ)*logBudget n^2) :=
      sum_le_sum dBound
    _ = (K.card : ℝ)*(W^2*((n : ℝ)/((D : ℝ)+1))*(T^2+(G : ℝ)*logBudget n^2)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right kc (by positivity)

end

end B13BoundedStepProductSavingProof

end

/- Thin high arithmetic cuts -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open scoped Classical Finset

noncomputable section

def thinHighProductCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(8191/8192 : ℝ)⌋₊
def thinHighGcdCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/4096 : ℝ)⌋₊
def thinHighLeftDivisorCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/2048 : ℝ)⌋₊

def thinHighLeftItems (n : ℕ) : Finset (ℕ × ℕ) :=
  extendedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep

end

end B13BoundedStepProductSavingProof

end

/- Outer left window budget -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

set_option maxHeartbeats 2100000 in
theorem norm_divided_prefix_le {n m g e k l₀ r₀ num : ℕ}
    (m0 : 0 < m) (mN : m ≤ n)
    (mLower : (n : ℝ)^(171/512 : ℝ) ≤ (m : ℝ)) (mUpper : (m : ℝ) ≤ (n : ℝ)^(515/1024 : ℝ))
    (charTop : m.gcd n ≤ targetDivisorCap n)
    (rUpper : r₀ ≤ n) (rProd : r₀*m ≤ expandedHyperbolaProductCap n)
    (lLower : subcriticalMediumProductCap n/m ≤ l₀)
    (gpos : 0 < g) (gn : g ∣ n) (gm : g ∣ m) (gSmall : g ≤ thinHighGcdCap n)
    (e0 : 0 < e) (eg : e ∣ g) (hk : k ∈ Icc 16 63)
    (ns : 1 < n) (numN : num ≤ n/g)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖moderateLowDividedHyperbolaPrefix n m g e k l₀ r₀ num‖ ≤
      592*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3/(m : ℝ) := by
  let v := m/g
  let N := (n : ℝ)
  let M := (m : ℝ)
  let V := (v : ℝ)
  let G := (g : ℝ)
  let E := (e : ℝ)
  let y := (k : ℝ)/256
  let x := y-1/512
  let A := primeHyperbolaFactorFloor n (k+1)/e
  let aLo := primeHyperbolaFactorLo n k
  let S := moderateLowDividedHyperbolaCofactorCap n r₀ g e k
  let I := expandedHighDividedHyperbolaFactors n m g e k
  let J := intIntervalModUnits v 0 S
  let mLo := l₀
  let mHi := r₀
  let l := mLo/g
  let r := mHi/g
  let L := logBudget n
  let α (a : ℕ) : ℂ := leftBandMoebius n (e*a)
  let β (j : ℤ) : ℂ := leftBilinearFactor n ((g/e)*j.toNat)
  have v0 : 0 < v := Nat.div_pos (Nat.le_of_dvd m0 gm) gpos
  let _ : NeZero v := ⟨v0.ne'⟩
  have vprod : v*g=m := Nat.div_mul_cancel gm
  have npNat : 0 < n := zero_lt_one.trans ns
  have nr : 1 < N := show (1 : ℝ) < (n : ℝ) from by exact_mod_cast ns
  have np : 0 < N := zero_lt_one.trans nr
  have gp : 0 < G := show (0 : ℝ) < (g : ℝ) from by exact_mod_cast gpos
  have G1 : 1 ≤ G := show (1 : ℝ) ≤ (g : ℝ) from by exact_mod_cast gpos
  have vN : v ≤ n := (by simpa only [mul_one] using Nat.mul_le_mul_left v (show 1 ≤ g from gpos) : v ≤ v*g).trans
    (by rw [vprod]; exact mN)
  have vEq : V*G=M := by
    change (v : ℝ)*(g : ℝ) = (m : ℝ)
    exact_mod_cast vprod
  have castGcd : (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ N^(1/128 : ℝ) := by
    have vd : v ∣ m := ⟨g,vprod.symm⟩
    have nd : n/g ∣ n := ⟨g,(Nat.div_mul_cancel gn).symm⟩
    have d : v.gcd (n/g) ∣ m.gcd n := Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans vd) ((Nat.gcd_dvd_right _ _).trans nd)
    have relation := (gcd_val_nat_cast_le_gcd (m := v) (n/g)).trans
      ((Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ npNat) d).trans charTop)
    exact (show (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ (targetDivisorCap n : ℝ) by
      exact_mod_cast relation).trans (Nat.floor_le (by positivity))
  have vTop : V ≤ N^(515/1024 : ℝ) := by
    have h : V ≤ M := by
      rw [← vEq]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left G1 (by positivity : 0 ≤ V)
    exact h.trans mUpper
  have gStrict : G ≤ N^(1/4096 : ℝ) :=
    (show G ≤ (thinHighGcdCap n : ℝ) by
      change (g : ℝ) ≤ (thinHighGcdCap n : ℝ)
      exact_mod_cast gSmall).trans (Nat.floor_le (by positivity))
  have gCap : G ≤ N^(1/512 : ℝ) :=
    gStrict.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by norm_num))
  have eCap : E ≤ N^(1/512 : ℝ) :=
    (by exact_mod_cast Nat.le_of_dvd gpos eg : (e : ℝ) ≤ g).trans gCap
  have vLo : N^(1/3 : ℝ) < V := by
    apply (mul_lt_mul_iff_left₀ gp).mp
    calc
      _ ≤ N^(1/3 : ℝ)*N^(1/4096 : ℝ) := mul_le_mul_of_nonneg_left gStrict (by positivity)
      _ < N^(171/512 : ℝ) := by
        rw [← Real.rpow_add np]
        exact Real.rpow_lt_rpow_of_exponent_lt nr (by norm_num)
      _ ≤ M := mLower
      _ = _ := vEq.symm
  have kmin : (16 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
  have kmax : (k : ℝ) ≤ 63 := by exact_mod_cast (mem_Icc.mp hk).2
  have xLo : 31/512 ≤ x := by unfold x y; linarith
  have xHi : x ≤ 1/4 := by unfold x y; linarith
  have aFormula : primeHyperbolaFactorFloor n (k+1) = ⌊N^(x+3/512)⌋₊ := by
    unfold primeHyperbolaFactorFloor N x y
    rw [Nat.cast_add,Nat.cast_one,add_div]
    congr 2
    ring
  have aCap : (A : ℝ) ≤ N^(x+3/512) :=
    (by exact_mod_cast Nat.div_le_self (primeHyperbolaFactorFloor n (k+1)) e :
      (A : ℝ) ≤ (primeHyperbolaFactorFloor n (k+1) : ℝ)).trans (by rw [aFormula]; exact Nat.floor_le (by positivity))
  have A1 : 0 < A := by
    change 1 ≤ primeHyperbolaFactorFloor n (k+1)/e
    apply (Nat.le_div_iff_mul_le e0).mpr
    rw [one_mul,aFormula]
    exact Nat.le_floor (eCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by linarith)))
  have aQ : (A : ℝ) ≤ N^(1/4 : ℝ) :=
    aCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by unfold x y; linarith))
  have Av : A < v := by
    have h := aQ.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt nr (by norm_num : (1/4 : ℝ) < 1/3)).trans vLo)
    change (A : ℝ) < (v : ℝ) at h
    exact_mod_cast h
  have Icap : I ⊆ Icc 1 A := by
    intro a ha
    have h := mem_Ioc.mp (mem_filter.mp ha).1
    exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt h.1,h.2.trans (Nat.div_le_div_right (min_le_right (lowCut n) _))⟩
  have copI (a : ℕ) (ha : a ∈ I) : a.Coprime v := (mem_filter.mp ha).2.2
  have rN : mHi ≤ n := rUpper
  have rG : r*g ≤ mHi := Nat.div_mul_le_self mHi g
  have sR : S ≤ r := Nat.div_le_self _ _
  have rp : r*v*g^2 ≤ expandedHyperbolaProductCap n := calc
    _ = (r*g)*(v*g) := by ring
    _ = (r*g)*m := by rw [vprod]
    _ ≤ mHi*m := Nat.mul_le_mul_right m rG
    _ ≤ _ := rProd
  have rCap : (r : ℝ)*V*G^2 ≤ 2*N^(513/512 : ℝ) := by
    calc
      _ ≤ (expandedHyperbolaProductCap n : ℝ) := by
        change (r : ℝ)*(v : ℝ)*(g : ℝ)^2 ≤ (expandedHyperbolaProductCap n : ℝ)
        exact_mod_cast rp
      _ ≤ _ := by
        unfold expandedHyperbolaProductCap
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
  have cofactorFloor : N^x ≤ (aLo/e : ℕ)+1 := by
    have more : aLo < (aLo/e+1)*e := (Nat.div_lt_iff_lt_mul e0).mp (Nat.lt_succ_self _)
    have rank : (primeHyperbolaFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*E := by
      have le : primeHyperbolaFactorFloor n k+1 ≤ (aLo/e+1)*e :=
        Nat.succ_le_of_lt ((le_max_right _ _).trans_lt more)
      change (primeHyperbolaFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*(e : ℝ)
      exact_mod_cast le
    have ground : N^y ≤ (((aLo/e : ℕ) : ℝ)+1)*E := (Nat.lt_floor_add_one (N^y)).le.trans rank
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (1/512 : ℝ))).mp
    calc
      _ = N^y := by rw [← Real.rpow_add np]; unfold x; simp
      _ ≤ (((aLo/e : ℕ) : ℝ)+1)*E := ground
      _ ≤ _ := mul_le_mul_of_nonneg_left eCap (by positivity)
  have sCap : (S : ℝ)*V*G^2 ≤ 2*N^(513/512-x) := by
    have cut : S*(aLo/e+1) ≤ r := Nat.div_mul_le_self r (aLo/e+1)
    have scaled : (S : ℝ)*(((aLo/e : ℕ) : ℝ)+1) ≤ (r : ℝ) := by exact_mod_cast cut
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np x)).mp
    calc
      _ ≤ ((S : ℝ)*V*G^2)*(((aLo/e : ℕ) : ℝ)+1) :=
        mul_le_mul_of_nonneg_left cofactorFloor (by positivity)
      _ = ((S : ℝ)*(((aLo/e : ℕ) : ℝ)+1))*V*G^2 := by ring
      _ ≤ (r : ℝ)*V*G^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right scaled (by positivity)) (by positivity)
      _ ≤ 2*N^(513/512 : ℝ) := rCap
      _ = (2*N^(513/512-x))*N^x := by rw [mul_assoc,← Real.rpow_add np,sub_add_cancel]
  have endCap : num/(l+1) ≤ ⌊V*G*N^(1/256 : ℝ)⌋₊ := by
    have endOrig := prime_hyperbola_endpoint_cap_of_size npNat m0 lLower (le_rfl : n ≤ n)
    have s : mLo+1 ≤ (l+1)*g := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul gpos).mp (Nat.lt_succ_self (mLo/g)))
    rw [vEq]
    calc
      _ ≤ (n/g)/(l+1) := Nat.div_le_div_right numN
      _ = n/((l+1)*g) := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm g (l+1)]
      _ ≤ n/(mLo+1) := Nat.div_le_div_left s (Nat.succ_pos _)
      _ ≤ _ := endOrig
  have divN (z : ℕ) (h : z ≤ n) : (z.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ ns.le (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors z (h.trans nn)
  have divV (z : ℕ) (h : z ≤ 4*v^3) : (z.divisors.card : ℝ) ≤ T :=
    divisors z (h.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left vN 3)))
  have divR (z : ℕ) (h : z ≤ r) : (z.divisors.card : ℝ) ≤ T :=
    divN z (h.trans ((Nat.div_le_self _ _).trans rN))
  have aw (a : ℕ) (ha : a ∈ I) : ‖α a‖ ≤ T := by
    have h := (mem_Ioc.mp (mem_filter.mp ha).1).2
    have eLe : e*a ≤ lowCut n := by
      have h' := (Nat.le_div_iff_mul_le e0).mp h
      exact (by simpa only [Nat.mul_comm] using h'.trans (min_le_left _ _) : e*a ≤ lowCut n)
    have lowN : lowCut n ≤ n := by
      have h : (lowCut n : ℝ) ≤ (n : ℝ) :=
        (Nat.floor_le (by positivity)).trans (Real.rpow_le_self_of_one_le nr.le (by norm_num))
      exact_mod_cast h
    exact (norm_leftBandMoebius_le n _).trans (divN _ (eLe.trans lowN))
  have bw (j : ℤ) (hj : j ∈ J) : ‖β j‖ ≤ T*L := by
    have data : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod v) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    have jR : j.toNat ≤ r := (show j.toNat ≤ S by have := (mem_Ioc.mp data.1).2; omega).trans sR
    have h : (g/e)*j.toNat ≤ n := calc
      _ ≤ g*r := Nat.mul_le_mul (Nat.div_le_self g e) jR
      _ ≤ mHi := by simpa only [Nat.mul_comm] using rG
      _ ≤ _ := rN
    exact norm_left_bilinear_factor_bound h divN
  have logBound : 1+Real.log V ≤ L := by
    have pv : 0 < V := show (0 : ℝ) < (v : ℝ) from by exact_mod_cast v0
    have up : V ≤ (n : ℝ)+2 := by
      change (v : ℝ) ≤ (n : ℝ)+2
      exact_mod_cast vN.trans (by omega : n≤n+2)
    unfold L logBudget
    linarith only [Real.log_le_log pv up]
  have vHi : V ≤ N^(1/2+x/2-7/256) :=
    vTop.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by linarith only [xLo]))
  have vMid : V ≤ N^(5/8-x/3) :=
    vTop.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by linarith only [xHi]))
  have b := norm_expanded_modulus_ratio_hyperbola_le (m := v) (c := ((n/g : ℕ) : ZMod v)) (g := g)
    castGcd nr.le G1 T1 (one_le_logBudget n) vHi vMid vLo.le gCap xLo xHi logBound aCap sCap rCap endCap
    A1 Av I Icap copI α β aw bw divV divR
  change ‖moderateLowDividedHyperbolaPrefix n m g e k l₀ r₀ num‖ ≤ 592*N^(1023/1024 : ℝ)*T^3*L^3/M
  exact b.trans_eq (by rw [vEq])

end

end B13BoundedStepProductSavingProof

end

/- Outer left window -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail
open scoped Classical Finset

noncomputable section

set_option maxHeartbeats 2200000 in
def outerLeftWindow (n m b c g e k l₀ r₀ : ℕ) : ℂ :=
  let v := m/g
  moderateLowDividedHyperbolaPrefix n m g e k l₀ r₀ (n/g-v*(b+1)) -
    moderateLowDividedHyperbolaPrefix n m g e k l₀ r₀ (n/g-v*c-1)

set_option maxHeartbeats 2200000 in
theorem norm_divided_window_le {n m b c g e k l₀ r₀ : ℕ}
    (m0 : 0 < m) (mN : m ≤ n)
    (mLower : (n : ℝ)^(171/512 : ℝ) ≤ (m : ℝ)) (mUpper : (m : ℝ) ≤ (n : ℝ)^(515/1024 : ℝ))
    (charTop : m.gcd n ≤ targetDivisorCap n)
    (rUpper : r₀ ≤ n) (rProd : r₀*m ≤ expandedHyperbolaProductCap n)
    (lLower : subcriticalMediumProductCap n/m ≤ l₀)
    (gpos : 0 < g) (gn : g ∣ n) (gm : g ∣ m) (gSmall : g ≤ thinHighGcdCap n)
    (e0 : 0 < e) (eg : e ∣ g) (hk : k ∈ Icc 16 63)
    (ns : 1 < n) {T : ℝ} (T1 : 1 ≤ T)
    (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖outerLeftWindow n m b c g e k l₀ r₀‖ ≤
      1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3/(m : ℝ) := by
  unfold outerLeftWindow
  dsimp only
  refine (norm_sub_le _ _).trans ?_
  let v := m/g
  let lo := v*(b+1)
  let hi := v*c
  have h₁ := norm_divided_prefix_le (num := n/g-lo) m0 mN mLower mUpper
    charTop rUpper rProd lLower gpos gn gm gSmall e0 eg hk ns
    (Nat.sub_le (n/g) lo) T1 divisors
  have h₂ := norm_divided_prefix_le (num := n/g-hi-1) m0 mN mLower mUpper
    charTop rUpper rProd lLower gpos gn gm gSmall e0 eg hk ns
    ((Nat.sub_le (n/g-hi) 1).trans (Nat.sub_le (n/g) hi)) T1 divisors
  exact (add_le_add h₁ h₂).trans_eq (by ring)

end

end B13BoundedStepProductSavingProof

end

/- Expanded wide approx -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def expandedWideStepCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(511/768 : ℝ)⌋₊

theorem expanded_wide_step_pos {n : ℕ} (hn : 0 < n) : 0 < expandedWideStepCap n :=
  Nat.le_floor (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))

theorem expanded_wide_step_le {n : ℕ} (hn : 0 < n) : expandedWideStepCap n ≤ n :=
  Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num))

end

end B13BoundedStepProductSavingProof

end

/- Expanded residue layer -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

theorem extended_step_cap_le_expanded (n : ℕ) : extendedWideStepCap n ≤ expandedWideStepCap n := by
  rcases eq_or_ne n 0 with rfl | n0
  · norm_num [extendedWideStepCap,expandedWideStepCap,Real.zero_rpow]
  · apply Nat.floor_mono
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero n0) (by norm_num)

def expandedWaveItems (n : ℕ) {α : Type*} (I : Finset α) (u : α → ℕ) : Finset α :=
  I.filter fun i => u i ≤ expandedWideStepCap n

end

end B13BoundedStepProductSavingProof

end

/- Swapped high cofactor size -/
section

namespace B13BoundedStepProductSavingProof

noncomputable section

theorem scaled_long_cofactor_size_for_swapped_high {n p q A S d : ℕ} {x T : ℝ}
    (n1 : 1 ≤ (n : ℝ)) (p0 : (0 : ℝ) < p) (m1 : 1 ≤ ((p*q : ℕ) : ℝ)) (d1 : 1 ≤ (d : ℝ)) (T1 : 1 ≤ T)
    (mHi : ((p*q : ℕ) : ℝ) ≤ (n : ℝ)^(1/2 : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ ((p*q : ℕ) : ℝ))
    (qCap : (q : ℝ) ≤ (n : ℝ)^(1/512 : ℝ))
    (xLo : 15/4096 ≤ x) (xHi : x ≤ 1/3)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+9/32768))
    (cofactorCap : (S : ℝ)*((p*q : ℕ) : ℝ)*(d : ℝ)^2 ≤ 2*(n : ℝ)^(1-x)) :
    longCofactorSize (p*q) p A S T ≤
      24*T*(n : ℝ)^(2047/2048 : ℝ)/(((p*q : ℕ) : ℝ)*(d : ℝ)^(3/2 : ℝ)) := by
  let N := (n : ℝ)
  let P := ((p*q : ℕ) : ℝ)
  let Q := (q : ℝ)
  let B := (A : ℝ)
  let K := (S : ℝ)
  let D := (d : ℝ)
  let Y := K*P*D^2
  let X := Y^(3/4 : ℝ)
  let H := N^(2047/2048 : ℝ)
  have np : 0 < N := zero_lt_one.trans_le n1
  have pp : 0 < P := zero_lt_one.trans_le m1
  have dp : 0 < D := zero_lt_one.trans_le d1
  have B0 : 0 ≤ B := by positivity
  have Y0 : 0 ≤ Y := by unfold Y; positivity
  have T0 := zero_le_one.trans T1
  have Ahalf : B^(1/2 : ℝ) ≤ N^((x+9/32768)*(1/2)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow B0 aCap (by norm_num)
  have Aextra : B^(7/8 : ℝ) ≤ N^((x+9/32768)*(7/8)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow B0 aCap (by norm_num)
  have Phalf : P^(1/2 : ℝ) ≤ N^(1/4 : ℝ) := by
    have h := Real.rpow_le_rpow pp.le mHi (by norm_num : (0 : ℝ) ≤ 1/2)
    rw [← Real.rpow_mul np.le] at h
    norm_num at h ⊢
    exact h
  have Pthree : P^(3/8 : ℝ) ≤ N^(3/16 : ℝ) := by
    have h := Real.rpow_le_rpow pp.le mHi (by norm_num : (0 : ℝ) ≤ 3/8)
    rw [← Real.rpow_mul np.le] at h
    norm_num at h ⊢
    exact h
  have Pneg : P^(-1/8 : ℝ) ≤ N^(-1/24 : ℝ) := by
    have cmp := Real.rpow_le_rpow (by positivity : 0 ≤ N^(1/3 : ℝ)) mLo (by norm_num : (0 : ℝ) ≤ 1/8)
    rw [← Real.rpow_mul np.le] at cmp
    norm_num at cmp
    rw [show (-1/8 : ℝ) = -(1/8 : ℝ) by ring, show (-1/24 : ℝ) = -(1/24 : ℝ) by ring,
      Real.rpow_neg pp.le, Real.rpow_neg np.le]
    have cast : P = (p : ℝ)*(q : ℝ) := by unfold P; push_cast; rfl
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (by simpa only [cast] using cmp)
  have xCap : X ≤ 2*N^((1-x)*(3/4)) := by
    calc
      _ ≤ (2*N^(1-x))^(3/4 : ℝ) := Real.rpow_le_rpow Y0 cofactorCap (by norm_num)
      _ = (2 : ℝ)^(3/4 : ℝ)*N^((1-x)*(3/4)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity),Real.rpow_mul np.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by positivity)
  have e1 : X*P^(1/2 : ℝ)*B^(1/2 : ℝ) ≤ 2*H := by
    calc
      _ ≤ (2*N^((1-x)*(3/4)))*N^(1/4 : ℝ)*N^((x+9/32768)*(1/2)) := by gcongr
      _ = 2*N^((1-x)*(3/4)+1/4+(x+9/32768)*(1/2)) := by
        rw [Real.rpow_add np,Real.rpow_add np]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)
  have e2 : X*P^(3/8 : ℝ)*B^(7/8 : ℝ) ≤ 2*H := by
    calc
      _ ≤ (2*N^((1-x)*(3/4)))*N^(3/16 : ℝ)*N^((x+9/32768)*(7/8)) := by gcongr
      _ = 2*N^((1-x)*(3/4)+3/16+(x+9/32768)*(7/8)) := by
        rw [Real.rpow_add np,Real.rpow_add np]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)
  have qQuarter : Q^(1/4 : ℝ) ≤ N^(1/2048 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ Q) qCap (by norm_num : (0 : ℝ) ≤ 1/4)
    rw [← Real.rpow_mul np.le] at h
    norm_num at h ⊢
    exact h
  have e3 : 2*Y*Q^(1/4 : ℝ)*B^(1/2 : ℝ) ≤ 4*H := by
    calc
      _ ≤ 2*(2*N^(1-x))*N^(1/2048 : ℝ)*N^((x+9/32768)*(1/2)) := by gcongr
      _ = 4*N^((1-x)+1/2048+(x+9/32768)*(1/2)) := by rw [Real.rpow_add np,Real.rpow_add np]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)
  have e4 : 2*Y*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ) ≤ 4*H := by
    calc
      _ ≤ 2*(2*N^(1-x))*N^(1/2048 : ℝ)*N^(-1/24 : ℝ)*N^((x+9/32768)*(7/8)) := by gcongr
      _ = 4*N^((1-x)+1/2048+(-1/24)+(x+9/32768)*(7/8)) := by
        rw [Real.rpow_add np ((1-x)+1/2048+(-1/24)), Real.rpow_add np ((1-x)+1/2048) (-1/24),
          Real.rpow_add np (1-x) (1/2048)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)

  have powerX : (K*P)^(3/4 : ℝ)*D^(3/2 : ℝ) = X := by
    unfold X Y
    have pow : (D^2)^(3/4 : ℝ) = D^(3/2 : ℝ) := by
      rw [← Real.rpow_natCast_mul dp.le 2]
      norm_num
    rw [Real.mul_rpow (by positivity : 0 ≤ K*P) (by positivity : 0 ≤ D^2),pow]
  have yd : (K*P)*D^(3/2 : ℝ) ≤ Y := by
    have dLe : D^(3/2 : ℝ) ≤ D^2 := calc
      _ ≤ D^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le d1 (by norm_num)
      _ = _ := by simpa only [Nat.cast_ofNat] using Real.rpow_natCast D 2
    exact mul_le_mul_of_nonneg_left dLe (by positivity)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < P*D^(3/2 : ℝ))).mpr
  change longCofactorSize (p*q) p A S T*(P*D^(3/2 : ℝ)) ≤ 24*T*H
  calc
    _ = (longCofactorSize (p*q) p A S T*P)*D^(3/2 : ℝ) := by ring
    _ ≤ (2*T*((K*P)^(3/4 : ℝ)*P^(1/2 : ℝ)*B^(1/2 : ℝ)+
      (K*P)^(3/4 : ℝ)*P^(3/8 : ℝ)*B^(7/8 : ℝ)+2*(K*P)*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+
        2*(K*P)*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ)))*D^(3/2 : ℝ) :=
      mul_le_mul_of_nonneg_right (long_cofactor_size_mul_modulus_le p0 m1 T1) (by positivity)
    _ = 2*T*(X*P^(1/2 : ℝ)*B^(1/2 : ℝ)+X*P^(3/8 : ℝ)*B^(7/8 : ℝ)+
        2*((K*P)*D^(3/2 : ℝ))*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+
        2*((K*P)*D^(3/2 : ℝ))*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ)) := by
      rw [← powerX]
      ring
    _ ≤ 2*T*(X*P^(1/2 : ℝ)*B^(1/2 : ℝ)+X*P^(3/8 : ℝ)*B^(7/8 : ℝ)+
        2*Y*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+2*Y*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ)) := by gcongr
    _ ≤ 2*T*(2*H+2*H+4*H+4*H) := by gcongr
    _ = _ := by ring

end

end B13BoundedStepProductSavingProof

end

/- Fourier majorant large divisor -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

theorem sum_interval_fourier_majorant_at_divisor_multiples_le {m d : ℕ} [NeZero m]
    (d0 : 0 < d) (dm : d ∣ m) :
    (∑ h ∈ ((univ : Finset (ZMod m)).filter (fun h => h ≠ 0)).filter (fun h => d ∣ h.val),
      (1/(2*(min h.val (m-h.val) : ℕ) : ℝ))) ≤ (1+Real.log m)/(d : ℝ) := by
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
      (1/(2*(min h.val (m-h.val) : ℕ) : ℝ)) ≤ ((1 : ℝ)/d)*C (f h) := by
    refine Eq.le ?_
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
        (add_le_add_right) (Real.log_le_log (by exact_mod_cast q0 : (0 : ℝ) < q)
          (by exact_mod_cast Nat.div_le_self m d : (q : ℝ) ≤ m)) 1
      calc
        _ ≤ ((1 : ℝ)/d)*(1+Real.log m) := mul_le_mul_of_nonneg_left cmp (by positivity)
        _ = _ := by ring

theorem sum_interval_fourier_majorant_with_large_gcd_le {m : ℕ} [NeZero m] (D : ℕ) :
    (∑ h ∈ ((univ : Finset (ZMod m)).filter (fun h => h ≠ 0)).filter (fun h => D < m.gcd h.val),
      (1/(2*(min h.val (m-h.val) : ℕ) : ℝ))) ≤
        (m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1) := by
  let H := (univ : Finset (ZMod m)).filter fun h => h ≠ 0
  let B := H.filter fun h => D < m.gcd h.val
  let J := m.divisors.filter fun d => D < d
  let F (h : ZMod m) := (1/(2*(min h.val (m-h.val) : ℕ) : ℝ))
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have L0 : 0 ≤ 1+Real.log (m : ℝ) := add_nonneg zero_le_one
    (Real.log_nonneg (by exact_mod_cast m0))
  have cover (h : ZMod m) (hh : h ∈ H) :
      (if D < m.gcd h.val then F h else 0) ≤ ∑ d ∈ J, if d ∣ h.val then F h else 0 := by
    by_cases hD : D < m.gcd h.val
    · let d := m.gcd h.val
      have dm : d ∈ J :=
        mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,m0.ne'⟩,hD⟩
      rw [ite_eq_left hD]
      have leading : ∀ a ∈ J, (0 : ℝ) ≤ (if a ∣ h.val then F h else 0) := by
        intro a ha
        split_ifs <;> positivity
      have dh : d ∣ h.val := Nat.gcd_dvd_right _ _
      exact (ite_eq_left dh).symm.le.trans (single_le_sum leading dm)
    · rw [ite_eq_right hD]
      exact sum_nonneg fun d _ => by split_ifs <;> positivity
  have each (d : ℕ) (hd : d ∈ J) :
      (∑ h ∈ H.filter (fun h => d ∣ h.val), F h) ≤ (1+Real.log m)/((D : ℝ)+1) := by
    obtain ⟨base,above⟩ := mem_filter.mp hd
    have dm := (Nat.mem_divisors.mp base).1
    have d0 : 0 < d := (Nat.zero_le _).trans_lt above
    have div_le : (D : ℝ)+1 ≤ (d : ℝ) := by exact_mod_cast Nat.succ_le_of_lt above
    exact (sum_interval_fourier_majorant_at_divisor_multiples_le d0 dm).trans
      (div_le_div_of_nonneg_left L0 (by positivity) div_le)
  change (∑ h ∈ B, F h) ≤ _
  unfold B
  rw [sum_filter]
  calc
    _ ≤ ∑ h ∈ H, ∑ d ∈ J, if d ∣ h.val then F h else 0 := sum_le_sum cover
    _ = ∑ d ∈ J, ∑ h ∈ H.filter (fun h => d ∣ h.val), F h := by
      rw [sum_comm]
      simp only [sum_filter]
    _ ≤ ∑ _ ∈ J, (1+Real.log (m : ℝ))/((D : ℝ)+1) := sum_le_sum each
    _ = (J.card : ℝ)*((1+Real.log (m : ℝ))/((D : ℝ)+1)) := by simp
    _ ≤ (m.divisors.card : ℝ)*((1+Real.log (m : ℝ))/((D : ℝ)+1)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card (filter_subset _ m.divisors)) (by positivity)
    _ = _ := by ring

end

end B13BoundedStepProductSavingProof

end

/- Variable initial segment fourier -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

theorem norm_gated_residue_of_short_index_endpoints {m : ℕ} [NeZero m]
    (D : ℕ) {c : ZMod m} {ι : Type*} (I : Finset ι)
    (a : ι → ZMod m) (units : ∀ i ∈ I, IsUnit (a i))
    (α : ι → ℂ) (β : ℤ → ℂ) (lo hi left right : ι → ℤ) {L R : ℤ}
    (ordered : ∀ i ∈ I, left i ≤ right i) {B : ℝ} (B0 : 0 ≤ B)
    (bound : ∀ h : ZMod m, h ≠ 0 → m.gcd h.val ≤ D →
      ∀ weight : ι → ℂ, (∀ i ∈ I, ‖weight i‖ ≤ ‖α i‖) →
      ‖gatedBilinearSum I (intIntervalModUnits m L R) weight β lo hi
        (fun i j => ZMod.stdAddChar ((-(h*c))*(a i)⁻¹*(j : ZMod m)⁻¹))‖ ≤ B) :
    let J := intIntervalModUnits m L R
    ‖gatedBilinearSum I J α β lo hi
        (fun i j => centeredIntIntervalResidue m (left i) (right i) (c*(a i*(j : ZMod m))⁻¹))‖ ≤
      (1+Real.log (m : ℕ))*B+
        ((m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1))*((∑ i ∈ I, ‖α i‖)*(∑ j ∈ J, ‖β j‖)) := by
  dsimp only
  let J := intIntervalModUnits m L R
  let H := (univ : Finset (ZMod m)).filter fun h => h ≠ 0
  let C (h : ZMod m) (i : ι) := intIntervalFourierCoefficient m (left i) (right i) h
  let f (h : ZMod m) (i : ι) (j : ℤ) := ZMod.stdAddChar ((-(h*c))*(a i)⁻¹*(j : ZMod m)⁻¹)
  let F (h : ZMod m) := gatedBilinearSum I J (fun i => α i*C h i) β lo hi (f h)
  let mass := (∑ i ∈ I, ‖α i‖)*(∑ j ∈ J, ‖β j‖)
  let δ (h : ZMod m) : ℝ := 1/(2*(min h.val (m-h.val) : ℕ) : ℝ)
  have mass0 : 0 ≤ mass := by unfold mass; positivity
  have majorant (h : ZMod m) (hs : h ≠ 0) (i : ι) : ‖C h i‖ ≤ δ h :=
    norm_int_interval_fourier_coefficient_le m (left i) (right i) hs
  have delta (h : ZMod m) (hs : h ≠ 0) : 0 < δ h := by
    have hp := lt_min (ZMod.val_pos.mpr hs) (Nat.sub_pos_of_lt (ZMod.val_lt h))
    unfold δ
    exact one_div_pos.mpr (mul_pos (by norm_num) (by exact_mod_cast hp))
  have point (i : ι) (hiI : i ∈ I) (j : ℤ) (hj : j ∈ J) :
      (if lo i < j ∧ j ≤ hi i then
        α i*centeredIntIntervalResidue m (left i) (right i) (c*(a i*(j : ZMod m))⁻¹) else 0) =
      ∑ h ∈ H, (if lo i < j ∧ j ≤ hi i then (α i*C h i)*f h i j else 0) := by
    by_cases gate : lo i < j ∧ j ≤ hi i
    · rw [ite_eq_left gate, centered_int_interval_residue_fourier m (ordered i hiI), mul_sum]
      have jun : IsUnit (j : ZMod m) := by
        have h : j ∈ Ioc L R ∧ IsUnit (j : ZMod m) := by
          simpa only [J,intIntervalModUnits,mem_filter] using hj
        exact h.2
      have prodInv : (a i*(j : ZMod m))⁻¹ = (a i)⁻¹*(j : ZMod m)⁻¹ := by
        apply ZMod.inv_eq_of_mul_eq_one
        calc
          _ = ((a i)*(a i)⁻¹)*((j : ZMod m)*(j : ZMod m)⁻¹) := by ring
          _ = _ := by rw [ZMod.mul_inv_of_unit _ (units i hiI),ZMod.mul_inv_of_unit _ jun,one_mul]
      have phase (h : ZMod m) : -(h*(c*(a i*(j : ZMod m))⁻¹)) = -(h*c)*(a i)⁻¹*(j : ZMod m)⁻¹ := by
        rw [prodInv]
        ring
      refine sum_congr rfl fun h _ => ?_
      rw [ite_eq_left gate,phase]
      unfold C f
      ring
    · simp [gate]
  have expansion : gatedBilinearSum I J α β lo hi
        (fun i j => centeredIntIntervalResidue m (left i) (right i) (c*(a i*(j : ZMod m))⁻¹)) = ∑ h ∈ H, F h := by
    calc
      _ = ∑ j ∈ J, β j*(∑ i ∈ I,∑ h ∈ H, if lo i < j ∧ j ≤ hi i then (α i*C h i)*f h i j else 0) := by
        unfold gatedBilinearSum
        refine sum_congr rfl fun j hj => congrArg (fun z : ℂ => β j*z) (sum_congr rfl fun i hiI => point i hiI j hj)
      _ = _ := by
        simp_rw [sum_comm (s := I) (t := H),mul_sum]
        rw [sum_comm]
        unfold F gatedBilinearSum
        simp only [mul_sum]
  have trivial (h : ZMod m) (hs : h ≠ 0) : ‖F h‖ ≤ δ h*mass := by
    unfold F gatedBilinearSum
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ j ∈ J, ‖β j‖*(∑ i ∈ I, δ h*‖α i‖) := by
        refine sum_le_sum fun j _ => ?_
        rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)) (norm_nonneg _)
        split_ifs
        · rw [norm_mul,norm_mul,norm_stdAddChar_eq_one,mul_one]
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (majorant h hs i) (norm_nonneg (α i))
        · simp [mul_nonneg (delta h hs).le (norm_nonneg (α i))]
      _ = _ := by
        unfold mass
        simp only [← mul_sum,← sum_mul]
        ring
  have good (h : ZMod m) (hs : h ≠ 0) (hg : m.gcd h.val ≤ D) : ‖F h‖ ≤ δ h*B := by
    let weights (i : ι) := (α i*C h i)/(δ h : ℂ)
    have positive := delta h hs
    have nonzero : (δ h : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
    have size (i : ι) (_ : i ∈ I) : ‖weights i‖ ≤ ‖α i‖ := by
      unfold weights
      rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
      exact (div_le_iff₀ positive).mpr (mul_le_mul_of_nonneg_left (majorant h hs i) (norm_nonneg _))
    have factor (i : ι) : (δ h : ℂ)*weights i=α i*C h i := by
      unfold weights
      field_simp
    have scale : F h = (δ h : ℂ)*gatedBilinearSum I J weights β lo hi (f h) := by
      unfold F gatedBilinearSum
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      have row : (∑ i ∈ I, if lo i < j ∧ j ≤ hi i then (α i*C h i)*f h i j else 0) =
          (δ h : ℂ)*(∑ i ∈ I, if lo i < j ∧ j ≤ hi i then weights i*f h i j else 0) := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        split_ifs
        · rw [← mul_assoc,factor]
        · simp
      rw [row]
      ring
    rw [scale,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
    exact mul_le_mul_of_nonneg_left (bound h hs hg weights size) positive.le
  have per (h : ZMod m) (hh : h ∈ H) :
      ‖F h‖ ≤ δ h*(B+if D < m.gcd h.val then mass else 0) := by
    have hs := (mem_filter.mp hh).2
    by_cases hd : D < m.gcd h.val
    · rw [ite_eq_left hd]
      exact (trivial h hs).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left B0) (delta h hs).le)
    · rw [ite_eq_right hd,add_zero]
      exact good h hs (le_of_not_gt hd)
  change ‖gatedBilinearSum I J α β lo hi
      (fun i j => centeredIntIntervalResidue m (left i) (right i) (c*(a i*(j : ZMod m))⁻¹))‖ ≤ _
  rw [expansion]
  calc
    _ ≤ ∑ h ∈ H, ‖F h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ H, δ h*(B+if D < m.gcd h.val then mass else 0) := sum_le_sum per
    _ = (∑ h ∈ H, δ h)*B+
        (∑ h ∈ H.filter (fun h => D < m.gcd h.val), δ h)*mass := by
      simp only [mul_add,sum_add_distrib]
      apply congrArg₂ (·+·)
      · exact (sum_mul ..).symm
      · calc
          _ = ∑ h ∈ H, if D < m.gcd h.val then δ h*mass else 0 := by
            refine sum_congr rfl fun h _ => ?_
            split_ifs <;> simp
          _ = _ := by rw [← sum_filter,sum_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (sum_inv_min_val_le m) B0)
      (mul_le_mul_of_nonneg_right (sum_interval_fourier_majorant_with_large_gcd_le D) mass0)

end

end B13BoundedStepProductSavingProof

end

/- Swapped high fixed residue -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

theorem norm_gated_swapped_high_fixed_endpoints_le {n m g A S : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(1/2 : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ))
    (xLo : 15/4096 ≤ x) (xHi : x ≤ 1/3) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+9/32768))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(1-x))
    (A0 : 0 < A) (Am : A < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi a b : ℕ → ℤ) (ab : ∀ i ∈ I, a i ≤ b i)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ T*L) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T)
    (divisors : ∀ z ≤ 4*m^3, (z.divisors.card : ℝ) ≤ T) :
    ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun i j => centeredIntIntervalResidue m (a i) (b i) (c*((i : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      98*(n : ℝ)^(2047/2048 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)^(3/2 : ℝ)) := by
  let N := (n : ℝ)
  let M := (m : ℝ)
  let G := (g : ℝ)
  let H := N^(2047/2048 : ℝ)
  let D := ⌊N^(1/1024 : ℝ)⌋₊
  let B := 96*H*T^3*L^2/(M*G^(3/2 : ℝ))
  let J := intIntervalModUnits m 0 S
  have np : 0 < N := zero_lt_one.trans_le n1
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have m1 : 1 ≤ M := show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast m0
  have mp : 0 < M := zero_lt_one.trans_le m1
  have gp : 0 < G := zero_lt_one.trans_le g1
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans L1
  have log0 := Real.log_nonneg m1
  have log2 : 2+Real.log (m : ℝ) ≤ 2*L := by linarith only [L1,logBound]
  have B0 : 0 ≤ B := by unfold B H; positivity
  have jProp (j : ℤ) (hj : j ∈ J) : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hj
  have uniform (h : ZMod m) (_ : h ≠ 0) (good : m.gcd h.val ≤ D)
      (weight : ℕ → ℂ) (wBound : ∀ i ∈ I, ‖weight i‖ ≤ ‖α i‖) :
      ‖gatedBilinearSum I J weight β lo hi
        (fun i j => ZMod.stdAddChar ((-(h*c))*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹))‖ ≤ B := by
    let z := -(h*c)
    let q := m.gcd z.val
    let p := inverseFrequencyPeriod m z
    have product : p*q=m := Nat.div_mul_cancel (Nat.gcd_dvd_left m z.val)
    have p0 : 0 < p := inverse_frequency_period_pos z
    have pr : (0 : ℝ) < p := by exact_mod_cast p0
    have a : (m.gcd h.val : ℝ) ≤ N^(1/1024 : ℝ) :=
      (by exact_mod_cast good : (m.gcd h.val : ℝ) ≤ (D : ℝ)).trans (Nat.floor_le (by positivity))
    have qCap : (q : ℝ) ≤ N^(1/512 : ℝ) := calc
      _ ≤ (m.gcd h.val : ℝ)*(m.gcd c.val : ℝ) := by
        change (m.gcd (-(h*c)).val : ℝ) ≤ _
        exact_mod_cast gcd_fourier_phase_product_le h c
      _ ≤ N^(1/1024 : ℝ)*N^(1/2048 : ℝ) := mul_le_mul a charBound (by positivity) (by positivity)
      _ ≤ _ := by rw [← Real.rpow_add np]; exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
    have long := scaled_long_cofactor_size_for_swapped_high (n := n) (p := p) (q := q) (A := A) (S := S)
      (d := g) (T := 2*T) n1 pr (by simpa only [product] using m1) g1 (by linarith)
      (by simpa only [product] using mHi) (by simpa only [product] using mLo) qCap xLo xHi aCap
      (by simpa only [product] using cofactorCap)
    have long' : longCofactorSize m p A S (2*T) ≤ 24*(2*T)*H/(M*G^(3/2 : ℝ)) := by
      simpa only [product,H,M,G] using long
    have long0 : 0 ≤ longCofactorSize m p A S (2*T) := by
      unfold longCofactorSize reciprocalBilinearBound inverseFibreBudget
      positivity
    have est := norm_gated_long_cofactor_inverse_le_with_reduced_period z (p := p) le_rfl p0 I J
      (fun j hj => (jProp j hj).1) (fun j hj => (jProp j hj).2) weight β lo hi (mul_nonneg T0 L0) T0
      (by positivity : 0 ≤ 2*T) (fun i hi => (wBound i hi).trans (aw i hi)) bw
      (fun weight {_} X0 xw => inverse_frequency_fourth_moment_composite_le A0 Am I Icap copI weight X0 xw T1 divisors)
    refine est.trans ?_
    calc
      _ ≤ (2*L)*(T*L)*T*(24*(2*T)*H/(M*G^(3/2 : ℝ))) := by gcongr
      _ = _ := by unfold B; ring
  have est := norm_gated_residue_of_short_index_endpoints D I (fun i => (i : ZMod m))
    (fun i hi => (ZMod.isUnit_iff_coprime _ _).mpr (copI i hi)) α β lo hi a b
    (L := 0) (R := (S : ℤ)) ab B0 uniform
  have lMass : (∑ i ∈ I, ‖α i‖) ≤ (A : ℝ)*(T*L) := calc
    _ ≤ ∑ _ ∈ I, T*L := sum_le_sum aw
    _ = (I.card : ℝ)*(T*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (card_le_card Icap).trans_eq (by simp [Nat.card_Icc])) (by positivity)
  have jSub : J ⊆ Ioc (0 : ℤ) (S : ℤ) := fun j hj => (jProp j hj).1
  have jSize : (J.card : ℝ) ≤ S := by
    exact_mod_cast (card_le_card jSub).trans_eq (by rw [Int.card_Ioc,sub_zero,Int.toNat_natCast])
  have rMass : (∑ j ∈ J, ‖β j‖) ≤ (S : ℝ)*T := calc
    _ ≤ ∑ _ ∈ J, T := sum_le_sum bw
    _ = (J.card : ℝ)*T := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right jSize (by positivity)
  have div_m : (m.divisors.card : ℝ) ≤ T := divisors m (by
    have h : m ≤ m^3 := by simpa only [pow_one] using pow_le_pow_right₀ m0 (show 1 ≤ 3 by decide)
    omega)
  have divisorFactor : (m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1) ≤ T*L/N^(1/1024 : ℝ) := by
    have d : N^(1/1024 : ℝ) ≤ (D : ℝ)+1 := (Nat.lt_floor_add_one (N^(1/1024 : ℝ))).le
    calc
      _ ≤ T*L/((D : ℝ)+1) := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) d
  have core : (A : ℝ)*(S : ℝ) ≤ 2*N^(1+9/32768 : ℝ)/(M*G^2) := by
    apply (le_div_iff₀ (by positivity : 0 < M*G^2)).mpr
    calc
      _ = (A : ℝ)*((S : ℝ)*M*G^2) := by ring
      _ ≤ N^(x+9/32768)*(2*N^(1-x)) := mul_le_mul aCap cofactorCap (by positivity) (by positivity)
      _ = _ := by
        have sum : N^(x+9/32768)*N^(1-x) = N^(1+9/32768 : ℝ) := by rw [← Real.rpow_add np]; congr 1; ring
        calc
          _ = 2*(N^(x+9/32768)*N^(1-x)) := by ring
          _ = _ := by rw [sum]
  have gpow : G^(3/2 : ℝ) ≤ G^2 := by
    rw [← Real.rpow_natCast G 2]
    exact Real.rpow_le_rpow_of_exponent_le g1 (by norm_num)
  have tail : ((m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1))*
       ((∑ i ∈ I, ‖α i‖)*(∑ j ∈ J, ‖β j‖)) ≤ 2*H*T^3*L^3/(M*G^(3/2 : ℝ)) := by
    calc
      _ ≤ (T*L/N^(1/1024 : ℝ))*(((A : ℝ)*(T*L))*((S : ℝ)*T)) := by gcongr
      _ = (T*L/N^(1/1024 : ℝ))*(((A : ℝ)*(S : ℝ))*T^2*L) := by ring
      _ ≤ (T*L/N^(1/1024 : ℝ))*((2*N^(1+9/32768 : ℝ)/(M*G^2))*T^2*L) := by gcongr
      _ = 2*N^(32745/32768 : ℝ)*T^3*L^2/(M*G^2) := by
        have pow : N^(1+9/32768 : ℝ)/N^(1/1024 : ℝ)=N^(32745/32768 : ℝ) := by rw [← Real.rpow_sub np]; norm_num
        rw [← pow]
        ring
      _ ≤ _ := by
        have h : N^(32745/32768 : ℝ) ≤ H := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        have l : L^2 ≤ L^3 := pow_le_pow_right₀ L1 (by decide)
        gcongr
  exact est.trans ((add_le_add (mul_le_mul_of_nonneg_right logBound B0) tail).trans_eq (by unfold B H; ring))

end

end B13BoundedStepProductSavingProof

end

/- Swapped high endpoint bucket -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

theorem swapped_high_endpoint_bucket_budget {n m g : ℕ}
    (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ)) :
    let cap := ⌊(m : ℝ)*(g : ℝ)*(n : ℝ)^(1/8192 : ℝ)⌋₊
    let d := ⌊(m : ℝ)*(n : ℝ)^(-1/32768 : ℝ)⌋₊
    0 < d ∧ ((cap/d+1 : ℕ) : ℝ) ≤ 3*(g : ℝ)*(n : ℝ)^(5/32768 : ℝ) ∧
      (d : ℝ)/(m : ℝ) ≤ (n : ℝ)^(-1/32768 : ℝ) := by
  dsimp only
  let N := (n : ℝ)
  let P := (m : ℝ)
  let G := (g : ℝ)
  let cap := ⌊P*G*N^(1/8192 : ℝ)⌋₊
  let d := ⌊P*N^(-1/32768 : ℝ)⌋₊
  have np : 0 < N := zero_lt_one.trans_le n1
  have pp : 0 < P := (Real.rpow_pos_of_pos np _).trans_le mLo
  have gp : 0 < G := zero_lt_one.trans_le g1
  have v1 : 1 ≤ P*N^(-1/32768 : ℝ) := calc
    1 ≤ N^(1/3-1/32768 : ℝ) := Real.one_le_rpow n1 (by norm_num)
    _ = N^(1/3 : ℝ)*N^(-1/32768 : ℝ) := by rw [sub_eq_add_neg,Real.rpow_add np]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right mLo (by positivity)
  have d1 : 1 ≤ d := Nat.le_floor v1
  have dp : (0 : ℝ) < d := by exact_mod_cast d1
  have low : P*N^(-1/32768 : ℝ) ≤ 2*(d : ℝ) := by
    have dR : (1 : ℝ) ≤ d := by exact_mod_cast d1
    have fl := Nat.lt_floor_add_one (P*N^(-1/32768 : ℝ))
    change P*N^(-1/32768 : ℝ) < (d : ℝ)+1 at fl
    linarith only [dR,fl]
  have upper : (d : ℝ) ≤ P*N^(-1/32768 : ℝ) := Nat.floor_le (by positivity)
  have capUp : (cap : ℝ) ≤ P*G*N^(1/8192 : ℝ) := Nat.floor_le (by positivity)
  have divided : ((cap/d : ℕ) : ℝ) ≤ (cap : ℝ)/(d : ℝ) :=
    (le_div_iff₀ dp).mpr (by exact_mod_cast Nat.div_mul_le_self cap d)
  have est : (cap : ℝ) ≤ (2*G*N^(5/32768 : ℝ))*(d : ℝ) := calc
    _ ≤ P*G*N^(1/8192 : ℝ) := capUp
    _ = (G*N^(5/32768 : ℝ))*(P*N^(-1/32768 : ℝ)) := by
      have r : N^(5/32768 : ℝ)*N^(-1/32768 : ℝ) = N^(1/8192 : ℝ) := by rw [← Real.rpow_add np]; norm_num
      calc
        _ = P*G*(N^(5/32768 : ℝ)*N^(-1/32768 : ℝ)) := by rw [r]
        _ = _ := by ring
    _ ≤ (G*N^(5/32768 : ℝ))*(2*(d : ℝ)) := mul_le_mul_of_nonneg_left low (by positivity)
    _ = _ := by ring
  have q := divided.trans ((div_le_iff₀ dp).mpr est)
  have one : 1 ≤ G*N^(5/32768 : ℝ) := one_le_mul_of_one_le_of_one_le g1 (Real.one_le_rpow n1 (by norm_num))
  refine ⟨d1,?_,(div_le_iff₀ pp).mpr (by simpa only [mul_comm] using upper)⟩
  change ((cap/d+1 : ℕ) : ℝ) ≤ 3*G*N^(5/32768 : ℝ)
  push_cast
  linarith only [q,one]

end

end B13BoundedStepProductSavingProof

end

/- Gated product ratio window -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

private theorem cofactor_gate_iff_product_interval {a l r : ℕ} (ha : 0 < a) {j : ℤ} (hj : 0 ≤ j) :
    (((l/a : ℕ) : ℤ) < j ∧ j ≤ ((r/a : ℕ) : ℤ)) ↔ l < a*j.toNat ∧ a*j.toNat ≤ r := by
  have cast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
  rw [← cast]
  simp only [Int.ofNat_lt, Int.ofNat_le, Nat.div_lt_iff_lt_mul ha, Nat.le_div_iff_mul_le ha,
    Nat.mul_comm j.toNat a, Int.toNat_natCast]

private theorem quotient_bucket_iff_endpoints {m d k : ℕ} (hd : 0 < d) :
    m/d = k ↔ k*d ≤ m ∧ m < (k+1)*d := by
  rw [← Nat.le_div_iff_mul_le hd, ← Nat.div_lt_iff_lt_mul hd]
  omega

private def gatedWindowStepLo (N l d k : ℕ) : ℕ := max l (N/((k+1)*d))

private def gatedWindowStepHi (N r d k : ℕ) : ℕ := min r (if k = 0 then r else N/(k*d))

private theorem gated_window_step_iff {N l r d k x : ℕ} (hd : 0 < d) (hx : 0 < x) :
    (gatedWindowStepLo N l d k < x ∧ x ≤ gatedWindowStepHi N r d k) ↔
      (l < x ∧ x ≤ r) ∧ (N/x)/d = k := by
  have left : N/((k+1)*d) < x ↔ N/x < (k+1)*d := by
    rw [Nat.div_lt_iff_lt_mul (mul_pos (by omega) hd), Nat.div_lt_iff_lt_mul hx, Nat.mul_comm x]
  have right (hk : k ≠ 0) : x ≤ N/(k*d) ↔ k*d ≤ N/x := by
    rw [Nat.le_div_iff_mul_le (mul_pos (Nat.pos_of_ne_zero hk) hd), Nat.le_div_iff_mul_le hx,
      Nat.mul_comm x]
  unfold gatedWindowStepLo gatedWindowStepHi
  rw [max_lt_iff, le_min_iff, left, quotient_bucket_iff_endpoints hd]
  by_cases hk : k = 0
  · simp only [hk, ite_true, zero_mul, Nat.zero_le, true_and]
    tauto
  · simp only [ite_eq_right hk, right hk]
    tauto

theorem norm_gated_product_interval_le_of_ratio_window {num p : ℕ}
    (I : Finset ℕ) (J : Finset ℤ) (α : ℕ → ℂ) (β : ℤ → ℂ) (f : ℕ → ℤ → ℂ) (baseLo baseHi : ℕ → ℤ)
    (apos : ∀ a ∈ I, 0 < a) (jpos : ∀ j ∈ J, 0 < j)
    {l r d endpointCap : ℕ} (hd : 0 < d)
    (cap : num/(l+1) ≤ endpointCap) {Q : ℝ}
    (windowEstimate : ∀ (g h : ℕ → ℤ) {b u : ℤ}, 0 ≤ b → b ≤ u →
      (∀ a ∈ I, ∀ j ∈ J, g a < j ∧ j ≤ h a →
        l+1 ≤ a*j.toNat ∧
          b ≤ (num : ℤ)/((a*j.toNat : ℕ) : ℤ) ∧
          (num : ℤ)/((a*j.toNat : ℕ) : ℤ) ≤ u) →
      ‖∑ j ∈ J, ∑ a ∈ I, if g a < j ∧ j ≤ h a then f a j else 0‖ ≤
        Q + (2*(((u-b : ℤ) : ℝ)/(p : ℝ))) *
          (∑ j ∈ J, ‖β j‖*∑ a ∈ I, if g a < j ∧ j ≤ h a then ‖α a‖ else 0)) :
    let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (baseLo a)
    let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (baseHi a)
    ‖∑ j ∈ J, ∑ a ∈ I, if lo a < j ∧ j ≤ hi a then f a j else 0‖ ≤
      ((endpointCap/d+1 : ℕ) : ℝ)*Q+(2*((d : ℝ)/(p : ℝ))) *
        (∑ j ∈ J, ‖β j‖*∑ a ∈ I, if lo a < j ∧ j ≤ hi a then ‖α a‖ else 0) := by
  dsimp only
  let K := range (endpointCap/d+1)
  let N := num
  let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (baseLo a)
  let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (baseHi a)
  let loK (k a : ℕ) : ℤ := max ((gatedWindowStepLo N l d k/a : ℕ) : ℤ) (baseLo a)
  let hiK (k a : ℕ) : ℤ := min ((gatedWindowStepHi N r d k/a : ℕ) : ℤ) (baseHi a)
  let B (a : ℕ) (j : ℤ) := N/(a*j.toNat)
  let V (k : ℕ) := ∑ j ∈ J, ∑ a ∈ I, if loK k a < j ∧ j ≤ hiK k a then f a j else 0
  let mass (f g : ℕ → ℤ) : ℝ :=
    ∑ j ∈ J, ‖β j‖*∑ a ∈ I, if f a < j ∧ j ≤ g a then ‖α a‖ else 0
  let D : ℝ := 2*((d : ℝ)/(p : ℝ))
  have jp {j : ℤ} (hj : j ∈ J) : 0 < j := jpos j hj
  have step_pos {a : ℕ} {j : ℤ} (ha : a ∈ I) (hj : j ∈ J) : 0 < a*j.toNat := by
    have jn : 0 < j.toNat := by have := jp hj; omega
    exact mul_pos (apos a ha) jn
  have gate {a : ℕ} {j : ℤ} (ha : a ∈ I) (hj : j ∈ J) :
      (lo a < j ∧ j ≤ hi a) ↔ (l < a*j.toNat ∧ a*j.toNat ≤ r) ∧ (baseLo a < j ∧ j ≤ baseHi a) := by
    have core := cofactor_gate_iff_product_interval (l := l) (r := r) (apos a ha) (jp hj).le
    simp only [lo,hi,max_lt_iff,le_min_iff]
    tauto
  have gateK (k : ℕ) {a : ℕ} {j : ℤ} (ha : a ∈ I) (hj : j ∈ J) :
      (loK k a < j ∧ j ≤ hiK k a) ↔ (lo a < j ∧ j ≤ hi a) ∧ B a j / d = k := by
    rw [gate ha hj]
    have core := (cofactor_gate_iff_product_interval (l := gatedWindowStepLo N l d k)
      (r := gatedWindowStepHi N r d k) (apos a ha) (jp hj).le).trans
      (gated_window_step_iff hd (step_pos ha hj))
    simp only [loK,hiK,max_lt_iff,le_min_iff,B]
    tauto
  have Bbound {a : ℕ} {j : ℤ} (ha : a ∈ I) (hj : j ∈ J) (h : lo a < j ∧ j ≤ hi a) :
      B a j ≤ endpointCap := by
    have step : l+1 ≤ a*j.toNat := Nat.succ_le_of_lt ((gate ha hj).mp h).1.1
    exact (Nat.div_le_div_left step (Nat.succ_pos _)).trans cap
  have splitSum {R : Type} [AddCommMonoid R] (f : ℕ → ℤ → R) :
      (∑ j ∈ J, ∑ a ∈ I, if lo a < j ∧ j ≤ hi a then f a j else 0) =
        ∑ k ∈ K, ∑ j ∈ J, ∑ a ∈ I, if loK k a < j ∧ j ≤ hiK k a then f a j else 0 := by
    rw [sum_comm (s := K) (t := J)]
    refine sum_congr rfl fun j hj => ?_
    rw [sum_comm (s := K) (t := I)]
    refine sum_congr rfl fun a ha => ?_
    simp_rw [gateK _ ha hj]
    by_cases h : lo a < j ∧ j ≤ hi a
    · have mem : B a j/d ∈ K := by
        apply mem_range.mpr
        exact Nat.lt_succ_of_le (Nat.div_le_div_right (Bbound ha hj h))
      simp only [h, true_and, ite_true, sum_ite_eq, mem]
    · simp [h]
  have sumV : (∑ j ∈ J, ∑ a ∈ I, if lo a < j ∧ j ≤ hi a then f a j else 0) = ∑ k ∈ K, V k :=
    splitSum f
  have mass_repr (f g : ℕ → ℤ) :
      mass f g = ∑ j ∈ J, ∑ a ∈ I, if f a < j ∧ j ≤ g a then ‖β j‖*‖α a‖ else 0 := by
    unfold mass
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  have sumMass : mass lo hi = ∑ k ∈ K, mass (loK k) (hiK k) := by
    simp only [mass_repr]
    exact splitSum _
  have window (k : ℕ) : ‖V k‖ ≤ Q+D*mass (loK k) (hiK k) := by
    have order : ((k*d : ℕ) : ℤ) ≤ (((k+1)*d : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_right d (Nat.le_succ k)
    have lower0 : 0 ≤ ((k*d : ℕ) : ℤ) := by positivity
    have est := windowEstimate (loK k) (hiK k) lower0 order (fun a ha j hj h => ?_)
    · have delta : ((((k+1)*d : ℕ) : ℤ)-((k*d : ℕ) : ℤ) : ℤ) = d := by
        push_cast
        ring
      simpa only [V, D, mass, delta, Int.cast_natCast] using est
    · obtain ⟨orig,eq⟩ := (gateK k ha hj).mp h
      have hx : l+1 ≤ a*j.toNat := Nat.succ_le_of_lt ((gate ha hj).mp orig).1.1
      have castB : (B a j : ℤ) = (num : ℤ)/((a*j.toNat : ℕ) : ℤ) := by
        unfold B N
        rw [Int.natCast_ediv]
      obtain ⟨lb,ub⟩ := (quotient_bucket_iff_endpoints hd).mp eq
      rw [←castB]
      exact ⟨hx, by exact_mod_cast lb, by exact_mod_cast ub.le⟩
  change ‖∑ j ∈ J, ∑ a ∈ I, if lo a < j ∧ j ≤ hi a then f a j else 0‖ ≤ ((endpointCap/d+1 : ℕ) : ℝ)*Q+D*mass lo hi
  rw [sumV]
  calc
    _ ≤ ∑ k ∈ K, ‖V k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ K, (Q+D*mass (loK k) (hiK k)) := sum_le_sum fun k _ => window k
    _ = _ := by
      rw [sum_add_distrib]
      have dm : (∑ k ∈ K, D*mass (loK k) (hiK k)) = D*mass lo hi := by rw [← mul_sum, ← sumMass]
      rw [dm]
      simp [K]

end

end B13BoundedStepProductSavingProof

end

/- Swapped high ratio hyperbola -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

set_option maxHeartbeats 1500000 in
theorem norm_swapped_high_ratio_hyperbola_le {n m g A S num l r : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(1/2 : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ))
    (gCap : (g : ℝ) ≤ (n : ℝ)^(1/4096 : ℝ))
    (xLo : 15/4096 ≤ x) (xHi : x ≤ 1/3) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+9/32768))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(1-x))
    (rCap : (r : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ))
    (endCap : num/(l+1) ≤ ⌊(m : ℝ)*(g : ℝ)*(n : ℝ)^(1/8192 : ℝ)⌋₊)
    (A0 : 0 < A) (Am : A < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (baseLo baseHi : ℕ → ℤ)
    (aw : ∀ a ∈ I, ‖α a‖ ≤ T*L) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T)
    (divisors : ∀ z ≤ 4*m^3, (z.divisors.card : ℝ) ≤ T)
    (dR : ∀ z ≤ r, (z.divisors.card : ℝ) ≤ T) :
    let J := intIntervalModUnits m 0 S
    let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (baseLo a)
    let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (baseHi a)
    ‖gatedBilinearSum I J α β lo hi
        (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
          (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      592*(n : ℝ)^(32767/32768 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)) := by
  dsimp only
  let P := (m : ℝ)
  let N := (n : ℝ)
  let G := (g : ℝ)
  let C := G^(1/2 : ℝ)
  let H := N^(32767/32768 : ℝ)
  let J := intIntervalModUnits m 0 S
  let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (baseLo a)
  let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (baseHi a)
  let R := 98*N^(2047/2048 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ))
  let d := ⌊P*N^(-1/32768 : ℝ)⌋₊
  let cap := ⌊P*G*N^(1/8192 : ℝ)⌋₊
  have m1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have pp : 0 < P := zero_lt_one.trans_le m1
  have np : 0 < N := zero_lt_one.trans_le n1
  have gp : 0 < G := zero_lt_one.trans_le g1
  have cp : 0 < C := by unfold C; positivity
  have t0 := zero_le_one.trans T1
  have l0 := zero_le_one.trans L1
  have log0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg m1
  have R0 : 0 ≤ R := by unfold R; positivity
  have bound : R ≤ 98*N^(2047/2048 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ)) := le_rfl
  obtain ⟨d0,dcount,dsmall⟩ := swapped_high_endpoint_bucket_budget n1 g1 mLo
  have rUp : (r : ℝ) ≤ 2*N/(P*G^2) := (le_div_iff₀ (by positivity)).mpr (by
    have h := rCap
    change (r : ℝ)*P*G^2 ≤ 2*N at h
    convert h using 1
    ring)
  have jPos (j : ℤ) (hj : j ∈ J) : 0 < j := by
    have data : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    exact (mem_Ioc.mp data.1).1
  let mass := ∑ j ∈ J, ‖β j‖*∑ a ∈ I, if lo a < j ∧ j ≤ hi a then ‖α a‖ else 0
  have mass0 : 0 ≤ mass := by
    unfold mass
    exact sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (sum_nonneg fun a _ => by split_ifs <;> positivity)
  have massCut : mass ≤ (2*N/(P*G^2))*T^3*L := by
    have b := gated_left_weight_mass_le α β lo hi (mul_nonneg t0 l0) t0
      (fun u hu => dR u (mem_Icc.mp hu).2) (fun a ha => (mem_Icc.mp (Icap ha)).1)
      (fun j hj => (jPos j hj).le) (fun a ha j hj active => ?_) aw bw
    · refine b.trans ?_
      calc
        _ ≤ (2*N/(P*G^2))*T*(T*L)*T := by gcongr
        _ = _ := by ring
    · have ja : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (jPos j hj).le
      have jR : j.toNat ≤ r/a := by
        have h : (j.toNat : ℤ) ≤ ((r/a : ℕ) : ℤ) := by rw [ja]; exact active.2.trans (min_le_left _ _)
        exact_mod_cast h
      have ap := (mem_Icc.mp (Icap ha)).1
      have jn : 0 < j.toNat := by have := jPos j hj; omega
      exact mem_Icc.mpr ⟨mul_pos ap jn,by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ap).mp jR⟩
  have est : ‖gatedBilinearSum I J α β lo hi
      (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
        (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
          ((cap/d+1 : ℕ) : ℝ)*(2*R)+(2*((d : ℝ)/P))*mass := by
    let phase (a : ℕ) (j : ℤ) := c*((a : ZMod m)*(j : ZMod m))⁻¹
    let e (a : ℕ) (j : ℤ) := (num : ℤ)/((a*j.toNat : ℕ) : ℤ)
    rw [gated_bilinear_sum_eq_pair_sum]
    refine norm_gated_product_interval_le_of_ratio_window (num := num) (p := m) I J α β _ baseLo baseHi (fun a ha => (mem_Icc.mp (Icap ha)).1)
      jPos d0 endCap ?_
    intro u v b t vb bt bracket
    rw [← gated_bilinear_sum_eq_pair_sum]
    refine norm_gated_residue_variable_endpoint_le m I J α β u v vb bt phase e
      (fun a ha j hj gate => (bracket a ha j hj gate).2) ?_ ?_
    · exact norm_gated_swapped_high_fixed_endpoints_le charBound n1 g1 T1 L1 mHi mLo xLo xHi
        logBound aCap cofactorCap A0 Am I Icap copI α β u v (fun _ => 0) (fun _ => b) (fun _ _ => vb) aw bw divisors
    · apply norm_gated_swapped_high_fixed_endpoints_le charBound n1 g1 T1 L1 mHi mLo xLo xHi
        logBound aCap cofactorCap A0 Am I Icap copI _ _ u v (fun _ => b) (fun _ => t) (fun _ _ => bt) ?_ ?_ divisors
      · intro a ha
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (α a))] using aw a ha
      · intro j hj
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (β j))] using bw j hj
  have e1 : ((cap/d+1 : ℕ) : ℝ)*(2*R) ≤ 588*H*T^3*L^3/(P*G) := by
    have Ghalf : G^(3/2 : ℝ) = G*C := by
      unfold C
      rw [mul_comm G,← Real.rpow_add_one gp.ne']
      norm_num
    have CC : C^2 = G := by unfold C; rw [← Real.rpow_mul_natCast gp.le]; norm_num
    have cpow : C ≤ N^(1/8192 : ℝ) := by
      have b := Real.rpow_le_rpow gp.le gCap (by norm_num : (0 : ℝ) ≤ 1/2)
      rw [← Real.rpow_mul np.le] at b
      norm_num at b ⊢
      exact b
    calc
      _ ≤ (3*G*N^(5/32768 : ℝ))*(2*(98*N^(2047/2048 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ)))) := by gcongr
      _ = 588*N^(32757/32768 : ℝ)*T^3*L^3*C/(P*G) := by
        have add : N^(5/32768 : ℝ)*N^(2047/2048 : ℝ) = N^(32757/32768 : ℝ) := by
          rw [← Real.rpow_add np]
          norm_num
        calc
          _ = 588*(N^(5/32768 : ℝ)*N^(2047/2048 : ℝ))*T^3*L^3*G/(P*G^(3/2 : ℝ)) := by ring
          _ = _ := by
            have frac : G/(P*(G*C)) = C/(P*G) := by
              rw [← CC]
              field_simp [pp.ne',cp.ne']
            rw [add,Ghalf]
            calc
              _ = (588*N^(32757/32768 : ℝ)*T^3*L^3)*(G/(P*(G*C))) := by ring
              _ = _ := by rw [frac]; ring
      _ ≤ 588*N^(32757/32768 : ℝ)*T^3*L^3*N^(1/8192 : ℝ)/(P*G) := by gcongr
      _ ≤ _ := by
        have add : N^(32757/32768 : ℝ)*N^(1/8192 : ℝ) ≤ H := by
          unfold H
          rw [← Real.rpow_add np]
          exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        calc
          _ = 588*(N^(32757/32768 : ℝ)*N^(1/8192 : ℝ))*T^3*L^3/(P*G) := by ring
          _ ≤ _ := by gcongr
  have e2 : (2*((d : ℝ)/P))*mass ≤ 4*H*T^3*L^3/(P*G) := by
    have lg : L ≤ L^3 := by simpa only [pow_one] using pow_le_pow_right₀ L1 (show 1 ≤ 3 by decide)
    have pow : N^(-1/32768 : ℝ)*N = H := by unfold H; rw [← Real.rpow_add_one np.ne']; norm_num
    calc
      _ ≤ (2*N^(-1/32768 : ℝ))*((2*N/(P*G^2))*T^3*L) := by gcongr
      _ = 4*H*T^3*L/(P*G^2) := by
        calc
          _ = 4*(N^(-1/32768 : ℝ)*N)*T^3*L/(P*G^2) := by ring
          _ = _ := by rw [pow]
      _ ≤ 4*H*T^3*L^3/(P*G^2) := by gcongr
      _ ≤ _ := by
        have gPow : G ≤ G^2 := by simpa only [pow_one] using pow_le_pow_right₀ g1 (show 1 ≤ 2 by decide)
        gcongr
  exact est.trans ((add_le_add e1 e2).trans_eq (by ring))

end

end B13BoundedStepProductSavingProof

end

/- Right high grouped factors -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale DyadicMixedB4MoebiusGauss
open scoped Classical

noncomputable section

def groupedRightHighItems (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Ioc (cutoffB n) (min (splitCut n) (n/(rightLargeCofactorCut n+1)))) ×ˢ Icc 1 n).filter
    (fun t => t.1*t.2 ≤ n)

def rightHighGroupingKey (j : RightHighWaveIndex) : ℕ × ℕ :=
  (j.1*j.2.1,j.2.2)

def groupedRightHighMoebius (n r : ℕ) : ℂ :=
  ∑ d ∈ r.divisors.filter (fun d => d ≤ cutoffU n), -(ArithmeticFunction.moebius d : ℂ)

theorem right_high_grouping_key_mem {n : ℕ} {j : RightHighWaveIndex}
    (hj : j ∈ rightHighWaveItems n) : rightHighGroupingKey j ∈ groupedRightHighItems n := by
  obtain ⟨base,step⟩ := mem_filter.mp hj
  obtain ⟨dBand,rest⟩ := mem_sigma.mp base
  obtain ⟨kBand,bBand⟩ := mem_product.mp rest
  obtain ⟨lo,hi⟩ := mem_Ioc.mp kBand
  have d0 : 0 < j.1 := (mem_Icc.mp dBand).1
  have low : cutoffB n < j.1*j.2.1 := by
    have h := (Nat.div_lt_iff_lt_mul d0).mp lo
    simpa only [Nat.mul_comm] using h
  have high : j.1*j.2.1 ≤ min (splitCut n) (n/(rightLargeCofactorCut n+1)) := by
    have f1 := (Nat.le_div_iff_mul_le d0).mp (hi.trans (min_le_left _ _))
    have f2 := (Nat.le_div_iff_mul_le d0).mp (hi.trans (min_le_right _ _))
    simpa only [Nat.mul_comm] using le_min f1 f2
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨low,high⟩,bBand⟩,step⟩

private theorem grouped_right_high_inverse_mem {n d : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ groupedRightHighItems n)
    (hd : d ∈ t.1.divisors.filter (fun d => d ≤ cutoffU n)) :
    (⟨d,t.1/d,t.2⟩ : RightHighWaveIndex) ∈ rightHighWaveItems n := by
  have tData := mem_product.mp (mem_filter.mp ht).1
  have hTop := mem_Ioc.mp tData.1
  have dData := mem_filter.mp hd
  have r0 : 0 < t.1 := (Nat.zero_le _).trans_lt hTop.1
  have dr : d ∣ t.1 := (Nat.mem_divisors.mp dData.1).1
  have d0 : 0 < d := Nat.pos_of_dvd_of_pos dr r0
  have eq : d*(t.1/d)=t.1 := Nat.mul_div_cancel' dr
  have low : cutoffB n/d < t.1/d := by
    apply (Nat.div_lt_iff_lt_mul d0).mpr
    simpa only [Nat.mul_comm,eq] using hTop.1
  have hi₁ : t.1/d ≤ splitCut n/d :=
    Nat.div_le_div_right (hTop.2.trans (min_le_left _ _))
  have hi₂ : t.1/d ≤ n/(rightLargeCofactorCut n+1)/d :=
    Nat.div_le_div_right (hTop.2.trans (min_le_right _ _))
  refine mem_filter.mpr ⟨mem_sigma.mpr ⟨mem_Icc.mpr ⟨d0,dData.2⟩,
    mem_product.mpr ⟨mem_Ioc.mpr ⟨low,le_min hi₁ hi₂⟩,tData.2⟩⟩,?_⟩
  change d*(t.1/d)*t.2 ≤ n
  rw [eq]
  exact (mem_filter.mp ht).2

theorem sum_right_high_wave_by_grouped_factors (n : ℕ) (f : (ℕ × ℕ) → ℂ) :
    (∑ j ∈ rightHighWaveItems n, rightHighWaveWeight n j*f (rightHighGroupingKey j)) =
      ∑ t ∈ groupedRightHighItems n, groupedRightHighMoebius n t.1*
        (rightHighWaveFactor n t.2 : ℂ)*f t := by
  rw [← sum_fiberwise_of_maps_to (fun j hj => right_high_grouping_key_mem (n := n) hj)]
  refine sum_congr rfl fun t ht => ?_
  let U := t.1.divisors.filter (fun d => d ≤ cutoffU n)
  let fibre := (rightHighWaveItems n).filter (fun j => rightHighGroupingKey j=t)
  have fibreEq (d : ℕ) (hd : d ∈ U) :
      (⟨d,t.1/d,t.2⟩ : RightHighWaveIndex) ∈ fibre := by
    refine mem_filter.mpr ⟨grouped_right_high_inverse_mem ht hd,?_⟩
    have div := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
    exact Prod.ext (Nat.mul_div_cancel' div) rfl
  have divides (j : RightHighWaveIndex) (hj : j ∈ fibre) : j.1 ∈ U := by
    obtain ⟨h1,eq⟩ := mem_filter.mp hj
    have data := mem_sigma.mp (mem_filter.mp h1).1
    have top := (mem_Icc.mp data.1).2
    have first : j.1*j.2.1=t.1 := congrArg Prod.fst eq
    have tPos : 0 < t.1 := (Nat.zero_le _).trans_lt (mem_Ioc.mp (mem_product.mp (mem_filter.mp ht).1).1).1
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨j.2.1,first.symm⟩,tPos.ne'⟩,top⟩
  have eval (j : RightHighWaveIndex) (hj : j ∈ fibre) :
      rightHighWaveWeight n j*f (rightHighGroupingKey j) =
        -(ArithmeticFunction.moebius j.1 : ℂ)*(rightHighWaveFactor n t.2 : ℂ)*f t := by
    have eq := (mem_filter.mp hj).2
    have bEq : j.2.2 = t.2 :=
      show (rightHighGroupingKey j).2 = t.2 from congrArg Prod.snd eq
    simp only [rightHighWaveWeight,bEq,eq]
  change (∑ j ∈ fibre, rightHighWaveWeight n j*f (rightHighGroupingKey j)) =
    (∑ d ∈ U, -(ArithmeticFunction.moebius d : ℂ)) * (rightHighWaveFactor n t.2 : ℂ)*f t
  rw [sum_mul,sum_mul]
  refine sum_bij (fun j _ => j.1) divides ?_ ?_ eval
  · intro a ha b hb eq
    have ea := mem_filter.mp ha
    have eb := mem_filter.mp hb
    have aPos : 0 < a.1 := (mem_Icc.mp (mem_sigma.mp (mem_filter.mp ea.1).1).1).1
    have firstA : a.1*a.2.1=t.1 := congrArg Prod.fst ea.2
    have firstB : b.1*b.2.1=t.1 := congrArg Prod.fst eb.2
    rw [← eq] at firstB
    have mid := Nat.eq_of_mul_eq_mul_left aPos (firstA.trans firstB.symm)
    have tail := (congrArg Prod.snd ea.2).trans (congrArg Prod.snd eb.2).symm
    cases a
    cases b
    cases eq
    simp only at mid tail
    exact congrArg (fun k : ℕ × ℕ => (⟨_,k⟩ : RightHighWaveIndex)) (Prod.ext mid tail)
  · intro d hd
    exact ⟨⟨d,t.1/d,t.2⟩, fibreEq d hd, rfl⟩

theorem norm_grouped_right_high_moebius_le (n r : ℕ) :
    ‖groupedRightHighMoebius n r‖ ≤ (r.divisors.card : ℝ) := by
  unfold groupedRightHighMoebius
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ r.divisors.filter (fun d => d ≤ cutoffU n), (1 : ℝ) := by
      refine sum_le_sum fun d _ => ?_
      simpa only [norm_neg,moebiusComplex] using norm_moebiusComplex_le_one d
    _ = ((r.divisors.filter (fun d => d ≤ cutoffU n)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast card_le_card (filter_subset _ _)

end

end B13BoundedStepProductSavingProof

end

/- Swapped high factor geometry -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4MoebiusGauss
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def swappedHighFactorCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(31/96 : ℝ)⌋₊

def swappedHighFactorFloor (n k : ℕ) : ℕ := ⌊(n : ℝ)^((k : ℝ)/32768)⌋₊

def swappedHighFactorLower (n k : ℕ) : ℕ := max (rightVaughanCut n) (swappedHighFactorFloor n k)

def swappedHighFactorBlock (n k : ℕ) : Finset ℕ :=
  Ioc (swappedHighFactorLower n k) (min (swappedHighFactorCap n) (swappedHighFactorFloor n (k+1)))

theorem norm_right_high_wave_factor_le {n b : ℕ} (bn : b ≤ n)
    {T : ℝ} (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖(rightHighWaveFactor n b : ℂ)‖ ≤ T * logBudget n := by
  let f := (μ : ArithmeticFunction ℝ)-rightVaughanMoebius n
  let g := vonMangoldt-rightVaughanMangoldt n
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have mNorm (j : ℕ) (_ : j ≤ n) : ‖(f j : ℂ)‖ ≤ 1 := by
    change ‖(((μ j : ℝ) - (if j ≤ rightVaughanCut n then (μ j : ℝ) else 0) : ℝ) : ℂ)‖ ≤ 1
    by_cases h : j ≤ rightVaughanCut n
    · simp [h]
    · simpa [h,moebiusComplex] using norm_moebiusComplex_le_one j
  have lNorm (j : ℕ) (hj : j ≤ n) : ‖(g j : ℂ)‖ ≤ logBudget n := by
    change ‖((vonMangoldt j - (if j ≤ rightVaughanCut n then vonMangoldt j else 0) : ℝ) : ℂ)‖ ≤ logBudget n
    by_cases h : j ≤ rightVaughanCut n
    · simp [h,L0]
    · simp only [h,ite_false,sub_zero]
      by_cases zero : j = 0
      · simp [zero,L0]
      · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg]
        refine vonMangoldt_le_log.trans ?_
        unfold logBudget
        linarith only [Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero zero : (0 : ℝ) < j)
          (show (j : ℝ) ≤ (n : ℝ)+2 by exact_mod_cast hj.trans (Nat.le_add_right n 2))]
  change ‖(((f*g : ArithmeticFunction ℝ) b) : ℂ)‖ ≤ _
  simpa only [one_mul] using norm_convolution_apply_le bn f g zero_le_one L0 (divisors b bn) mNorm lNorm

theorem swapped_high_factor_blocks_cover {n a : ℕ} (n1 : 1 ≤ n)
    (ha : a ∈ Ioc (rightVaughanCut n) (swappedHighFactorCap n)) :
    ∃! k, k ∈ Icc 128 10581 ∧ a ∈ swappedHighFactorBlock n k := by
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have mono : Monotone (swappedHighFactorFloor n) := by
    intro j k le
    have hr : (j : ℝ) ≤ k := by exact_mod_cast le
    exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR
      (div_le_div_of_nonneg_right hr (by norm_num)))
  have Lo : swappedHighFactorFloor n 128 = rightVaughanCut n := by
    unfold swappedHighFactorFloor rightVaughanCut
    norm_num
  have Hi : swappedHighFactorCap n ≤ swappedHighFactorFloor n 10582 := by
    exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have upper : a ≤ swappedHighFactorFloor n 10582 := (mem_Ioc.mp ha).2.trans Hi
  have existsBlock : ∃ t : ℕ, a ≤ swappedHighFactorFloor n t := ⟨10582,upper⟩
  let t := Nat.find existsBlock
  have tLe : t ≤ 10582 := Nat.find_min' existsBlock upper
  have tHi : a ≤ swappedHighFactorFloor n t := Nat.find_spec existsBlock
  have tLo : 128 < t := by
    apply lt_of_not_ge
    intro h
    have impossible := tHi.trans (mono h)
    rw [Lo] at impossible
    exact (not_le_of_gt (mem_Ioc.mp ha).1) impossible
  let k := t-1
  have kn : k+1=t := by unfold k; omega
  have kt : k<t := by unfold k; omega
  have kMem : k ∈ Icc 128 10581 := mem_Icc.mpr ⟨by omega,by omega⟩
  have lo : swappedHighFactorFloor n k < a := lt_of_not_ge (Nat.find_min existsBlock kt)
  have hi : a ≤ swappedHighFactorFloor n (k+1) := by rw [kn]; exact tHi
  have inK : a ∈ swappedHighFactorBlock n k :=
    mem_Ioc.mpr ⟨max_lt (mem_Ioc.mp ha).1 lo,le_min (mem_Ioc.mp ha).2 hi⟩
  refine ⟨k,⟨kMem,inK⟩,fun j hj => ?_⟩
  have separate (b c : ℕ) (hb : a ∈ swappedHighFactorBlock n b)
      (hc : a ∈ swappedHighFactorBlock n c) (bc : b < c) : False := by
    have upper : a ≤ swappedHighFactorFloor n (b+1) := (mem_Ioc.mp hb).2.trans (min_le_right _ _)
    have lower : swappedHighFactorFloor n c < a := (le_max_right _ _).trans_lt (mem_Ioc.mp hc).1
    exact (not_le_of_gt lower) (upper.trans (mono bc))
  exact le_antisymm (le_of_not_gt (separate k j inK hj.2)) (le_of_not_gt (separate j k hj.2 inK))

end

end B13BoundedStepProductSavingProof

end

/- Swapped high windows geometry -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def swappedHighRows (n : ℕ) : Finset (ℕ × ℕ) :=
  (bilateralLeftWaveItems n).filter fun i =>
    let m := leftBilinearStep i
    m^2 ≤ n ∧ (n : ℝ)^(87/256 : ℝ) ≤ (m : ℝ) ∧ m.gcd n ≤ thinHighLeftDivisorCap n

def swappedHighStepUpper (n m : ℕ) : ℕ :=
  min (extendedWideStepCap n) (2*n/m)

def swappedHighFactors (n m g e k : ℕ) : Finset ℕ :=
  (Ioc (swappedHighFactorLower n k/e)
      (min (swappedHighFactorCap n) (swappedHighFactorFloor n (k+1))/e)).filter
    (fun a => (e*a).gcd g=e ∧ a.Coprime (m/g))

def swappedHighCofactorCap (n m g e k : ℕ) : ℕ :=
  (swappedHighStepUpper n m/g)/(swappedHighFactorLower n k/e+1)

def swappedHighTailLower (n g e : ℕ) : ℤ :=
  (cutoffB n/(g/e) : ℕ)

def swappedHighPrefixLower (n e a : ℕ) : ℕ := rightLargeCofactorCut n/(e*a)

def swappedHighTailUpper (n m g e a : ℕ) : ℤ :=
  let b := swappedHighPrefixLower n e a
  let cap := min (splitCut n) (n/(rightLargeCofactorCut n+1))/(g/e)
  ((min cap (if b=0 then n else (n/g-m/g)/(a*b)) : ℕ) : ℤ)

theorem swapped_high_endpoint_cap_of_size {n p l num : ℕ} (n0 : 0 < n) (p0 : 0 < p)
    (cut : thinHighProductCap n/p ≤ l) (nBound : num ≤ n) :
    num/(l+1) ≤ ⌊(p : ℝ)*(n : ℝ)^(1/8192 : ℝ)⌋₊ := by
  let N := (n : ℝ)
  let P := (p : ℝ)
  let H := N^(1/8192 : ℝ)
  have np : 0 < N := show (0 : ℝ) < (n : ℝ) from by exact_mod_cast n0
  have lp : (0 : ℝ) < (l : ℝ)+1 := by positivity
  have large : thinHighProductCap n < (l+1)*p :=
    (Nat.div_lt_iff_lt_mul p0).mp (Nat.lt_succ_of_le cut)
  have scaled : N^(8191/8192 : ℝ) ≤ ((l : ℝ)+1)*P := by
    have fl := Nat.lt_floor_add_one (N^(8191/8192 : ℝ))
    have room : (thinHighProductCap n : ℝ)+1 ≤ ((l : ℝ)+1)*P := by
      unfold P
      exact_mod_cast Nat.succ_le_of_lt large
    exact fl.le.trans room
  have final : N ≤ ((l : ℝ)+1)*(P*H) := calc
    _ = N^(8191/8192 : ℝ)*H := by unfold H; rw [← Real.rpow_add np]; norm_num
    _ ≤ (((l : ℝ)+1)*P)*H := mul_le_mul_of_nonneg_right scaled (by positivity)
    _ = _ := by ring
  apply Nat.le_floor
  calc
    _ ≤ N/((l : ℝ)+1) := (le_div_iff₀ lp).mpr (by
      have nat := (Nat.div_mul_le_self num (l+1)).trans nBound
      change ((num/(l+1) : ℕ) : ℝ)*((l : ℝ)+1) ≤ (n : ℝ)
      exact_mod_cast nat)
    _ ≤ P*H := (div_le_iff₀ lp).mpr (by simpa only [mul_comm] using final)

end

end B13BoundedStepProductSavingProof

end

/- Swapped high row def -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def swappedHighDivisors (n m : ℕ) : Finset ℕ :=
  n.divisors.filter fun g => g ≤ thinHighGcdCap n ∧ g ≤ maximumStep n ∧ g ∣ m

end

end B13BoundedStepProductSavingProof

end

/- Swapped high near gate -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

theorem thin_high_product_cap_ge_old (n : ℕ) : subcriticalMediumProductCap n ≤ thinHighProductCap n := by
  rcases eq_or_ne n 0 with rfl | h
  · norm_num [thinHighProductCap,subcriticalMediumProductCap,Real.zero_rpow]
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero h) (by norm_num))

theorem thin_high_gcd_cap_le_old (n : ℕ) : thinHighGcdCap n ≤ nearProductCommonDivisorCut n := by
  rcases eq_or_ne n 0 with rfl | h
  · norm_num [thinHighGcdCap,nearProductCommonDivisorCut,Real.zero_rpow]
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero h) (by norm_num))

theorem eventually_swapped_high_large : ∀ᶠ n : ℕ in Filter.atTop,
    (2 : ℝ) ≤ (n : ℝ)^(3/1024 : ℝ) := by
  have limit : Filter.Tendsto (fun n : ℕ => (n : ℝ)^(3/1024 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/1024)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  exact limit.eventually_ge_atTop 2

end

end B13BoundedStepProductSavingProof

end

/- Moderate low divided hyperbola bridge -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical Finset

noncomputable section

set_option maxHeartbeats 2200000 in
def moderateLowDividedHyperbolaLeftItems (n m g e k l₀ r₀ : ℕ) : Finset (ℕ × ℕ) :=
  (bilateralLeftWaveItems n).filter fun i =>
    i.1 ∈ primeHyperbolaFactorBlock n k ∧ (leftBilinearStep i).gcd m = g ∧ i.1.gcd g = e ∧
      l₀ < leftBilinearStep i ∧ leftBilinearStep i ≤ r₀

set_option maxHeartbeats 2200000 in
theorem moderate_low_divided_hyperbola_window_eq_selected {n m g e k l₀ r₀ : ℕ}
    (mpos : 0 < m) (mN : m ≤ n) (lLower : leftMediumCap n ≤ l₀) (rUpper : r₀ ≤ extendedWideStepCap n)
    (g0 : 0 < g) (gn : g ∣ n) (gm : g ∣ m) (e0 : 0 < e) (eg : e ∣ g) :
    moderateLowDividedHyperbolaWindow n m g e k l₀ r₀ =
      ∑ i ∈ moderateLowDividedHyperbolaLeftItems n m g e k l₀ r₀,
        leftBilinearWeight n i * (pairResidueError n (leftBilinearStep i) m 0
          (n/leftBilinearStep i) 0 (n/m) : ℂ) := by
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
  let value (i : ℕ × ℕ) := leftBilinearWeight n i *
    (pairResidueError n (leftBilinearStep i) m 0
      (n/leftBilinearStep i) 0 (n/m) : ℂ)
  let F (num a : ℕ) (j : ℤ) :=
    centeredIntIntervalResidue v 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
      ((n/g : ℕ)*((a : ZMod v)*(j : ZMod v))⁻¹)
  let w (t : ℤ × ℕ) := leftBilinearWeight n (liftPoint t) * (F (n/g-v) t.2 t.1 - F (n/g-v*(n/m)-1) t.2 t.1)
  have n0 : 0 < n := mpos.trans_le mN
  have gE : e*h = g := Nat.mul_div_cancel' eg
  have h0 : 0 < h := Nat.div_pos (Nat.le_of_dvd g0 eg) e0
  have vG : g*v=m := Nat.mul_div_cancel' gm
  have vEq : m/g=v := rfl
  have ends : 0 < n/m := Nat.div_pos mN mpos
  have cap_mul : m*(n/m) ≤ n := Nat.mul_div_le n m
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
    have z0 := (mem_Ioc.mp (infoJ htJ).1).1
    have j0 : 0 < t.1.toNat := by omega
    have a0 := (Nat.zero_le _).trans_lt (infoI (mem_product.mp (mem_filter.mp ht).1).2).1
    have alg : (leftBilinearStep (liftPoint t)).gcd m=g := (mem_filter.mp hi).2.2.1
    have c : (t.1.toNat : ZMod v) = (t.1 : ZMod v) := by
      simpa only [Int.cast_natCast] using congrArg (fun j : ℤ => (j : ZMod v)) (Int.toNat_of_nonneg z0.le)
    have E := left_factor_capped_interval_residue_eq_normalized (mul_pos e0 a0) (mul_pos h0 j0) mpos ends cap_mul
      (show (e*t.2*(h*t.1.toNat)).gcd m ∣ n from alg.symm ▸ gn)
    dsimp only at E
    change (pairResidueError n (e*t.2*(h*t.1.toNat)) m 0 (n/(e*t.2*(h*t.1.toNat))) 0 (n/m) : ℂ) = _ at E
    change (e*t.2*(h*t.1.toNat)).gcd m = g at alg
    rw [alg,(infoI (mem_product.mp (mem_filter.mp ht).1).2).2.2.1,
      Nat.mul_div_cancel_left _ e0,Nat.mul_div_cancel_left _ h0] at E
    unfold w value
    change _ * (F (n/g-v) t.2 t.1 - F (n/g-v*(n/m)-1) t.2 t.1) =
      _ * (pairResidueError n (e*t.2*(h*t.1.toNat)) m 0 (n/(e*t.2*(h*t.1.toNat))) 0 (n/m) : ℂ)
    rw [E]
    unfold F
    have phase : ((t.2*t.1.toNat : ℕ) : ZMod v) = (t.2 : ZMod v)*(t.1 : ZMod v) := by
      rw [Nat.cast_mul,c]
    change _ * (centeredIntIntervalResidue v 0 _ _ - centeredIntIntervalResidue v 0 _ _) =
      _ * (centeredIntIntervalResidue v 0 _ ((n/g : ℕ)*(((t.2*t.1.toNat : ℕ) : ZMod v)⁻¹)) -
        centeredIntIntervalResidue v 0 _ ((n/g : ℕ)*(((t.2*t.1.toNat : ℕ) : ZMod v)⁻¹)))
    rw [phase]
    simp only [Nat.zero_add,Nat.mul_one,v]
  have eq : moderateLowDividedHyperbolaWindow n m g e k l₀ r₀ = ∑ t ∈ P, w t := by
    change gatedBilinearSum I J (fun a => (leftBandMoebius n (e*a) : ℂ))
        (fun j => (leftBilinearFactor n (h*j.toNat) : ℂ)) (fun a => (l/a : ℕ)) (fun a => (r/a : ℕ)) (F (n/g-v)) -
      gatedBilinearSum I J (fun a => (leftBandMoebius n (e*a) : ℂ))
        (fun j => (leftBilinearFactor n (h*j.toNat) : ℂ)) (fun a => (l/a : ℕ)) (fun a => (r/a : ℕ)) (F (n/g-v*(n/m)-1)) = _
    rw [gated_bilinear_sum_eq_pair_sum,gated_bilinear_sum_eq_pair_sum,← sum_sub_distrib]
    unfold P
    rw [sum_filter,sum_product]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    change (ite (gate a j) _ 0 - ite (gate a j) _ 0) = ite (gate a j) _ 0
    by_cases hG : gate a j
    · rw [ite_eq_left hG,ite_eq_left hG,ite_eq_left hG]
      simp only [w,liftPoint,leftBilinearWeight,← mul_sub]
    · simp only [ite_eq_right hG,sub_zero]
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

end B13BoundedStepProductSavingProof

end

/- Outer left window bridge -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical Finset

noncomputable section

set_option maxHeartbeats 2200000 in
theorem outer_left_window_eq_selected {n m b c g e k l₀ r₀ : ℕ}
    (mpos : 0 < m) (mN : m ≤ n) (ends : b < c) (cap_mul : m*c ≤ n) (lLower : leftMediumCap n ≤ l₀) (rUpper : r₀ ≤ n)
    (g0 : 0 < g) (gn : g ∣ n) (gm : g ∣ m) (e0 : 0 < e) (eg : e ∣ g) :
    outerLeftWindow n m b c g e k l₀ r₀ =
      ∑ i ∈ moderateLowDividedHyperbolaLeftItems n m g e k l₀ r₀,
        leftBilinearWeight n i * (pairResidueError n (leftBilinearStep i) m 0
          (n/leftBilinearStep i) b c : ℂ) := by
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
  let value (i : ℕ × ℕ) := leftBilinearWeight n i *
    (pairResidueError n (leftBilinearStep i) m 0
      (n/leftBilinearStep i) b c : ℂ)
  let F (num a : ℕ) (j : ℤ) :=
    centeredIntIntervalResidue v 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
      ((n/g : ℕ)*((a : ZMod v)*(j : ZMod v))⁻¹)
  let w (t : ℤ × ℕ) := leftBilinearWeight n (liftPoint t) * (F (n/g-v*(b+1)) t.2 t.1 - F (n/g-v*c-1) t.2 t.1)
  have n0 : 0 < n := mpos.trans_le mN
  have gE : e*h = g := Nat.mul_div_cancel' eg
  have h0 : 0 < h := Nat.div_pos (Nat.le_of_dvd g0 eg) e0
  have vG : g*v=m := Nat.mul_div_cancel' gm
  have vEq : m/g=v := rfl
  have rN : r₀ ≤ n := rUpper
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
    have z0 := (mem_Ioc.mp (infoJ htJ).1).1
    have j0 : 0 < t.1.toNat := by omega
    have a0 := (Nat.zero_le _).trans_lt (infoI (mem_product.mp (mem_filter.mp ht).1).2).1
    have alg : (leftBilinearStep (liftPoint t)).gcd m=g := (mem_filter.mp hi).2.2.1
    have castRight : (t.1.toNat : ZMod v) = (t.1 : ZMod v) := by
      simpa only [Int.cast_natCast] using congrArg (fun j : ℤ => (j : ZMod v)) (Int.toNat_of_nonneg z0.le)
    have E := left_factor_capped_interval_residue_eq_normalized (mul_pos e0 a0) (mul_pos h0 j0) mpos ends cap_mul
      (show (e*t.2*(h*t.1.toNat)).gcd m ∣ n from alg.symm ▸ gn)
    dsimp only at E
    change (pairResidueError n (e*t.2*(h*t.1.toNat)) m 0 (n/(e*t.2*(h*t.1.toNat))) b c : ℂ) = _ at E
    change (e*t.2*(h*t.1.toNat)).gcd m = g at alg
    rw [alg,(infoI (mem_product.mp (mem_filter.mp ht).1).2).2.2.1,
      Nat.mul_div_cancel_left _ e0,Nat.mul_div_cancel_left _ h0] at E
    unfold w value
    change _ * (F (n/g-v*(b+1)) t.2 t.1 - F (n/g-v*c-1) t.2 t.1) =
      _ * (pairResidueError n (e*t.2*(h*t.1.toNat)) m 0 (n/(e*t.2*(h*t.1.toNat))) b c : ℂ)
    rw [E]
    unfold F
    have phase : ((t.2*t.1.toNat : ℕ) : ZMod v) = (t.2 : ZMod v)*(t.1 : ZMod v) := by
      rw [Nat.cast_mul,castRight]
    change _ * (centeredIntIntervalResidue v 0 _ _ - centeredIntIntervalResidue v 0 _ _) =
      _ * (centeredIntIntervalResidue v 0 _ ((n/g : ℕ)*(((t.2*t.1.toNat : ℕ) : ZMod v)⁻¹)) -
        centeredIntIntervalResidue v 0 _ ((n/g : ℕ)*(((t.2*t.1.toNat : ℕ) : ZMod v)⁻¹)))
    rw [phase] <;> rfl
  have eq : outerLeftWindow n m b c g e k l₀ r₀ = ∑ t ∈ P, w t := by
    change gatedBilinearSum I J (fun a => (leftBandMoebius n (e*a) : ℂ))
        (fun j => (leftBilinearFactor n (h*j.toNat) : ℂ)) (fun a => (l/a : ℕ)) (fun a => (r/a : ℕ)) (F (n/g-v*(b+1))) -
      gatedBilinearSum I J (fun a => (leftBandMoebius n (e*a) : ℂ))
        (fun j => (leftBilinearFactor n (h*j.toNat) : ℂ)) (fun a => (l/a : ℕ)) (fun a => (r/a : ℕ)) (F (n/g-v*c-1)) = _
    rw [gated_bilinear_sum_eq_pair_sum,gated_bilinear_sum_eq_pair_sum,← sum_sub_distrib]
    unfold P
    rw [sum_filter,sum_product]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    change (ite (gate a j) _ 0 - ite (gate a j) _ 0) = ite (gate a j) _ 0
    by_cases hG : gate a j
    · rw [ite_eq_left hG,ite_eq_left hG,ite_eq_left hG]
      simp only [w,liftPoint,leftBilinearWeight,← mul_sub]
    · simp only [ite_eq_right hG,sub_zero]
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

end B13BoundedStepProductSavingProof

end

/- Bounded outer left row -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4PairIntegral
open scoped Classical

noncomputable section

def boundedOuterLeftRow (n m b c lo hi : ℕ) : ℂ :=
  ∑ g ∈ swappedHighDivisors n m, ∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63,
    outerLeftWindow n m b c g e k lo hi

theorem norm_bounded_divided_row_le {n m b c lo hi : ℕ}
    (m0 : 0 < m) (mN : m ≤ n)
    (mLower : (n : ℝ)^(171/512 : ℝ) ≤ (m : ℝ)) (mUpper : (m : ℝ) ≤ (n : ℝ)^(515/1024 : ℝ))
    (charTop : m.gcd n ≤ targetDivisorCap n) (ns : 1 < n)
    (rUpper : hi ≤ n) (rProd : hi*m ≤ expandedHyperbolaProductCap n)
    (lLower : subcriticalMediumProductCap n/m ≤ lo)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T)
    (divN : ∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) :
    ‖boundedOuterLeftRow n m b c lo hi‖ ≤
      (48*(1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3)*T^2)*(1/(m : ℝ)) := by
  let B := 1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3
  let M := (m : ℝ)
  let V := 48*B/M
  let G := swappedHighDivisors n m
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have V0 : 0 ≤ V := by unfold V M B; positivity
  have natCard : G.card ≤ n.divisors.card := card_le_card (filter_subset _ n.divisors)
  have nG : (G.card : ℝ) ≤ T := (show (G.card : ℝ) ≤ (n.divisors.card : ℝ) by exact_mod_cast natCard).trans (divN n le_rfl)
  have per (g : ℕ) (hg : g ∈ G) : ‖∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63,
      outerLeftWindow n m b c g e k lo hi‖ ≤ T*V := by
    obtain ⟨data,gS,_,gq⟩ := mem_filter.mp hg
    have gn := (Nat.mem_divisors.mp data).1
    have g0 := Nat.pos_of_dvd_of_pos gn (zero_lt_one.trans ns)
    have en : (g.divisors.card : ℝ) ≤ T := divN g (Nat.le_of_dvd (zero_lt_one.trans ns) gn)
    calc
      _ ≤ ∑ e ∈ g.divisors, ‖∑ k ∈ Icc 16 63, outerLeftWindow n m b c g e k lo hi‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ g.divisors, V := by
        refine sum_le_sum fun e he => ?_
        have eg := (Nat.mem_divisors.mp he).1
        have e0 := Nat.pos_of_dvd_of_pos eg g0
        calc
          _ ≤ ∑ k ∈ Icc 16 63, ‖outerLeftWindow n m b c g e k lo hi‖ := norm_sum_le _ _
          _ ≤ ∑ _ ∈ Icc 16 63, B/M := sum_le_sum fun k hk =>
            norm_divided_window_le m0 mN mLower mUpper charTop rUpper rProd lLower
              g0 gn gq gS e0 eg hk ns T1 divisors
          _ = V := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,V]; norm_num; ring
      _ = (g.divisors.card : ℝ)*V := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right en V0
  change ‖∑ g ∈ G, ∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63, outerLeftWindow n m b c g e k lo hi‖ ≤
    (48*B*T^2)*(1/(m : ℝ))
  calc
    _ ≤ ∑ g ∈ G, ‖∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63, outerLeftWindow n m b c g e k lo hi‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ ∈ G, T*V := sum_le_sum per
    _ = (G.card : ℝ)*(T*V) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ T*(T*V) := mul_le_mul_of_nonneg_right nG (by positivity)
    _ = _ := by unfold V M; ring

def boundedOuterLeftRowItems (n m lo hi : ℕ) : Finset (ℕ × ℕ) :=
  (bilateralLeftWaveItems n).filter fun i =>
    let u := leftBilinearStep i
    u.gcd m ∈ swappedHighDivisors n m ∧ lo < u ∧ u ≤ hi

theorem bounded_outer_left_row_eq_selected {n m b c lo hi : ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (ends : b < c) (cap : m*c ≤ n)
    (lLeft : leftMediumCap n ≤ lo) (rUpper : hi ≤ n) :
    boundedOuterLeftRow n m b c lo hi =
      ∑ i ∈ boundedOuterLeftRowItems n m lo hi, leftBilinearWeight n i *
        (pairResidueError n (leftBilinearStep i) m 0 (n/leftBilinearStep i) b c : ℂ) := by
  let I := boundedOuterLeftRowItems n m lo hi
  let G := swappedHighDivisors n m
  let K := Icc 16 63
  let d (i : ℕ × ℕ) := (leftBilinearStep i).gcd m
  let w (i : ℕ × ℕ) := leftBilinearWeight n i *
    (pairResidueError n (leftBilinearStep i) m 0
      (n/leftBilinearStep i) b c : ℂ)
  have n1 : 1 ≤ n := m0.trans_le mN
  have mapsG : ∀ i ∈ I, d i ∈ G := fun _ hi => (mem_filter.mp hi).2.1
  change boundedOuterLeftRow n m b c lo hi = ∑ i ∈ I, w i
  rw [← sum_fiberwise_of_maps_to mapsG w]
  unfold boundedOuterLeftRow
  refine sum_congr rfl fun g hg => ?_
  let I₁ := I.filter fun i => d i = g
  let aGcd (i : ℕ × ℕ) := i.1.gcd g
  have gData := mem_filter.mp hg
  have gn := (Nat.mem_divisors.mp gData.1).1
  have g0 := Nat.pos_of_dvd_of_pos gn n1
  have gq := gData.2.2.2
  have mapsE : ∀ i ∈ I₁, aGcd i ∈ g.divisors :=
    fun i _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right i.1 g,g0.ne'⟩
  change (∑ e ∈ g.divisors, ∑ k ∈ K, outerLeftWindow n m b c g e k lo hi) = ∑ i ∈ I₁, w i
  rw [← sum_fiberwise_of_maps_to mapsE w]
  refine sum_congr rfl fun e he => ?_
  let I₂ := I₁.filter fun i => aGcd i=e
  have eg := (Nat.mem_divisors.mp he).1
  have e0 := Nat.pos_of_dvd_of_pos eg g0
  have eqFilter (k : ℕ) : moderateLowDividedHyperbolaLeftItems n m g e k lo hi =
      I₂.filter fun i => i.1 ∈ primeHyperbolaFactorBlock n k := by
    ext i
    constructor
    · intro hi
      obtain ⟨left,fac,gg,ee,lo,up⟩ := mem_filter.mp hi
      have dG : d i ∈ G := by
        change (leftBilinearStep i).gcd m ∈ swappedHighDivisors n m
        rw [gg]
        exact hg
      have base : i ∈ I := mem_filter.mpr ⟨left,dG,lo,up⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨base,gg⟩,ee⟩,fac⟩
    · intro hi
      obtain ⟨hi₂,fac⟩ := mem_filter.mp hi
      obtain ⟨hi₁,ee⟩ := mem_filter.mp hi₂
      obtain ⟨hi₀,gg⟩ := mem_filter.mp hi₁
      obtain ⟨left,_,lo,up⟩ := mem_filter.mp hi₀
      exact mem_filter.mpr ⟨left,fac,gg,ee,lo,up⟩
  calc
    (∑ k ∈ K, outerLeftWindow n m b c g e k lo hi) =
        ∑ k ∈ K, ∑ i ∈ I₂.filter (fun i => i.1 ∈ primeHyperbolaFactorBlock n k), w i := by
      refine sum_congr rfl fun k _ => ?_
      rw [← eqFilter k]
      exact outer_left_window_eq_selected m0 mN ends cap lLeft rUpper g0 gn gq e0 eg
    _ = ∑ i ∈ I₂, ∑ k ∈ K, if i.1 ∈ primeHyperbolaFactorBlock n k then w i else 0 := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = ∑ i ∈ I₂, w i := by
      refine sum_congr rfl fun i hi => ?_
      have left : i ∈ bilateralLeftWaveItems n :=
        (mem_filter.mp (mem_filter.mp (mem_filter.mp hi).1).1).1
      have aRange := (mem_product.mp (mem_filter.mp (mem_filter.mp left).1).1).1
      obtain ⟨k,⟨kMem,hk⟩,unique⟩ := prime_hyperbola_factor_blocks_cover n1 aRange
      rw [sum_eq_single_of_mem k kMem]
      · exact ite_eq_left hk
      · intro k' hk' neq
        exact ite_eq_right (fun h => neq (unique k' ⟨hk',h⟩))

end

end B13BoundedStepProductSavingProof

end

/- Bounded outer left saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def boundedDividedResidueFrom (lower upper : ℕ → ℕ → ℕ) (n : ℕ) {κ : Type} (J : Finset κ)
    (v b c : κ → ℕ) (w : κ → ℂ) : ℂ :=
  ∑ j ∈ J, w j * boundedOuterLeftRow n (v j) (b j) (c j) (lower n (v j)) (upper n (v j))

private theorem norm_bounded_divided_slice_le (lower upper : ℕ → ℕ → ℕ) {n : ℕ} (nBig : 2 ≤ n) {κ : Type}
    (J₀ R : Finset κ) (v b c : κ → ℕ) (w : κ → ℂ)
    (subset : R ⊆ J₀)
    (data : ∀ j ∈ R, (n : ℝ)^(171/512 : ℝ) ≤ (v j : ℝ) ∧
      (v j : ℝ) ≤ (n : ℝ)^(515/1024 : ℝ) ∧ (v j).gcd n ≤ targetDivisorCap n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T)
    (bounds : ∀ m : ℕ, upper n m ≤ n ∧ upper n m*m ≤ expandedHyperbolaProductCap n ∧
      subcriticalMediumProductCap n/m ≤ lower n m)
    (steps : ∀ j ∈ J₀, v j ∈ Icc 1 n)
    (weights : ∀ m ∈ Icc 1 n, (∑ j ∈ J₀.filter (fun j => v j=m), ‖w j‖) ≤ T^3*logBudget n) :
    ‖boundedDividedResidueFrom lower upper n R v b c w‖ ≤ 56832*(n : ℝ)^(1023/1024 : ℝ)*T^8*logBudget n^5 := by
  let L := logBudget n
  let C := n
  let B := 1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*L^3
  let W := T^3*L
  let J := R
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have B0 : 0 ≤ B := by unfold B; positivity
  have W0 : 0 ≤ W := by unfold W; positivity
  have n1 : 1 ≤ n := (show 1 ≤ (2 : ℕ) by decide).trans nBig
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have nPos : (0 : ℝ) < n := zero_lt_one.trans_le nR
  have C1 : 1 ≤ C := n1
  have Cn : (C : ℝ) ≤ (n : ℝ) := le_rfl
  have Cnat : C ≤ n := by exact_mod_cast Cn
  have divN (u : ℕ) (h : u ≤ n) : (u.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors u (h.trans nn)
  have ns : 1 < n := nBig
  have massH : (∑ m ∈ Icc 1 C, 1/(m : ℝ)) ≤ L := calc
    _ = (harmonic C : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    _ ≤ 1+Real.log C := by exact_mod_cast harmonic_le_one_add_log C
    _ ≤ L := by
      unfold L logBudget
      exact add_le_add_right (Real.log_le_log (by exact_mod_cast C1)
        (Cn.trans (by linarith : (n : ℝ) ≤ (n : ℝ)+2))) _
  have step (j : κ) (hj : j ∈ J) : v j ∈ Icc 1 C :=
    steps j (subset hj)
  have weighted : (∑ j ∈ J, ‖w j‖*(1/(v j : ℝ))) ≤ W*L := by
    refine (sum_norm_mul_le_of_step_mass J v w (fun m => 1/(m : ℝ))
      step (fun _ _ => by positivity) ?_).trans (mul_le_mul_of_nonneg_left massH W0)
    intro m hm
    have h : m ∈ Icc 1 n := mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans Cnat⟩
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ subset)
      (fun _ _ _ => norm_nonneg _)).trans (weights m h)
  have each (j : κ) (hj : j ∈ J) :
      ‖boundedOuterLeftRow n (v j) (b j) (c j) (lower n (v j)) (upper n (v j))‖ ≤ (48*B*T^2)*(1/(v j : ℝ)) := by
    obtain ⟨mLo,mHi,char⟩ := data j hj
    have range := mem_Icc.mp (steps j (subset hj))
    obtain ⟨rUpper,rProd,lLower⟩ := bounds (v j)
    exact norm_bounded_divided_row_le range.1 range.2 mLo mHi char ns rUpper rProd lLower T1 divisors divN
  unfold boundedDividedResidueFrom
  change ‖∑ j ∈ J, w j*boundedOuterLeftRow n (v j) (b j) (c j) (lower n (v j)) (upper n (v j))‖ ≤ _
  calc
    _ ≤ ∑ j ∈ J, ‖w j*boundedOuterLeftRow n (v j) (b j) (c j) (lower n (v j)) (upper n (v j))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ‖w j‖*((48*B*T^2)*(1/(v j : ℝ))) := by
      refine sum_le_sum fun j hj => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (each j hj) (norm_nonneg _)
    _ = (48*B*T^2)*(∑ j ∈ J, ‖w j‖*(1/(v j : ℝ))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (48*B*T^2)*(W*L) := mul_le_mul_of_nonneg_left weighted (by positivity)
    _ = _ := by unfold B W L; ring

theorem bounded_divided_residue_saving (lower upper : ℕ → ℕ → ℕ) {κ : Type} (J R : ℕ → Finset κ)
    (v : κ → ℕ) (b c : ℕ → κ → ℕ) (w : ℕ → κ → ℂ)
    (subset : ∀ n, R n ⊆ J n)
    (data : ∀ n, ∀ j ∈ R n, (n : ℝ)^(171/512 : ℝ) ≤ (v j : ℝ) ∧
      (v j : ℝ) ≤ (n : ℝ)^(515/1024 : ℝ) ∧ (v j).gcd n ≤ targetDivisorCap n)
    (bounds : ∀ n > (0 : ℕ), ∀ m : ℕ, upper n m ≤ n ∧ upper n m*m ≤ expandedHyperbolaProductCap n ∧
      subcriticalMediumProductCap n/m ≤ lower n m)
    (steps : ∀ n, ∀ j ∈ J n, v j ∈ Icc 1 n)
    (weights : ∀ n, ∀ {T : ℝ}, 1 ≤ T → (∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) →
      ∀ m ∈ Icc 1 n, (∑ j ∈ (J n).filter (fun j => v j=m), ‖w n j‖) ≤ T^3*logBudget n) :
    saving (fun n => boundedDividedResidueFrom lower upper n (R n) v (b n) (c n) (w n)) := by
  intro ε he
  obtain ⟨D,D1,db⟩ := divisor_envelope_at_power 65536 (by decide)
  let C := 56832*(4*D)^8
  have hlimit : Tendsto (fun n : ℕ => (n : ℝ)^(-(35/65536) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 35/65536)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(35/65536) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlimit
  have bound : ∀ᶠ n : ℕ in atTop, ‖boundedDividedResidueFrom lower upper n (R n) v (b n) (c n) (w n)‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_log_budget_le_power (1/65536) (by norm_num),
      hl.eventually_lt_const he] with n nBig logb final
    have hn : 1 ≤ n := (show 1 ≤ (2 : ℕ) by decide).trans nBig
    have nr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have np : (0 : ℝ) < n := zero_lt_one.trans_le nr
    have D0 := zero_le_one.trans D1
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/65536 : ℝ)
    let T := (4*D)*X^3
    have X1 : 1 ≤ X := Real.one_le_rpow nr (by norm_num)
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) D1) (one_le_pow₀ X1)
    have cp : (4 : ℝ)^(1/65536 : ℝ) ≤ 4 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have divs (m : ℕ) (hm : m ≤ 4*n^3) : (m.divisors.card : ℝ) ≤ T := by
      calc
        _ ≤ D*((4*n^3 : ℕ) : ℝ)^(1/(65536 : ℕ) : ℝ) := db (4*n^3) m hm
        _ = D*((4 : ℝ)^(1/65536 : ℝ)*X^3) := by
          push_cast
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul np.le]
          unfold X
          rw [← Real.rpow_mul_natCast np.le]
          norm_num
        _ ≤ D*(4*X^3) := by gcongr
        _ = _ := by unfold T; ring
    have divN (u : ℕ) (h : u ≤ n) : (u.divisors.card : ℝ) ≤ T := by
      have nn : n ≤ 4*n^3 := calc
        n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ hn (show 1 ≤ 3 by decide)
        _ ≤ _ := by omega
      exact divs u (h.trans nn)
    have ex : (n : ℝ)^(1023/1024 : ℝ)*X^29 = (n : ℝ)^(-(35/65536) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast np.le, ← Real.rpow_add np, ← Real.rpow_add_one np.ne']
      congr 1
      norm_num
    calc
      _ ≤ 56832*(n : ℝ)^(1023/1024 : ℝ)*T^8*logBudget n^5 := norm_bounded_divided_slice_le lower upper nBig (J n) (R n) v (b n) (c n) (w n) (subset n) (data n) T1 divs
          (bounds n (by omega)) (steps n) (weights n T1 divN)
      _ ≤ 56832*(n : ℝ)^(1023/1024 : ℝ)*T^8*X^5 := by gcongr
      _ = C*((n : ℝ)^(1023/1024 : ℝ)*X^29) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(35/65536) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right final.le np.le
  obtain ⟨N,h⟩ := eventually_atTop.mp bound
  exact ⟨N,fun n hn _ => h n hn⟩

end

end B13BoundedStepProductSavingProof

end

/- Outer right factor geometry -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical

noncomputable section

def outerRightFactorCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(85/256 : ℝ)⌋₊

theorem grouped_right_high_factor_le_outer_cap {n : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ groupedRightHighItems n) (h : t.1*t.2 ≤ expandedWideStepCap n) :
    t.2 ≤ outerRightFactorCap n := by
  let N := (n : ℝ)
  have row := mem_product.mp (mem_filter.mp ht).1
  have rLower : N^(1/3 : ℝ) ≤ (t.1 : ℝ) := (Nat.lt_floor_add_one _).le.trans (by
    have nat : cutoffB n+1 ≤ t.1 := Nat.succ_le_of_lt (mem_Ioc.mp row.1).1
    change (cutoffB n : ℝ)+1 ≤ (t.1 : ℝ)
    exact_mod_cast nat)
  have np : 0 < N := by
    change (0 : ℝ) < (n : ℝ)
    exact_mod_cast ((Nat.zero_lt_one.trans_le (mem_Icc.mp row.2).1).trans_le (mem_Icc.mp row.2).2)
  have top : (t.1 : ℝ)*(t.2 : ℝ) ≤ N^(511/768 : ℝ) :=
    (by exact_mod_cast h : (t.1 : ℝ)*(t.2 : ℝ) ≤ (expandedWideStepCap n : ℝ)).trans (Nat.floor_le (by positivity))
  apply Nat.le_floor
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (1/3 : ℝ))).mp
  calc
    (t.2 : ℝ)*N^(1/3 : ℝ) ≤ (t.2 : ℝ)*(t.1 : ℝ) := mul_le_mul_of_nonneg_left rLower (by positivity)
    _ ≤ N^(511/768 : ℝ) := by simpa only [mul_comm] using top
    _ = N^(85/256 : ℝ)*N^(1/3 : ℝ) := by rw [← Real.rpow_add np]; norm_num

end

end B13BoundedStepProductSavingProof

end

/- Outer right windows geometry -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def outerRightRows (n : ℕ) : Finset (ℕ × ℕ) :=
  (bilateralLeftWaveItems n).filter fun i =>
    let m := leftBilinearStep i
    m^2 ≤ n ∧ (n : ℝ)^(171/512 : ℝ) ≤ (m : ℝ) ∧ m.gcd n ≤ thinHighLeftDivisorCap n

end

end B13BoundedStepProductSavingProof

end

/- Swapped high window gate -/
section

namespace B13BoundedStepProductSavingProof

open DyadicMixedB4Scale
open scoped Classical

noncomputable section

theorem swapped_high_tail_gate_iff {n m g e a j : ℕ}
    (a0 : 0 < a) (j0 : 0 < j) (h0 : 0 < g/e) (jn : j ≤ n) :
    (swappedHighTailLower n g e < (j : ℤ) ∧ (j : ℤ) ≤ swappedHighTailUpper n m g e a) ↔
      (cutoffB n < (g/e)*j ∧ (g/e)*j ≤ min (splitCut n) (n/(rightLargeCofactorCut n+1))) ∧
        swappedHighPrefixLower n e a ≤ (n/g-m/g)/(a*j) := by
  let h := g/e
  let P := min (splitCut n) (n/(rightLargeCofactorCut n+1))
  let b := swappedHighPrefixLower n e a
  let M := n/g-m/g
  change ((((cutoffB n/h : ℕ) : ℤ) < (j : ℤ)) ∧
    (j : ℤ) ≤ ((min (P/h) (if b=0 then n else M/(a*b)) : ℕ) : ℤ)) ↔
    ((cutoffB n < h*j ∧ h*j ≤ P) ∧ b ≤ M/(a*j))
  simp only [Int.ofNat_lt,Int.ofNat_le,le_min_iff]
  rw [Nat.div_lt_iff_lt_mul h0,Nat.le_div_iff_mul_le h0,Nat.mul_comm j h]
  by_cases b0 : b=0
  · simp [b0,jn]
  · have line : j ≤ M/(a*b) ↔ b ≤ M/(a*j) := by
      rw [Nat.le_div_iff_mul_le (mul_pos a0 (Nat.pos_of_ne_zero b0)),
        Nat.le_div_iff_mul_le (mul_pos a0 j0)]
      congr 1
      ring
    simp only [ite_eq_right b0,line]
    tauto

theorem swapped_high_full_gate_iff {n m g e l r a : ℕ} {z : ℤ}
    (a0 : 0 < a) (z0 : 0 < z) (h0 : 0 < g/e) (zn : z.toNat ≤ n) :
    (max ((l/a : ℕ) : ℤ) (swappedHighTailLower n g e) < z ∧
      z ≤ min ((r/a : ℕ) : ℤ) (swappedHighTailUpper n m g e a)) ↔
      (l < a*z.toNat ∧ a*z.toNat ≤ r) ∧
      (cutoffB n < (g/e)*z.toNat ∧ (g/e)*z.toNat ≤ min (splitCut n) (n/(rightLargeCofactorCut n+1))) ∧
      swappedHighPrefixLower n e a ≤ (n/g-m/g)/(a*z.toNat) := by
  have positive : 0 < z.toNat := by omega
  have cast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg z0.le
  have core := swapped_high_tail_gate_iff (m := m) a0 positive h0 zn
  rw [cast] at core
  have prod : ((((l/a : ℕ) : ℤ) < z) ∧ (z ≤ ((r/a : ℕ) : ℤ))) ↔
      (l < a*z.toNat ∧ a*z.toNat ≤ r) := by
    rw [← cast]
    simp only [Int.ofNat_lt,Int.ofNat_le,Int.toNat_natCast,Nat.div_lt_iff_lt_mul a0,Nat.le_div_iff_mul_le a0,Nat.mul_comm z.toNat a]
  simp only [max_lt_iff,le_min_iff] at ⊢ core
  tauto

end

end B13BoundedStepProductSavingProof

end

/- Swapped high window bridge -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def swappedHighGroupedStep (t : ℕ × ℕ) : ℕ := t.2*t.1

def swappedHighGroupedWeight (n : ℕ) (t : ℕ × ℕ) : ℂ :=
  (rightHighWaveFactor n t.2 : ℂ)*groupedRightHighMoebius n t.1

def swappedHighGroupedResidue (n m : ℕ) (t : ℕ × ℕ) : ℂ :=
  let v := swappedHighGroupedStep t
  swappedHighGroupedWeight n t *
    (pairResidueError n v m (rightLargeCofactorCut n/t.2) (n/v) 0 (n/m) : ℂ)

end

end B13BoundedStepProductSavingProof

end

/- Residue swap family -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

def pairResidueSwapFamily (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if gate i j then
    a i*b j*((pairResidueError n (u i) (v j) (l i) (r i) (p j) (s j) : ℂ) -
      (pairResidueError n (v j) (u i) (p j) (s j) (l i) (r i) : ℂ)) else 0

theorem pair_residue_swap_family_eq_rounding_difference (n : ℕ) {α β : Type*}
    (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    (u0 : ∀ i ∈ I, 0 < u i) (v0 : ∀ j ∈ J, 0 < v j) :
    pairResidueSwapFamily n I J u l r v p s a b gate =
      volumeRoundingFamily n J I v p s u l r b a (fun j i => gate i j) -
        volumeRoundingFamily n I J u l r v p s a b gate := by
  unfold pairResidueSwapFamily volumeRoundingFamily
  rw [sum_comm (s := J) (t := I),← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  by_cases ok : gate i j
  · by_cases gcd : (u i).gcd (v j) ∣ n
    · have gc : (v j).gcd (u i) ∣ n := by rwa [Nat.gcd_comm]
      rw [if_pos ok,if_pos ⟨ok,gc⟩,if_pos ⟨ok,gcd⟩]
      rw [← Complex.ofReal_sub, residue_error_swap_diff_eq_volume_diff (u0 i hi) (v0 j hj),
        Complex.ofReal_sub, Nat.gcd_comm (v j) (u i), ← overlap_mass_swap n (u i) (v j) (l i) (r i) (p j) (s j)]
      ring
    · have gc : ¬(v j).gcd (u i) ∣ n := by rwa [Nat.gcd_comm]
      rw [if_pos ok,if_neg (fun h => gc h.2),if_neg (fun h => gcd h.2)]
      simp [pairResidueError,gcd,gc]
  · simp [ok]

theorem norm_pair_residue_swap_family_le (n A : ℕ) (n0 : 0 < n) (A0 : 0 < A)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    {W : ℝ} (W0 : 0 ≤ W) (uSteps : ∀ i ∈ I, u i ∈ Icc 1 A) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 A)
    (uWeights : ∀ x ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i=x), ‖a i‖) ≤ W)
    (vWeights : ∀ x ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j=x), ‖b j‖) ≤ W) :
    ‖pairResidueSwapFamily n I J u l r v p s a b gate‖ ≤
      24*W^2*(A : ℝ)*(1+Real.log (A : ℝ))*(n.divisors.card : ℝ) := by
  have first := norm_volume_rounding_family_le n A n0 A0 I J u l r v p s a b gate W0 uSteps vSteps uWeights vWeights
  have other := norm_volume_rounding_family_le n A n0 A0 J I v p s u l r b a (fun j i => gate i j)
    W0 vSteps uSteps vWeights uWeights
  rw [pair_residue_swap_family_eq_rounding_difference n I J u l r v p s a b gate
    (fun i hi => (mem_Icc.mp (uSteps i hi)).1) (fun j hj => (mem_Icc.mp (vSteps j hj)).1)]
  exact (norm_sub_le _ _).trans ((add_le_add other first).trans_eq (by ring))

end

end B13BoundedStepProductSavingProof

end

/- Outer right wave conversion -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

def outerRightHighItems (n : ℕ) : Finset RightHighWaveIndex :=
  expandedWaveItems n (rightHighWaveItems n) rightHighWaveStep

end

end B13BoundedStepProductSavingProof

end

/- Right bounded cuts -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open scoped Classical Finset

noncomputable section

def boundedRightProductGate (gate : ℕ → (ℕ × ℕ) → RightHighWaveIndex → Prop) (n : ℕ) (i : ℕ × ℕ) (j : RightHighWaveIndex) : Prop :=
  gate n i j ∧ thinHighProductCap n < leftBilinearStep i*rightHighWaveStep j

def boundedRightProductCut (gate : ℕ → (ℕ × ℕ) → RightHighWaveIndex → Prop) (n : ℕ) : ℂ :=
  smallProductResidueFamily n (thinHighProductCap n) (thinHighLeftItems n) (outerRightHighItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightHighWaveStep (rightHighWaveLower n) (fun j => n/rightHighWaveStep j)
    (leftBilinearWeight n) (rightHighWaveWeight n) (gate n)

def boundedRightCommonCut (gate : ℕ → (ℕ × ℕ) → RightHighWaveIndex → Prop) (n : ℕ) : ℂ :=
  gcdResidueFamily n (thinHighGcdCap n) (thinHighLeftItems n) (outerRightHighItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightHighWaveStep (rightHighWaveLower n) (fun j => n/rightHighWaveStep j)
    (leftBilinearWeight n) (rightHighWaveWeight n) (boundedRightProductGate gate n)

def boundedRightTargetCut (gate : ℕ → (ℕ × ℕ) → RightHighWaveIndex → Prop) (n : ℕ) : ℂ :=
  largeLeftDivisorResidueFamily n (thinHighLeftDivisorCap n) (thinHighGcdCap n)
    (thinHighLeftItems n) (outerRightHighItems n) leftBilinearStep rightHighWaveStep
    (rightHighWaveLower n) (fun j => n/rightHighWaveStep j)
    (leftBilinearWeight n) (rightHighWaveWeight n) (boundedRightProductGate gate n)

def boundedRightCuts (gate : ℕ → (ℕ × ℕ) → RightHighWaveIndex → Prop) (n : ℕ) : ℂ :=
  boundedRightProductCut gate n + boundedRightCommonCut gate n + boundedRightTargetCut gate n

theorem norm_bounded_right_cuts_le (gate : ℕ → (ℕ × ℕ) → RightHighWaveIndex → Prop) {n : ℕ} (n0 : 0 < n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖boundedRightCuts gate n‖ ≤ 5*(n : ℝ)^(8191/8192 : ℝ)*T^9*logBudget n^4 := by
  let A := expandedWideStepCap n
  let N := (n : ℝ)
  let L := logBudget n
  let W := T^3*L
  let P := thinHighProductCap n
  let D := thinHighGcdCap n
  let E := thinHighLeftDivisorCap n
  have n1 : 1 ≤ N := by change (1 : ℝ) ≤ (n : ℝ); exact_mod_cast n0
  have np : 0 < N := zero_lt_one.trans_le n1
  have Ap := expanded_wide_step_pos n0
  have An := expanded_wide_step_le n0
  have T0 := zero_le_one.trans T1
  have L1 := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have W0 : 0 ≤ W := by unfold W; positivity
  have range {α : Type} {S : Finset α} {u : α → ℕ} (h : ∀ x ∈ S, u x ∈ Icc 1 n) (x : α)
      (hx : x ∈ expandedWaveItems n S u) : u x ∈ Icc 1 A := by
    obtain ⟨base,limit⟩ := mem_filter.mp hx
    exact mem_Icc.mpr ⟨(mem_Icc.mp (h x base)).1,limit⟩
  have mass {α : Type} {S : Finset α} {u : α → ℕ} {a : α → ℂ}
      (h : ∀ m ∈ Icc 1 n, (∑ i ∈ S.filter (fun i => u i=m), ‖a i‖) ≤ W)
      (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ i ∈ (expandedWaveItems n S u).filter (fun i => u i=m), ‖a i‖) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (h m (Icc_subset_Icc_right An hm))
  have leftRange (i : ℕ × ℕ) (hi : i ∈ thinHighLeftItems n) : leftBilinearStep i ∈ Icc 1 A := by
    obtain ⟨base,cap⟩ := mem_filter.mp hi
    exact mem_Icc.mpr ⟨(mem_Icc.mp (bilateral_left_step_range base)).1, cap.trans (extended_step_cap_le_expanded n)⟩
  have rightRange (j : RightHighWaveIndex) (hj : j ∈ outerRightHighItems n) : rightHighWaveStep j ∈ Icc 1 A :=
    range (u := rightHighWaveStep) (fun _ h => bilateral_right_high_step_range h) j hj
  have leftMass (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ i ∈ (thinHighLeftItems n).filter (fun i => leftBilinearStep i=m), ‖leftBilinearWeight n i‖) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _)) (fun _ _ _ => norm_nonneg _)).trans
      (norm_bilateral_left_step_mass n0 T0 divisors m (Icc_subset_Icc_right An hm))
  have rightMass := mass (norm_bilateral_right_high_step_mass T0 divisors)
  have logN : 1+Real.log N ≤ L := by
    unfold L logBudget
    linarith only [Real.log_le_log np (show N ≤ (n : ℝ)+2 by dsimp [N]; linarith)]
  have logA : 1+Real.log (A : ℝ) ≤ L := by
    have h : (A : ℝ) ≤ N := by
      change (expandedWideStepCap n : ℝ) ≤ (n : ℝ)
      exact_mod_cast An
    linarith only [Real.log_le_log (by exact_mod_cast Ap : (0 : ℝ) < A) h, logN]
  have logN0 : 0 ≤ 1+Real.log N := add_nonneg zero_le_one (Real.log_nonneg n1)
  have product := norm_small_product_residue_family_le n P A (thinHighLeftItems n) (outerRightHighItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) rightHighWaveStep (rightHighWaveLower n)
    (fun j => n/rightHighWaveStep j) (leftBilinearWeight n) (rightHighWaveWeight n)
    (gate n) W0 leftRange rightRange leftMass rightMass
  have common := norm_gcd_residue_family_le (D := D) n0 An (thinHighLeftItems n) (outerRightHighItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) rightHighWaveStep (rightHighWaveLower n)
    (fun j => n/rightHighWaveStep j) (leftBilinearWeight n) (rightHighWaveWeight n)
    (boundedRightProductGate gate n) W0 T0 divisors leftRange rightRange leftMass rightMass
  have target := norm_large_left_divisor_residue_family_le (D := E) (G := D) n0 An
    (thinHighLeftItems n) (outerRightHighItems n) leftBilinearStep rightHighWaveStep (rightHighWaveLower n)
    (fun j => n/rightHighWaveStep j) (leftBilinearWeight n) (rightHighWaveWeight n)
    (boundedRightProductGate gate n) W0 T0 divisors leftRange rightRange leftMass rightMass
  let H := N^(8191/8192 : ℝ)
  have Ptop : (P : ℝ) ≤ H := Nat.floor_le (by positivity)
  have Dtop : (D : ℝ) ≤ N^(1/4096 : ℝ) := Nat.floor_le (by positivity)
  have Ddiv : N/((D : ℝ)+1) ≤ N^(4095/4096 : ℝ) := by
    calc
      _ ≤ N/N^(1/4096 : ℝ) := div_le_div_of_nonneg_left np.le (by positivity) (Nat.lt_floor_add_one _).le
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub np]; norm_num
  have Ediv : N/((E : ℝ)+1) ≤ N^(2047/2048 : ℝ) := by
    calc
      _ ≤ N/N^(1/2048 : ℝ) := div_le_div_of_nonneg_left np.le (by positivity) (Nat.lt_floor_add_one _).le
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub np]; norm_num
  have bProduct : ‖boundedRightProductCut gate n‖ ≤ H*T^9*L^4 := by
    refine product.trans ?_
    calc
      _ ≤ W^2*H*L := by gcongr
      _ = H*T^6*L^3 := by unfold W; ring
      _ ≤ _ := by
        have ht : T^6 ≤ T^9 := pow_le_pow_right₀ T1 (by decide)
        have hl : L^3 ≤ L^4 := pow_le_pow_right₀ L1 (by decide)
        gcongr
  have bCommon : ‖boundedRightCommonCut gate n‖ ≤ 2*H*T^9*L^4 := by
    refine common.trans ?_
    have d := Ddiv.trans (Real.rpow_le_rpow_of_exponent_le n1 (by norm_num :
      (4095/4096 : ℝ) ≤ 8191/8192))
    have sq : (1+Real.log N)^2 ≤ L^2 := pow_le_pow_left₀ logN0 logN 2
    have l : T^2+(1+Real.log N)^2 ≤ 2*T^2*L^2 := by
      have x := le_mul_of_one_le_right (sq_nonneg T) (one_le_pow₀ L1 (n := 2))
      have y := sq.trans (le_mul_of_one_le_left (sq_nonneg L) (one_le_pow₀ T1 (n := 2)))
      linarith only [x,y]
    calc
      _ ≤ T*(W^2*H*(2*T^2*L^2)) := by gcongr
      _ = _ := by unfold W; ring
  have bTarget : ‖boundedRightTargetCut gate n‖ ≤ 2*H*T^9*L^4 := by
    refine target.trans ?_
    have d : 1 ≤ N^(1/4096 : ℝ) := Real.one_le_rpow n1 (by norm_num)
    have ht : T^2+(D : ℝ)*L^2 ≤ 2*N^(1/4096 : ℝ)*T^2*L^2 := by
      have a := (le_mul_of_one_le_left (sq_nonneg T) d).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ L1 (n := 2)))
      have b := mul_le_mul_of_nonneg_right
        (Dtop.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ T1 (n := 2)))) (sq_nonneg L)
      linarith only [a,b]
    calc
      _ ≤ T*(W^2*N^(2047/2048 : ℝ)*(2*N^(1/4096 : ℝ)*T^2*L^2)) := by gcongr
      _ = 2*(N^(2047/2048 : ℝ)*N^(1/4096 : ℝ))*T^9*L^4 := by unfold W; ring
      _ ≤ _ := by
        have ex : N^(2047/2048 : ℝ)*N^(1/4096 : ℝ) ≤ H := by
          rw [← Real.rpow_add np]
          exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        gcongr
  exact (norm_add_le _ _).trans
    ((add_le_add ((norm_add_le _ _).trans (add_le_add bProduct bCommon)) bTarget).trans_eq (by unfold H N L; ring))

theorem saving_of_bounded_right_growth (f : ℕ → ℂ) {K : ℝ} (K0 : 0 ≤ K)
    (bound : ∀ n : ℕ, 0 < n → ∀ T : ℝ, 1 ≤ T →
      (∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) →
        ‖f n‖ ≤ K*(n : ℝ)^(8191/8192 : ℝ)*T^9*logBudget n^4) : saving f := by
  intro ε he
  obtain ⟨D,D1,dBound⟩ := divisor_envelope_at_power 262144 (by decide)
  let C := K*D^9
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-(19/262144) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 19/262144)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(19/262144) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have estimate : ∀ᶠ n : ℕ in atTop, ‖f n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le_power (1/262144) (by norm_num),
      scaled.eventually_lt_const he] with n hn logb small
    have nr : (0 : ℝ) < n := by exact_mod_cast hn
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/262144 : ℝ)
    let T := D*X
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1
      (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))
    have ex : (n : ℝ)^(8191/8192 : ℝ)*X^13 =
        (n : ℝ)^(-(19/262144) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast nr.le,← Real.rpow_add nr,← Real.rpow_add_one nr.ne']
      congr 1
      norm_num
    calc
      _ ≤ K*(n : ℝ)^(8191/8192 : ℝ)*T^9*logBudget n^4 :=
        bound n hn T T1 (dBound n)
      _ ≤ K*(n : ℝ)^(8191/8192 : ℝ)*T^9*X^4 := by gcongr
      _ = C*((n : ℝ)^(8191/8192 : ℝ)*X^13) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(19/262144) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
  obtain ⟨N,h⟩ := eventually_atTop.mp estimate
  exact ⟨N,fun n hn _ => h n hn⟩

theorem bounded_right_cuts_saving (gate : ℕ → (ℕ × ℕ) → RightHighWaveIndex → Prop) :
    saving (fun n => boundedRightCuts gate n) :=
  saving_of_bounded_right_growth _ (by norm_num) (fun _ hn _ ht d => norm_bounded_right_cuts_le gate hn ht d)

end

end B13BoundedStepProductSavingProof

end

/- Bounded outer left arithmetic -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open scoped Classical Finset

noncomputable section

def boundedOuterLeftKeptGate (gate : ℕ → ℕ → ℕ → Prop) (n u v : ℕ) : Prop :=
  gate n u v ∧ thinHighProductCap n < u*v ∧
    u.gcd v ≤ thinHighGcdCap n ∧ v.gcd n ≤ targetDivisorCap n

def boundedOuterLeftKeptFrom (gate : ℕ → ℕ → ℕ → Prop) (n : ℕ) {κ : Type} (J : Finset κ)
    (v b c : κ → ℕ) (w : κ → ℂ) : ℂ :=
  ∑ i ∈ expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep,
  ∑ j ∈ expandedWaveItems n J v,
    if boundedOuterLeftKeptGate gate n (leftBilinearStep i) (v j) then
      leftBilinearWeight n i*w j*
        (pairResidueError n (leftBilinearStep i) (v j) 0 (n/leftBilinearStep i) (b j) (c j) : ℂ)
    else 0

def boundedOuterLeftBaseFrom (gate : ℕ → ℕ → ℕ → Prop) (n : ℕ) {κ : Type} (J : Finset κ) (v b c : κ → ℕ) (w : κ → ℂ) : ℂ :=
  ∑ i ∈ expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep,
  ∑ j ∈ expandedWaveItems n J v,
    if gate n (leftBilinearStep i) (v j) then
      leftBilinearWeight n i*w j*
        (pairResidueError n (leftBilinearStep i) (v j) 0 (n/leftBilinearStep i) (b j) (c j) : ℂ)
    else 0

private def boundedOuterLeftThinGate (gate : ℕ → ℕ → ℕ → Prop) (n u v : ℕ) : Prop :=
  gate n u v ∧ thinHighProductCap n < u*v

private def boundedOuterLeftProductCut (gate : ℕ → ℕ → ℕ → Prop) (n : ℕ) {κ : Type} (J : Finset κ) (v b c : κ → ℕ) (w : κ → ℂ) : ℂ :=
  smallProductResidueFamily n (thinHighProductCap n)
    (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep) (expandedWaveItems n J v)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) v b c (leftBilinearWeight n) w
    (fun i j => gate n (leftBilinearStep i) (v j))

private def boundedOuterLeftCommonCut (gate : ℕ → ℕ → ℕ → Prop) (n : ℕ) {κ : Type} (J : Finset κ) (v b c : κ → ℕ) (w : κ → ℂ) : ℂ :=
  gcdResidueFamily n (thinHighGcdCap n)
    (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep) (expandedWaveItems n J v)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) v b c (leftBilinearWeight n) w
    (fun i j => boundedOuterLeftThinGate gate n (leftBilinearStep i) (v j))

private def boundedOuterLeftTargetCut (gate : ℕ → ℕ → ℕ → Prop) (n : ℕ) {κ : Type} (J : Finset κ) (v b c : κ → ℕ) (w : κ → ℂ) : ℂ :=
  largeRightDivisorResidueFamily n (targetDivisorCap n) (thinHighGcdCap n)
    (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep) (expandedWaveItems n J v)
    leftBilinearStep v b c (leftBilinearWeight n) w
    (fun i j => boundedOuterLeftThinGate gate n (leftBilinearStep i) (v j))

def boundedOuterLeftCut (gate : ℕ → ℕ → ℕ → Prop) (n : ℕ) {κ : Type} (J : Finset κ) (v b c : κ → ℕ) (w : κ → ℂ) : ℂ :=
  boundedOuterLeftProductCut gate n J v b c w + boundedOuterLeftCommonCut gate n J v b c w + boundedOuterLeftTargetCut gate n J v b c w

theorem bounded_outer_left_base_eq_partition (gate : ℕ → ℕ → ℕ → Prop) (n : ℕ) {κ : Type} (J : Finset κ) (v b c : κ → ℕ) (w : κ → ℂ) :
    boundedOuterLeftBaseFrom gate n J v b c w = boundedOuterLeftKeptFrom gate n J v b c w + boundedOuterLeftCut gate n J v b c w := by
  unfold boundedOuterLeftBaseFrom boundedOuterLeftKeptFrom boundedOuterLeftCut boundedOuterLeftProductCut boundedOuterLeftCommonCut boundedOuterLeftTargetCut
    smallProductResidueFamily gcdResidueFamily largeRightDivisorResidueFamily
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  let u := leftBilinearStep i
  let m := v j
  by_cases base : gate n u m
  · by_cases p : u*m ≤ thinHighProductCap n
    · simp [u,m,base,p,not_lt.mpr p,boundedOuterLeftKeptGate,boundedOuterLeftThinGate]
    · by_cases g : u.gcd m ≤ thinHighGcdCap n
      · by_cases t : m.gcd n ≤ targetDivisorCap n <;>
          simp [u,m,base,p,lt_of_not_ge p,g,not_lt.mpr g,t,lt_of_not_ge,
            boundedOuterLeftKeptGate,boundedOuterLeftThinGate]
      · simp [u,m,base,p,lt_of_not_ge p,g,lt_of_not_ge g,boundedOuterLeftKeptGate,boundedOuterLeftThinGate]
  · simp [u,m,base,boundedOuterLeftKeptGate,boundedOuterLeftThinGate]

private theorem norm_bounded_outer_left_cut_le (gate : ℕ → ℕ → ℕ → Prop) {n : ℕ} (n0 : 0 < n) {κ : Type}
    (J : Finset κ) (v b c : κ → ℕ) (w : κ → ℂ)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (steps : ∀ j ∈ J, v j ∈ Icc 1 n)
    (weights : ∀ m ∈ Icc 1 n, (∑ j ∈ J.filter (fun j => v j=m), ‖w j‖) ≤ T^3*logBudget n) :
    ‖boundedOuterLeftCut gate n J v b c w‖ ≤ 5*(n : ℝ)^(8191/8192 : ℝ)*T^9*logBudget n^4 := by
  let I := expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep
  let R := expandedWaveItems n J v
  let A := expandedWideStepCap n
  let N := (n : ℝ)
  let L := logBudget n
  let W := T^3*L
  let P := thinHighProductCap n
  let D := thinHighGcdCap n
  let E := targetDivisorCap n
  have n1 : 1 ≤ N := by change (1 : ℝ) ≤ (n : ℝ); exact_mod_cast n0
  have np : 0 < N := zero_lt_one.trans_le n1
  have Ap := expanded_wide_step_pos n0
  have An := expanded_wide_step_le n0
  have T0 := zero_le_one.trans T1
  have L1 := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have W0 : 0 ≤ W := by unfold W; positivity
  have range {α : Type} {S : Finset α} {u : α → ℕ} (h : ∀ x ∈ S, u x ∈ Icc 1 n) (x : α)
      (hx : x ∈ expandedWaveItems n S u) : u x ∈ Icc 1 A := by
    obtain ⟨base,limit⟩ := mem_filter.mp hx
    exact mem_Icc.mpr ⟨(mem_Icc.mp (h x base)).1,limit⟩
  have mass {α : Type} {S : Finset α} {u : α → ℕ} {a : α → ℂ}
      (h : ∀ m ∈ Icc 1 n, (∑ i ∈ S.filter (fun i => u i=m), ‖a i‖) ≤ W)
      (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ i ∈ (expandedWaveItems n S u).filter (fun i => u i=m), ‖a i‖) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (h m (Icc_subset_Icc_right An hm))
  have leftRange (i : ℕ × ℕ) (hi : i ∈ I) : leftBilinearStep i ∈ Icc 1 A :=
    range (u := leftBilinearStep) (fun _ h => bilateral_left_step_range h) i hi
  have rightRange (j : κ) (hj : j ∈ R) : v j ∈ Icc 1 A := range steps j hj
  have leftMass := mass (norm_bilateral_left_step_mass n0 T0 divisors)
  have rightMass := mass weights
  have logN : 1+Real.log N ≤ L := by
    unfold L logBudget
    linarith only [Real.log_le_log np (show N ≤ (n : ℝ)+2 by dsimp [N]; linarith)]
  have logA : 1+Real.log (A : ℝ) ≤ L := by
    have h : (A : ℝ) ≤ N := by
      change (expandedWideStepCap n : ℝ) ≤ (n : ℝ)
      exact_mod_cast An
    linarith only [Real.log_le_log (by exact_mod_cast Ap : (0 : ℝ) < A) h, logN]
  have logN0 : 0 ≤ 1+Real.log N := add_nonneg zero_le_one (Real.log_nonneg n1)
  have product := norm_small_product_residue_family_le n P A I R
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) v b c (leftBilinearWeight n) w
    (fun i j => gate n (leftBilinearStep i) (v j)) W0 leftRange rightRange leftMass rightMass
  have common := norm_gcd_residue_family_le (D := D) n0 An I R
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) v b c (leftBilinearWeight n) w
    (fun i j => boundedOuterLeftThinGate gate n (leftBilinearStep i) (v j)) W0 T0 divisors leftRange rightRange leftMass rightMass
  have target := norm_large_right_divisor_residue_family_le (D := E) (G := D) n0 An I R
    leftBilinearStep v b c (leftBilinearWeight n) w
    (fun i j => boundedOuterLeftThinGate gate n (leftBilinearStep i) (v j)) W0 T0 divisors leftRange rightRange leftMass rightMass
  let H := N^(8191/8192 : ℝ)
  have Ptop : (P : ℝ) ≤ H := Nat.floor_le (by positivity)
  have Dtop : (D : ℝ) ≤ N^(1/4096 : ℝ) := Nat.floor_le (by positivity)
  have Ddiv : N/((D : ℝ)+1) ≤ N^(4095/4096 : ℝ) := by
    calc
      _ ≤ N/N^(1/4096 : ℝ) := div_le_div_of_nonneg_left np.le (by positivity) (Nat.lt_floor_add_one _).le
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub np]; norm_num
  have Ediv : N/((E : ℝ)+1) ≤ N^(127/128 : ℝ) := by
    calc
      _ ≤ N/N^(1/128 : ℝ) := div_le_div_of_nonneg_left np.le (by positivity) (Nat.lt_floor_add_one _).le
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub np]; norm_num
  have bProduct : ‖boundedOuterLeftProductCut gate n J v b c w‖ ≤ H*T^9*L^4 := by
    refine product.trans ?_
    calc
      _ ≤ W^2*H*L := by gcongr
      _ = H*T^6*L^3 := by unfold W; ring
      _ ≤ _ := by
        have ht : T^6 ≤ T^9 := pow_le_pow_right₀ T1 (by decide)
        have hl : L^3 ≤ L^4 := pow_le_pow_right₀ L1 (by decide)
        gcongr
  have bCommon : ‖boundedOuterLeftCommonCut gate n J v b c w‖ ≤ 2*H*T^9*L^4 := by
    refine common.trans ?_
    have d := Ddiv.trans (Real.rpow_le_rpow_of_exponent_le n1 (by norm_num :
      (4095/4096 : ℝ) ≤ 8191/8192))
    have sq : (1+Real.log N)^2 ≤ L^2 := pow_le_pow_left₀ logN0 logN 2
    have l : T^2+(1+Real.log N)^2 ≤ 2*T^2*L^2 := by
      have x := le_mul_of_one_le_right (sq_nonneg T) (one_le_pow₀ L1 (n := 2))
      have y := sq.trans (le_mul_of_one_le_left (sq_nonneg L) (one_le_pow₀ T1 (n := 2)))
      linarith only [x,y]
    calc
      _ ≤ T*(W^2*H*(2*T^2*L^2)) := by gcongr
      _ = _ := by unfold W; ring
  have bTarget : ‖boundedOuterLeftTargetCut gate n J v b c w‖ ≤ 2*H*T^9*L^4 := by
    refine target.trans ?_
    have d : 1 ≤ N^(1/4096 : ℝ) := Real.one_le_rpow n1 (by norm_num)
    have ht : T^2+(D : ℝ)*L^2 ≤ 2*N^(1/4096 : ℝ)*T^2*L^2 := by
      have a := (le_mul_of_one_le_left (sq_nonneg T) d).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ L1 (n := 2)))
      have b := mul_le_mul_of_nonneg_right
        (Dtop.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ T1 (n := 2)))) (sq_nonneg L)
      linarith only [a,b]
    calc
      _ ≤ T*(W^2*N^(127/128 : ℝ)*(2*N^(1/4096 : ℝ)*T^2*L^2)) := by gcongr
      _ = 2*(N^(127/128 : ℝ)*N^(1/4096 : ℝ))*T^9*L^4 := by unfold W; ring
      _ ≤ _ := by
        have ex : N^(127/128 : ℝ)*N^(1/4096 : ℝ) ≤ H := by
          rw [← Real.rpow_add np]
          exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        gcongr
  exact (norm_add_le _ _).trans
    ((add_le_add ((norm_add_le _ _).trans (add_le_add bProduct bCommon)) bTarget).trans_eq (by unfold H N L; ring))

theorem bounded_outer_left_cut_saving (gate : ℕ → ℕ → ℕ → Prop) {κ : Type} (J : ℕ → Finset κ)
    (v : κ → ℕ) (b c : ℕ → κ → ℕ) (w : ℕ → κ → ℂ)
    (steps : ∀ n, ∀ j ∈ J n, v j ∈ Icc 1 n)
    (weights : ∀ n, ∀ {T : ℝ}, 1 ≤ T → (∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) →
      ∀ m ∈ Icc 1 n, (∑ j ∈ (J n).filter (fun j => v j=m), ‖w n j‖) ≤ T^3*logBudget n) :
    saving (fun n => boundedOuterLeftCut gate n (J n) v (b n) (c n) (w n)) := by
  apply saving_of_bounded_right_growth _ (K := 5) (by norm_num)
  intro n n0 T T1 divs
  exact norm_bounded_outer_left_cut_le gate n0 (J n) v (b n) (c n) (w n) T1 divs
    (steps n) (weights n T1 divs)

end

end B13BoundedStepProductSavingProof

end

/- Sixth moment moderate far budget -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

theorem sixth_moment_moderate_far_envelope_le {n m g A S : ℕ} {x T : ℝ}
    (n1 : 1 ≤ (n : ℝ)) (m1 : 1 ≤ (m : ℝ)) (g1 : 1 ≤ (g : ℝ)) (T0 : 0 ≤ T)
    (xLo : 31/512 ≤ x) (mHi : (m : ℝ) ≤ (n : ℝ)^(535/1024 : ℝ))
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+3/512))
    (sCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512-x)) :
    rectangularMomentEnvelope 6 S ((m : ℝ)*(A : ℝ)^3*T^6) ≤
      2*(n : ℝ)^(1016/1024 : ℝ)*T/((m : ℝ)*(g : ℝ)^(3/2 : ℝ)) := by
  let N := (n : ℝ)
  let M := (m : ℝ)
  let G := (g : ℝ)
  let V := (S : ℝ)
  let C := (A : ℝ)
  let Y := V*M*G^2
  let H := N^(1016/1024 : ℝ)
  let Q := rectangularMomentEnvelope 6 S (M*C^3*T^6)
  have np : 0 < N := zero_lt_one.trans_le n1
  have mp := zero_lt_one.trans_le m1
  have gp := zero_lt_one.trans_le g1
  have C0 : 0 ≤ C := by unfold C; positivity
  have V0 : 0 ≤ V := by unfold V; positivity
  have Q0 : 0 ≤ Q := rectangular_moment_envelope_nonneg _ _ (by positivity)
  have formula : Q*(M*G^(5/3 : ℝ)) = Y^(5/6 : ℝ)*M^(1/3 : ℝ)*C^(1/2 : ℝ)*T := by
    change ((V^5*(M*C^3*T^6))^(1/6 : ℝ))*(M*G^(5/3 : ℝ)) = _
    rw [Real.mul_rpow (by positivity : 0 ≤ V^5) (by positivity : 0 ≤ M*C^3*T^6),
      Real.mul_rpow (by positivity : 0 ≤ M*C^3) (by positivity : 0 ≤ T^6),
      Real.mul_rpow mp.le (by positivity : 0 ≤ C^3)]
    rw [← Real.rpow_natCast_mul V0 5, ← Real.rpow_natCast_mul C0 3, ← Real.rpow_natCast_mul T0 6]
    norm_num only [show ((5 : ℕ) : ℝ)*(1/6 : ℝ) = 5/6 by norm_num,
      show ((3 : ℕ) : ℝ)*(1/6 : ℝ) = 1/2 by norm_num,
      show ((6 : ℕ) : ℝ)*(1/6 : ℝ) = 1 by norm_num, Real.rpow_one]
    unfold Y
    rw [Real.mul_rpow (by positivity : 0 ≤ V*M) (by positivity : 0 ≤ G^2),
      Real.mul_rpow V0 mp.le,← Real.rpow_natCast_mul gp.le]
    have merge : M^(5/6 : ℝ)*M^(1/3 : ℝ) = M^(1/6 : ℝ)*M := by
      rw [← Real.rpow_add mp]
      nth_rw 2 [← Real.rpow_one M]
      rw [← Real.rpow_add mp]
      congr 1
      norm_num
    have eg : ((2 : ℕ) : ℝ)*(5/6 : ℝ) = 5/3 := by norm_num
    rw [eg]
    calc
      _ = V^(5/6 : ℝ)*(M^(1/6 : ℝ)*M)*G^(5/3 : ℝ)*C^(1/2 : ℝ)*T := by ring
      _ = _ := by rw [← merge]; ring
  have yLimit : Y^(5/6 : ℝ) ≤ 2*N^((513/512-x)*(5/6)) := by
    calc
      _ ≤ (2*N^(513/512-x))^(5/6 : ℝ) := Real.rpow_le_rpow (by positivity) sCap (by norm_num)
      _ = (2 : ℝ)^(5/6 : ℝ)*N^((513/512-x)*(5/6)) := by rw [Real.mul_rpow (by norm_num) (by positivity),Real.rpow_mul np.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by positivity)
  have mLimit : M^(1/3 : ℝ) ≤ N^((535/1024 : ℝ)*(1/3)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow mp.le mHi (by norm_num)
  have cLimit : C^(1/2 : ℝ) ≤ N^((x+3/512)*(1/2)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow C0 aCap (by norm_num)
  have bound : Q*(M*G^(5/3 : ℝ)) ≤ 2*H*T := by
    rw [formula]
    calc
      _ ≤ (2*N^((513/512-x)*(5/6)))*N^((535/1024 : ℝ)*(1/3))*N^((x+3/512)*(1/2))*T := by gcongr
      _ = 2*N^((513/512-x)*(5/6)+(535/1024)*(1/3)+(x+3/512)*(1/2))*T := by
        rw [Real.rpow_add np,Real.rpow_add np]
        ring
      _ ≤ _ := by
        have exp : N^((513/512-x)*(5/6)+(535/1024)*(1/3)+(x+3/512)*(1/2)) ≤ H :=
          Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo])
        gcongr
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < M*G^(3/2 : ℝ))).mpr
  have gCmp : G^(3/2 : ℝ) ≤ G^(5/3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le g1 (by norm_num)
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left gCmp mp.le) Q0).trans bound

end

end B13BoundedStepProductSavingProof

end

/- Sixth moment moderate far fixed residue -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

theorem norm_gated_sixth_moment_moderate_far_fixed_endpoints_le {n m g A S : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/128 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (large : (2 : ℝ) ≤ (n : ℝ)^(1/64 : ℝ))
    (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(535/1024 : ℝ)) (mLo : (n : ℝ)^(255/512 : ℝ) ≤ (m : ℝ))
    (xLo : 31/512 ≤ x) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+3/512))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512-x))
    (small : 6*A^5 < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi : ℕ → ℤ) {a b : ℤ} (ab : a ≤ b)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ T) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T*L)
    (divisors : ∀ z ≤ max m (A^3), (z.divisors.card : ℝ) ≤ T) :
    ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun i j => centeredIntIntervalResidue m a b (c*((i : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      6*(n : ℝ)^(1016/1024 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)^(3/2 : ℝ)) := by
  let N := (n : ℝ)
  let M := (m : ℝ)
  let G := (g : ℝ)
  let H := N^(1016/1024 : ℝ)
  let D := ⌊N^(1/32 : ℝ)⌋₊
  let B := 4*H*T^3*L^2/(M*G^(3/2 : ℝ))
  let J := intIntervalModUnits m 0 S
  have np : 0 < N := zero_lt_one.trans_le n1
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have m1 : 1 ≤ M := show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast m0
  have mp : 0 < M := zero_lt_one.trans_le m1
  have gp : 0 < G := zero_lt_one.trans_le g1
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans L1
  have log0 := Real.log_nonneg m1
  have log2 : 2+Real.log (m : ℝ) ≤ 2*L := by linarith only [L1,logBound]
  have B0 : 0 ≤ B := by unfold B H; positivity
  have jProp (j : ℤ) (hj : j ∈ J) : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hj
  have uniform (h : ZMod m) (_ : h ≠ 0) (good : m.gcd h.val ≤ D) :
      ‖gatedBilinearSum I J α β lo hi
        (fun i j => ZMod.stdAddChar ((-(h*c))*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹))‖ ≤ B := by
    let z := -(h*c)
    let q := m.gcd z.val
    let p := inverseFrequencyPeriod m z
    have product : p*q=m := Nat.div_mul_cancel (Nat.gcd_dvd_left m z.val)
    have p0 : 0 < p := inverse_frequency_period_pos z
    have pr : (0 : ℝ) < p := by exact_mod_cast p0
    have a : (m.gcd h.val : ℝ) ≤ N^(1/32 : ℝ) :=
      (by exact_mod_cast good : (m.gcd h.val : ℝ) ≤ (D : ℝ)).trans (Nat.floor_le (by positivity))
    have qCap : (q : ℝ) ≤ N^(5/128 : ℝ) := calc
      _ ≤ (m.gcd h.val : ℝ)*(m.gcd c.val : ℝ) := by
        change (m.gcd (-(h*c)).val : ℝ) ≤ _
        exact_mod_cast gcd_fourier_phase_product_le h c
      _ ≤ N^(1/32 : ℝ)*N^(1/128 : ℝ) := mul_le_mul a charBound (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add np]; norm_num
    have q0 := Nat.gcd_pos_of_pos_left z.val m0
    have per : S ≤ p := by
      have G1 : 1 ≤ G^2 := one_le_pow₀ g1
      have scaled : ((S : ℝ)*(q : ℝ))*(M*G^2) ≤ M*(M*G^2) := calc
        _ = ((S : ℝ)*M*G^2)*(q : ℝ) := by ring
        _ ≤ (2*N^(513/512-x))*N^(5/128 : ℝ) := mul_le_mul cofactorCap qCap (by positivity) (by positivity)
        _ ≤ (N^(1/64 : ℝ)*N^(513/512-x))*N^(5/128 : ℝ) := by gcongr
        _ = N^(513/512-x+5/128+1/64) := by
          rw [Real.rpow_add np,Real.rpow_add np]
          ring
        _ ≤ N^(255/256 : ℝ) := Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo])
        _ = N^(255/512 : ℝ)*N^(255/512 : ℝ) := by rw [← Real.rpow_add np]; norm_num
        _ ≤ M*M := mul_le_mul mLo mLo (by positivity) mp.le
        _ ≤ _ := by
          have b := mul_le_mul_of_nonneg_left G1 (by positivity : 0 ≤ M*M)
          simpa only [mul_one,mul_assoc] using b
      have goodSq : (S : ℝ)*(q : ℝ) ≤ M := (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < M*G^2)).mp scaled
      have nat : S*q ≤ m := by
        change (S : ℝ)*(q : ℝ) ≤ (m : ℝ) at goodSq
        exact_mod_cast goodSq
      rw [← product] at nat
      exact Nat.le_of_mul_le_mul_right nat q0
    let K := M*(A : ℝ)^3*T^6
    have K0 : 0 ≤ K := by unfold K; positivity
    have dTop : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le T0
    have evenMoment (weight : ℕ → ℂ) {X : ℝ} (X0 : 0 ≤ X) (xw : ∀ i ∈ I, ‖weight i‖ ≤ X) :
        (∑ x : ZMod m, ‖inverseFrequencySum m I weight x‖^6) ≤ K*X^6 := by
      have use := inverse_frequency_even_moment_small_le (k := 3) (D := ⌊T⌋₊)
        (show 2*3*A^(2*3-1) < m from small) I Icap copI
        (fun y hy => Nat.le_floor (divisors y (hy.trans (le_max_right _ _)))) weight X0 xw
      refine use.trans ?_
      unfold K M
      gcongr
    have est := norm_gated_inverse_on_reduced_span_of_moment (r := 6) (by decide) z
      (show S ≤ inverseFrequencyPeriod m z from per) 0 I J
      (fun j hj => by simpa only [zero_add] using (jProp j hj).1)
      (fun j hj => (jProp j hj).2) α β lo hi T0 (mul_nonneg T0 L0) K0 aw bw evenMoment
    have size : J.card ≤ S :=
      (card_le_card (fun j hj => (jProp j hj).1)).trans_eq (by rw [Int.card_Ioc,sub_zero,Int.toNat_natCast])
    calc
      _ ≤ (2+Real.log m)*T*(T*L)*rectangularMomentEnvelope 6 J.card K := est
      _ ≤ (2*L)*T*(T*L)*rectangularMomentEnvelope 6 S K :=
        mul_le_mul (by gcongr) (rectangular_moment_envelope_mono_card K0 size)
          (rectangular_moment_envelope_nonneg _ _ K0) (by positivity)
      _ ≤ (2*L)*T*(T*L)*(2*H*T/(M*G^(3/2 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (sixth_moment_moderate_far_envelope_le n1 m1 g1 T0 xLo mHi aCap cofactorCap)
        positivity
      _ = B := by unfold B; ring
  have est := norm_gated_unit_residue_of_divisor_frequency_bound D I (fun i => (i : ZMod m))
    (fun i hi => (ZMod.isUnit_iff_coprime _ _).mpr (copI i hi)) α β lo hi
    (L := 0) (R := (S : ℤ)) ab B0 uniform
  have lMass : (∑ i ∈ I, ‖α i‖) ≤ (A : ℝ)*T := calc
    _ ≤ ∑ _ ∈ I, T := sum_le_sum aw
    _ = (I.card : ℝ)*T := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (card_le_card Icap).trans_eq (by simp [Nat.card_Icc])) T0
  have jSub : J ⊆ Ioc (0 : ℤ) (S : ℤ) := fun j hj => (jProp j hj).1
  have jSize : (J.card : ℝ) ≤ S := by
    exact_mod_cast (card_le_card jSub).trans_eq (by rw [Int.card_Ioc,sub_zero,Int.toNat_natCast])
  have rMass : (∑ j ∈ J, ‖β j‖) ≤ (S : ℝ)*(T*L) := calc
    _ ≤ ∑ _ ∈ J, T*L := sum_le_sum bw
    _ = (J.card : ℝ)*(T*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right jSize (by positivity)
  have div_m : (m.divisors.card : ℝ) ≤ T := divisors m (le_max_left _ _)
  have divisorFactor : (m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1) ≤ T*L/N^(1/32 : ℝ) := by
    have d : N^(1/32 : ℝ) ≤ (D : ℝ)+1 := (Nat.lt_floor_add_one (N^(1/32 : ℝ))).le
    calc
      _ ≤ T*L/((D : ℝ)+1) := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) d
  have core : (A : ℝ)*(S : ℝ) ≤ 2*N^(513/512+3/512 : ℝ)/(M*G^2) := by
    apply (le_div_iff₀ (by positivity : 0 < M*G^2)).mpr
    calc
      _ = (A : ℝ)*((S : ℝ)*M*G^2) := by ring
      _ ≤ N^(x+3/512)*(2*N^(513/512-x)) := mul_le_mul aCap cofactorCap (by positivity) (by positivity)
      _ = _ := by
        have sum : N^(x+3/512)*N^(513/512-x) = N^(513/512+3/512 : ℝ) := by rw [← Real.rpow_add np]; congr 1; ring
        calc
          _ = 2*(N^(x+3/512)*N^(513/512-x)) := by ring
          _ = _ := by rw [sum]
  have gpow : G^(3/2 : ℝ) ≤ G^2 := by
    rw [← Real.rpow_natCast G 2]
    exact Real.rpow_le_rpow_of_exponent_le g1 (by norm_num)
  have tail : ((m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1))*
       ((∑ i ∈ I, ‖α i‖)*(∑ j ∈ J, ‖β j‖)) ≤ 2*H*T^3*L^3/(M*G^(3/2 : ℝ)) := by
    calc
      _ ≤ (T*L/N^(1/32 : ℝ))*(((A : ℝ)*T)*((S : ℝ)*(T*L))) := by gcongr
      _ = (T*L/N^(1/32 : ℝ))*(((A : ℝ)*(S : ℝ))*T^2*L) := by ring
      _ ≤ (T*L/N^(1/32 : ℝ))*((2*N^(513/512+3/512 : ℝ)/(M*G^2))*T^2*L) := by gcongr
      _ = 2*N^(500/512 : ℝ)*T^3*L^2/(M*G^2) := by
        have pow : N^(513/512+3/512 : ℝ)/N^(1/32 : ℝ)=N^(500/512 : ℝ) := by rw [← Real.rpow_sub np]; norm_num
        rw [← pow]
        ring
      _ ≤ _ := by
        have h : N^(500/512 : ℝ) ≤ H := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        have l : L^2 ≤ L^3 := pow_le_pow_right₀ L1 (by decide)
        gcongr
  exact est.trans ((add_le_add (mul_le_mul_of_nonneg_right logBound B0) tail).trans_eq (by unfold B H; ring))

end

end B13BoundedStepProductSavingProof

end

/- Moderate far endpoint bucket -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

theorem moderate_far_endpoint_bucket_budget {n m g : ℕ}
    (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ)) :
    let cap := ⌊(m : ℝ)*(g : ℝ)*(n : ℝ)^(3/1024 : ℝ)⌋₊
    let d := ⌊(m : ℝ)*(n : ℝ)^(-3/1024 : ℝ)⌋₊
    0 < d ∧ ((cap/d+1 : ℕ) : ℝ) ≤ 3*(g : ℝ)*(n : ℝ)^(6/1024 : ℝ) ∧
      (d : ℝ)/(m : ℝ) ≤ (n : ℝ)^(-3/1024 : ℝ) := by
  dsimp only
  let N := (n : ℝ)
  let P := (m : ℝ)
  let G := (g : ℝ)
  let cap := ⌊P*G*N^(3/1024 : ℝ)⌋₊
  let d := ⌊P*N^(-3/1024 : ℝ)⌋₊
  have np : 0 < N := zero_lt_one.trans_le n1
  have pp : 0 < P := (Real.rpow_pos_of_pos np _).trans_le mLo
  have gp : 0 < G := zero_lt_one.trans_le g1
  have v1 : 1 ≤ P*N^(-3/1024 : ℝ) := calc
    1 ≤ N^(1/3-3/1024 : ℝ) := Real.one_le_rpow n1 (by norm_num)
    _ = N^(1/3 : ℝ)*N^(-3/1024 : ℝ) := by rw [sub_eq_add_neg,Real.rpow_add np]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right mLo (by positivity)
  have d1 : 1 ≤ d := Nat.le_floor v1
  have dp : (0 : ℝ) < d := by exact_mod_cast d1
  have low : P*N^(-3/1024 : ℝ) ≤ 2*(d : ℝ) := by
    have dR : (1 : ℝ) ≤ d := by exact_mod_cast d1
    have fl := Nat.lt_floor_add_one (P*N^(-3/1024 : ℝ))
    change P*N^(-3/1024 : ℝ) < (d : ℝ)+1 at fl
    linarith only [dR,fl]
  have upper : (d : ℝ) ≤ P*N^(-3/1024 : ℝ) := Nat.floor_le (by positivity)
  have capUp : (cap : ℝ) ≤ P*G*N^(3/1024 : ℝ) := Nat.floor_le (by positivity)
  have divided : ((cap/d : ℕ) : ℝ) ≤ (cap : ℝ)/(d : ℝ) :=
    (le_div_iff₀ dp).mpr (by exact_mod_cast Nat.div_mul_le_self cap d)
  have est : (cap : ℝ) ≤ (2*G*N^(6/1024 : ℝ))*(d : ℝ) := calc
    _ ≤ P*G*N^(3/1024 : ℝ) := capUp
    _ = (G*N^(6/1024 : ℝ))*(P*N^(-3/1024 : ℝ)) := by
      have r : N^(6/1024 : ℝ)*N^(-3/1024 : ℝ) = N^(3/1024 : ℝ) := by rw [← Real.rpow_add np]; norm_num
      calc
        _ = P*G*(N^(6/1024 : ℝ)*N^(-3/1024 : ℝ)) := by rw [r]
        _ = _ := by ring
    _ ≤ (G*N^(6/1024 : ℝ))*(2*(d : ℝ)) := mul_le_mul_of_nonneg_left low (by positivity)
    _ = _ := by ring
  have q := divided.trans ((div_le_iff₀ dp).mpr est)
  have one : 1 ≤ G*N^(6/1024 : ℝ) := one_le_mul_of_one_le_of_one_le g1 (Real.one_le_rpow n1 (by norm_num))
  refine ⟨d1,?_,(div_le_iff₀ pp).mpr (by simpa only [mul_comm] using upper)⟩
  change ((cap/d+1 : ℕ) : ℝ) ≤ 3*G*N^(6/1024 : ℝ)
  push_cast
  linarith only [q,one]

end

end B13BoundedStepProductSavingProof

end

/- Sixth moment moderate far ratio hyperbola -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

set_option maxHeartbeats 1500000 in
theorem norm_sixth_moment_moderate_far_ratio_hyperbola_le {n m g A S num l r : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/128 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (large : (2 : ℝ) ≤ (n : ℝ)^(1/64 : ℝ))
    (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(535/1024 : ℝ))
    (mLo : (n : ℝ)^(255/512 : ℝ) ≤ (m : ℝ))
    (gCap : (g : ℝ) ≤ (n : ℝ)^(1/512 : ℝ))
    (xLo : 31/512 ≤ x) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+3/512))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512-x))
    (rCap : (r : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(513/512 : ℝ))
    (endCap : num/(l+1) ≤ ⌊(m : ℝ)*(g : ℝ)*(n : ℝ)^(3/1024 : ℝ)⌋₊)
    (small : 6*A^5 < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ)
    (aw : ∀ a ∈ I, ‖α a‖ ≤ T) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T*L)
    (divisors : ∀ z ≤ max m (A^3), (z.divisors.card : ℝ) ≤ T)
    (dR : ∀ z ≤ r, (z.divisors.card : ℝ) ≤ T) :
    let J := intIntervalModUnits m 0 S
    let lo (a : ℕ) : ℤ := (l/a : ℕ)
    let hi (a : ℕ) : ℤ := (r/a : ℕ)
    ‖gatedBilinearSum I J α β lo hi
        (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
          (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      592*(n : ℝ)^(1023/1024 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)) := by
  dsimp only
  let P := (m : ℝ)
  let N := (n : ℝ)
  let G := (g : ℝ)
  let C := G^(1/2 : ℝ)
  let H := N^(1023/1024 : ℝ)
  let J := intIntervalModUnits m 0 S
  let lo (a : ℕ) : ℤ := (l/a : ℕ)
  let hi (a : ℕ) : ℤ := (r/a : ℕ)
  let R := 98*N^(1016/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ))
  let d := ⌊P*N^(-3/1024 : ℝ)⌋₊
  let cap := ⌊P*G*N^(3/1024 : ℝ)⌋₊
  have m1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have pp : 0 < P := zero_lt_one.trans_le m1
  have np : 0 < N := zero_lt_one.trans_le n1
  have gp : 0 < G := zero_lt_one.trans_le g1
  have cp : 0 < C := by unfold C; positivity
  have t0 := zero_le_one.trans T1
  have l0 := zero_le_one.trans L1
  have log0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg m1
  have R0 : 0 ≤ R := by unfold R; positivity
  have bound : R ≤ 98*N^(1016/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ)) := le_rfl
  have mThird : N^(1/3 : ℝ) ≤ P :=
    (Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : (1/3 : ℝ) ≤ 255/512)).trans mLo
  obtain ⟨d0,dcount,dsmall⟩ := moderate_far_endpoint_bucket_budget n1 g1 mThird
  have rUp : (r : ℝ) ≤ 2*N^(513/512 : ℝ)/(P*G^2) := (le_div_iff₀ (by positivity)).mpr (by
    have h := rCap
    change (r : ℝ)*P*G^2 ≤ 2*N^(513/512 : ℝ) at h
    convert h using 1
    ring)
  have jPos (j : ℤ) (hj : j ∈ J) : 0 < j := by
    have data : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    exact (mem_Ioc.mp data.1).1
  let mass := ∑ j ∈ J, ‖β j‖*∑ a ∈ I, if lo a < j ∧ j ≤ hi a then ‖α a‖ else 0
  have mass0 : 0 ≤ mass := by
    unfold mass
    exact sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (sum_nonneg fun a _ => by split_ifs <;> positivity)
  have massCut : mass ≤ (2*N^(513/512 : ℝ)/(P*G^2))*T^3*L := by
    have b := gated_left_weight_mass_le α β lo hi t0 (mul_nonneg t0 l0)
      (fun u hu => dR u (mem_Icc.mp hu).2) (fun a ha => (mem_Icc.mp (Icap ha)).1)
      (fun j hj => (jPos j hj).le) (fun a ha j hj active => ?_) aw bw
    · refine b.trans ?_
      calc
        _ ≤ (2*N^(513/512 : ℝ)/(P*G^2))*T*T*(T*L) := by gcongr
        _ = _ := by ring
    · have ja : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (jPos j hj).le
      have jR : j.toNat ≤ r/a := by
        have h : (j.toNat : ℤ) ≤ ((r/a : ℕ) : ℤ) := by rw [ja]; exact active.2
        exact_mod_cast h
      have ap := (mem_Icc.mp (Icap ha)).1
      have jn : 0 < j.toNat := by have := jPos j hj; omega
      exact mem_Icc.mpr ⟨mul_pos ap jn,by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ap).mp jR⟩
  have est : ‖gatedBilinearSum I J α β lo hi
      (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
        (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
          ((cap/d+1 : ℕ) : ℝ)*(2*R)+(2*((d : ℝ)/P))*mass := by
    let phase (a : ℕ) (j : ℤ) := c*((a : ZMod m)*(j : ZMod m))⁻¹
    let e (a : ℕ) (j : ℤ) := (num : ℤ)/((a*j.toNat : ℕ) : ℤ)
    rw [gated_bilinear_sum_eq_pair_sum]
    refine norm_product_interval_le_of_ratio_window (num := num) (p := m) I J α β _ (fun a ha => (mem_Icc.mp (Icap ha)).1)
      jPos d0 endCap ?_
    intro u v b t vb bt bracket
    rw [← gated_bilinear_sum_eq_pair_sum]
    refine norm_gated_residue_variable_endpoint_le m I J α β u v vb bt phase e
      (fun a ha j hj gate => (bracket a ha j hj gate).2) ?_ ?_
    · refine (norm_gated_sixth_moment_moderate_far_fixed_endpoints_le charBound n1 large g1 T1 L1 mHi mLo xLo
        logBound aCap cofactorCap small I Icap copI α β u v vb aw bw divisors).trans ?_
      unfold R P G N
      gcongr <;> norm_num
    · refine (norm_gated_sixth_moment_moderate_far_fixed_endpoints_le charBound n1 large g1 T1 L1 mHi mLo xLo
        logBound aCap cofactorCap small I Icap copI _ _ u v bt ?_ ?_ divisors).trans ?_
      · intro a ha
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (α a))] using aw a ha
      · intro j hj
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (β j))] using bw j hj
      · unfold R P G N
        gcongr <;> norm_num
  have e1 : ((cap/d+1 : ℕ) : ℝ)*(2*R) ≤ 588*H*T^3*L^3/(P*G) := by
    have Ghalf : G^(3/2 : ℝ) = G*C := by
      unfold C
      rw [mul_comm G,← Real.rpow_add_one gp.ne']
      norm_num
    have CC : C^2 = G := by unfold C; rw [← Real.rpow_mul_natCast gp.le]; norm_num
    have cpow : C ≤ N^(1/1024 : ℝ) := by
      have b := Real.rpow_le_rpow gp.le gCap (by norm_num : (0 : ℝ) ≤ 1/2)
      rw [← Real.rpow_mul np.le] at b
      norm_num at b ⊢
      exact b
    calc
      _ ≤ (3*G*N^(6/1024 : ℝ))*(2*(98*N^(1016/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ)))) := by gcongr
      _ = 588*N^(511/512 : ℝ)*T^3*L^3*C/(P*G) := by
        have add : N^(6/1024 : ℝ)*N^(1016/1024 : ℝ) = N^(511/512 : ℝ) := by
          rw [← Real.rpow_add np]
          norm_num
        calc
          _ = 588*(N^(6/1024 : ℝ)*N^(1016/1024 : ℝ))*T^3*L^3*G/(P*G^(3/2 : ℝ)) := by ring
          _ = _ := by
            have frac : G/(P*(G*C)) = C/(P*G) := by
              rw [← CC]
              field_simp [pp.ne',cp.ne']
            rw [add,Ghalf]
            calc
              _ = (588*N^(511/512 : ℝ)*T^3*L^3)*(G/(P*(G*C))) := by ring
              _ = _ := by rw [frac]; ring
      _ ≤ 588*N^(511/512 : ℝ)*T^3*L^3*N^(1/1024 : ℝ)/(P*G) := by gcongr
      _ = _ := by
        have add : N^(511/512 : ℝ)*N^(1/1024 : ℝ) = H := by
          unfold H
          rw [← Real.rpow_add np]
          norm_num
        calc
          _ = 588*(N^(511/512 : ℝ)*N^(1/1024 : ℝ))*T^3*L^3/(P*G) := by ring
          _ = _ := by rw [add]
  have e2 : (2*((d : ℝ)/P))*mass ≤ 4*H*T^3*L^3/(P*G) := by
    have lg : L ≤ L^3 := by simpa only [pow_one] using pow_le_pow_right₀ L1 (show 1 ≤ 3 by decide)
    have pow : N^(-3/1024 : ℝ)*N^(513/512 : ℝ) = H := by unfold H; rw [← Real.rpow_add np]; norm_num
    calc
      _ ≤ (2*N^(-3/1024 : ℝ))*((2*N^(513/512 : ℝ)/(P*G^2))*T^3*L) := by gcongr
      _ = 4*H*T^3*L/(P*G^2) := by
        calc
          _ = 4*(N^(-3/1024 : ℝ)*N^(513/512 : ℝ))*T^3*L/(P*G^2) := by ring
          _ = _ := by rw [pow]
      _ ≤ 4*H*T^3*L^3/(P*G^2) := by gcongr
      _ ≤ _ := by
        have gPow : G ≤ G^2 := by simpa only [pow_one] using pow_le_pow_right₀ g1 (show 1 ≤ 2 by decide)
        gcongr
  exact est.trans ((add_le_add e1 e2).trans_eq (by ring))

end

end B13BoundedStepProductSavingProof

end

/- Wider low far window -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

set_option maxHeartbeats 2300000 in
def widerLowFarModulusCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(535/1024 : ℝ)⌋₊

set_option maxHeartbeats 2300000 in
theorem norm_wider_low_far_prefix_le {n m g e k l₀ r₀ num : ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (hsq : n ≤ m^2) (modLo : shortLowModulusCap n < m)
    (modCap : m ≤ widerLowFarModulusCap n)
    (charTop : m.gcd n ≤ targetDivisorCap n)
    (rUpper : r₀ ≤ extendedWideStepCap n) (rProd : r₀*m ≤ expandedHyperbolaProductCap n)
    (lFar : 2*n/m ≤ l₀)
    (gpos : 0 < g) (gn : g ∣ n) (gm : g ∣ m) (gSmall : g ≤ nearProductCommonDivisorCut n)
    (e0 : 0 < e) (eg : e ∣ g) (hk : k ∈ Icc 16 63)
    (ns : 1 < n) (huge : (6 : ℝ) < (n : ℝ)^(1/512 : ℝ)) (numN : num ≤ n/g)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖moderateLowDividedHyperbolaPrefix n m g e k l₀ r₀ num‖ ≤
      592*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3/(m : ℝ) := by
  let v := m/g
  let N := (n : ℝ)
  let M := (m : ℝ)
  let V := (v : ℝ)
  let G := (g : ℝ)
  let E := (e : ℝ)
  let y := (k : ℝ)/256
  let x := y-1/512
  let A := primeHyperbolaFactorFloor n (k+1)/e
  let aLo := primeHyperbolaFactorLo n k
  let S := moderateLowDividedHyperbolaCofactorCap n r₀ g e k
  let I := expandedHighDividedHyperbolaFactors n m g e k
  let J := intIntervalModUnits v 0 S
  let mLo := l₀
  let mHi := r₀
  let l := mLo/g
  let r := mHi/g
  let L := logBudget n
  let α (a : ℕ) : ℂ := leftBandMoebius n (e*a)
  let β (j : ℤ) : ℂ := leftBilinearFactor n ((g/e)*j.toNat)
  have v0 : 0 < v := Nat.div_pos (Nat.le_of_dvd m0 gm) gpos
  let _ : NeZero v := ⟨v0.ne'⟩
  have vprod : v*g=m := Nat.div_mul_cancel gm
  have npNat : 0 < n := zero_lt_one.trans ns
  have nr : 1 < N := show (1 : ℝ) < (n : ℝ) from by exact_mod_cast ns
  have np : 0 < N := zero_lt_one.trans nr
  have gp : 0 < G := show (0 : ℝ) < (g : ℝ) from by exact_mod_cast gpos
  have G1 : 1 ≤ G := show (1 : ℝ) ≤ (g : ℝ) from by exact_mod_cast gpos
  have vN : v ≤ n := (by simpa only [mul_one] using Nat.mul_le_mul_left v (show 1 ≤ g from gpos) : v ≤ v*g).trans
    (by rw [vprod]; exact mN)
  have vEq : V*G=M := by
    change (v : ℝ)*(g : ℝ) = (m : ℝ)
    exact_mod_cast vprod
  have origHi : M ≤ N^(535/1024 : ℝ) :=
    (show M ≤ (widerLowFarModulusCap n : ℝ) by
      change (m : ℝ) ≤ (widerLowFarModulusCap n : ℝ)
      exact_mod_cast modCap).trans
      (Nat.floor_le (by positivity))
  have castGcd : (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ N^(1/128 : ℝ) := by
    have vd : v ∣ m := ⟨g,vprod.symm⟩
    have nd : n/g ∣ n := ⟨g,(Nat.div_mul_cancel gn).symm⟩
    have d : v.gcd (n/g) ∣ m.gcd n := Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans vd) ((Nat.gcd_dvd_right _ _).trans nd)
    have relation := (gcd_val_nat_cast_le_gcd (m := v) (n/g)).trans
      ((Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ npNat) d).trans charTop)
    exact (show (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ (targetDivisorCap n : ℝ) by
      exact_mod_cast relation).trans (Nat.floor_le (by positivity))
  have vTop : V ≤ N^(535/1024 : ℝ) := by
    have h : V ≤ M := by
      rw [← vEq]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left G1 (by positivity : 0 ≤ V)
    exact h.trans origHi
  have gCap : G ≤ N^(1/512 : ℝ) :=
    (by exact_mod_cast gSmall : (g : ℝ) ≤ nearProductCommonDivisorCut n).trans (Nat.floor_le (by positivity))
  have eCap : E ≤ N^(1/512 : ℝ) :=
    (by exact_mod_cast Nat.le_of_dvd gpos eg : (e : ℝ) ≤ g).trans gCap
  have mLower : N^(1/2 : ℝ) ≤ M := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_left (by positivity)).mpr
    change (n : ℝ) ≤ (m : ℝ)^2
    exact_mod_cast hsq
  have vLower : N^(255/512 : ℝ) ≤ V := by
    apply (mul_le_mul_iff_left₀ gp).mp
    calc
      _ ≤ N^(255/512 : ℝ)*N^(1/512 : ℝ) :=
        mul_le_mul_of_nonneg_left gCap (by positivity)
      _ = N^(1/2 : ℝ) := by rw [← Real.rpow_add np]; norm_num
      _ ≤ M := mLower
      _ = _ := vEq.symm
  have mStrict : N^(133/256 : ℝ) < M :=
    (Nat.lt_floor_add_one _).trans_le
      (by change (shortLowModulusCap n : ℝ)+1 ≤ (m : ℝ); exact_mod_cast Nat.succ_le_of_lt modLo)
  have vStrict : N^(265/512 : ℝ) ≤ V := by
    apply (mul_le_mul_iff_left₀ gp).mp
    calc
      _ ≤ N^(265/512 : ℝ)*N^(1/512 : ℝ) := mul_le_mul_of_nonneg_left gCap (by positivity)
      _ = N^(133/256 : ℝ) := by rw [← Real.rpow_add np]; norm_num
      _ ≤ M := mStrict.le
      _ = _ := vEq.symm
  have vLo : N^(1/3 : ℝ) < V :=
    (Real.rpow_lt_rpow_of_exponent_lt nr (by norm_num : (1/3 : ℝ) < 255/512)).trans_le vLower
  have kmin : (16 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
  have kmax : (k : ℝ) ≤ 63 := by exact_mod_cast (mem_Icc.mp hk).2
  have xLo : 31/512 ≤ x := by unfold x y; linarith
  have xHi : x ≤ 1/4 := by unfold x y; linarith
  have aFormula : primeHyperbolaFactorFloor n (k+1) = ⌊N^(x+3/512)⌋₊ := by
    unfold primeHyperbolaFactorFloor N x y
    rw [Nat.cast_add,Nat.cast_one,add_div]
    congr 2
    ring
  have aCap : (A : ℝ) ≤ N^(x+3/512) :=
    (by exact_mod_cast Nat.div_le_self (primeHyperbolaFactorFloor n (k+1)) e :
      (A : ℝ) ≤ (primeHyperbolaFactorFloor n (k+1) : ℝ)).trans (by rw [aFormula]; exact Nat.floor_le (by positivity))
  have A1 : 0 < A := by
    change 1 ≤ primeHyperbolaFactorFloor n (k+1)/e
    apply (Nat.le_div_iff_mul_le e0).mpr
    rw [one_mul,aFormula]
    exact Nat.le_floor (eCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by linarith)))
  have aQ : (A : ℝ) ≤ N^(1/4 : ℝ) :=
    aCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by unfold x y; linarith))
  have Av : A < v := by
    have h := aQ.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt nr (by norm_num : (1/4 : ℝ) < 1/3)).trans vLo)
    change (A : ℝ) < (v : ℝ) at h
    exact_mod_cast h
  have Icap : I ⊆ Icc 1 A := by
    intro a ha
    have h := mem_Ioc.mp (mem_filter.mp ha).1
    exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt h.1,h.2.trans (Nat.div_le_div_right (min_le_right (lowCut n) _))⟩
  have copI (a : ℕ) (ha : a ∈ I) : a.Coprime v := (mem_filter.mp ha).2.2
  have rN : mHi ≤ n := rUpper.trans (extended_wide_step_le npNat)
  have rG : r*g ≤ mHi := Nat.div_mul_le_self mHi g
  have sR : S ≤ r := Nat.div_le_self _ _
  have rp : r*v*g^2 ≤ expandedHyperbolaProductCap n := calc
    _ = (r*g)*(v*g) := by ring
    _ = (r*g)*m := by rw [vprod]
    _ ≤ mHi*m := Nat.mul_le_mul_right m rG
    _ ≤ _ := rProd
  have rCap : (r : ℝ)*V*G^2 ≤ 2*N^(513/512 : ℝ) := by
    calc
      _ ≤ (expandedHyperbolaProductCap n : ℝ) := by
        change (r : ℝ)*(v : ℝ)*(g : ℝ)^2 ≤ (expandedHyperbolaProductCap n : ℝ)
        exact_mod_cast rp
      _ ≤ _ := by
        unfold expandedHyperbolaProductCap
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
  have cofactorFloor : N^x ≤ (aLo/e : ℕ)+1 := by
    have more : aLo < (aLo/e+1)*e := (Nat.div_lt_iff_lt_mul e0).mp (Nat.lt_succ_self _)
    have rank : (primeHyperbolaFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*E := by
      have le : primeHyperbolaFactorFloor n k+1 ≤ (aLo/e+1)*e :=
        Nat.succ_le_of_lt ((le_max_right _ _).trans_lt more)
      change (primeHyperbolaFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*(e : ℝ)
      exact_mod_cast le
    have ground : N^y ≤ (((aLo/e : ℕ) : ℝ)+1)*E := (Nat.lt_floor_add_one (N^y)).le.trans rank
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (1/512 : ℝ))).mp
    calc
      _ = N^y := by rw [← Real.rpow_add np]; unfold x; simp
      _ ≤ (((aLo/e : ℕ) : ℝ)+1)*E := ground
      _ ≤ _ := mul_le_mul_of_nonneg_left eCap (by positivity)
  have sCap : (S : ℝ)*V*G^2 ≤ 2*N^(513/512-x) := by
    have cut : S*(aLo/e+1) ≤ r := Nat.div_mul_le_self r (aLo/e+1)
    have scaled : (S : ℝ)*(((aLo/e : ℕ) : ℝ)+1) ≤ (r : ℝ) := by exact_mod_cast cut
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np x)).mp
    calc
      _ ≤ ((S : ℝ)*V*G^2)*(((aLo/e : ℕ) : ℝ)+1) :=
        mul_le_mul_of_nonneg_left cofactorFloor (by positivity)
      _ = ((S : ℝ)*(((aLo/e : ℕ) : ℝ)+1))*V*G^2 := by ring
      _ ≤ (r : ℝ)*V*G^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right scaled (by positivity)) (by positivity)
      _ ≤ 2*N^(513/512 : ℝ) := rCap
      _ = (2*N^(513/512-x))*N^x := by rw [mul_assoc,← Real.rpow_add np,sub_add_cancel]
  have endCap : num/(l+1) ≤ ⌊V*G*N^(3/1024 : ℝ)⌋₊ := by
    have lBound : 2*n/m < (l+1)*g :=
      lFar.trans_lt ((Nat.div_lt_iff_lt_mul gpos).mp (Nat.lt_succ_self (l₀/g)))
    have scaled := (Nat.div_lt_iff_lt_mul m0).mp lBound
    have product : n ≤ (m*(l+1))*g := by
      calc
        _ ≤ 2*n := by omega
        _ ≤ ((l+1)*g)*m := scaled.le
        _ = _ := by ring
    have nTop : n/g ≤ m*(l+1) := Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm g] using product)
    have stepTop : num/(l+1) ≤ m := Nat.div_le_of_le_mul (by
      simpa only [Nat.mul_comm m] using numN.trans nTop)
    refine stepTop.trans ?_
    apply Nat.le_floor
    calc
      (m : ℝ) = V*G := vEq.symm
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow nr.le (by norm_num))
  have wideEndCap : num/(l+1) ≤ ⌊V*G*N^(1/256 : ℝ)⌋₊ :=
    endCap.trans (Nat.floor_mono (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le nr.le (by norm_num)) (by positivity)))
  have divN (z : ℕ) (h : z ≤ n) : (z.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ ns.le (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors z (h.trans nn)
  have divV (z : ℕ) (h : z ≤ 4*v^3) : (z.divisors.card : ℝ) ≤ T :=
    divisors z (h.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left vN 3)))
  have divR (z : ℕ) (h : z ≤ r) : (z.divisors.card : ℝ) ≤ T :=
    divN z (h.trans ((Nat.div_le_self _ _).trans rN))
  have aw (a : ℕ) (ha : a ∈ I) : ‖α a‖ ≤ T := by
    have h := (mem_Ioc.mp (mem_filter.mp ha).1).2
    have eLe : e*a ≤ lowCut n := by
      have h' := (Nat.le_div_iff_mul_le e0).mp h
      exact (by simpa only [Nat.mul_comm] using h'.trans (min_le_left _ _) : e*a ≤ lowCut n)
    have lowN : lowCut n ≤ n := by
      have h : (lowCut n : ℝ) ≤ (n : ℝ) :=
        (Nat.floor_le (by positivity)).trans (Real.rpow_le_self_of_one_le nr.le (by norm_num))
      exact_mod_cast h
    exact (norm_leftBandMoebius_le n _).trans (divN _ (eLe.trans lowN))
  have bw (j : ℤ) (hj : j ∈ J) : ‖β j‖ ≤ T*L := by
    have data : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod v) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    have jR : j.toNat ≤ r := (show j.toNat ≤ S by have := (mem_Ioc.mp data.1).2; omega).trans sR
    have h : (g/e)*j.toNat ≤ n := calc
      _ ≤ g*r := Nat.mul_le_mul (Nat.div_le_self g e) jR
      _ ≤ mHi := by simpa only [Nat.mul_comm] using rG
      _ ≤ _ := rN
    exact norm_left_bilinear_factor_bound h divN
  have logBound : 1+Real.log V ≤ L := by
    have pv : 0 < V := show (0 : ℝ) < (v : ℝ) from by exact_mod_cast v0
    have up : V ≤ (n : ℝ)+2 := by
      change (v : ℝ) ≤ (n : ℝ)+2
      exact_mod_cast vN.trans (by omega : n≤n+2)
    unfold L logBudget
    linarith only [Real.log_le_log pv up]
  change ‖moderateLowDividedHyperbolaPrefix n m g e k l₀ r₀ num‖ ≤ 592*N^(1023/1024 : ℝ)*T^3*L^3/M
  by_cases smallBand : k ≤ 25
  · have smallK : (k : ℝ) ≤ 25 := by exact_mod_cast smallBand
    have aSmall : (A : ℝ) ≤ N^(26/256 : ℝ) :=
      aCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by unfold x y; linarith only [smallK]))
    have aPow : (A : ℝ)^5 ≤ N^(130/256 : ℝ) := by
      calc
        _ ≤ (N^(26/256 : ℝ))^5 := pow_le_pow_left₀ (by positivity) aSmall _
        _ = _ := by rw [← Real.rpow_mul_natCast np.le]; norm_num
    have large : (2 : ℝ) ≤ N^(1/64 : ℝ) :=
      (show (2 : ℝ) ≤ 6 by norm_num).trans
        (huge.le.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by norm_num)))
    have small : 6*A^5 < v := by
      have hs : (6 : ℝ)*(A : ℝ)^5 < V := calc
        _ ≤ 6*N^(130/256 : ℝ) := mul_le_mul_of_nonneg_left aPow (by norm_num)
        _ < N^(1/512 : ℝ)*N^(130/256 : ℝ) :=
          mul_lt_mul_of_pos_right huge (by positivity)
        _ ≤ N^(265/512 : ℝ) := by
          rw [← Real.rpow_add np]
          exact Real.rpow_le_rpow_of_exponent_le nr.le (by norm_num)
        _ ≤ _ := vStrict
      change (6 : ℝ)*(A : ℝ)^5 < (v : ℝ) at hs
      exact_mod_cast hs
    have dA (z : ℕ) (hz : z ≤ max v (A^3)) : (z.divisors.card : ℝ) ≤ T := by
      have v3 : v ≤ v^3 := by simpa only [pow_one] using pow_le_pow_right₀ v0 (show 1 ≤ 3 by decide)
      exact divV z (hz.trans ((max_le v3 (Nat.pow_le_pow_left Av.le 3)).trans (by omega)))
    have b := norm_sixth_moment_moderate_far_ratio_hyperbola_le (m := v) (c := ((n/g : ℕ) : ZMod v)) (g := g)
      castGcd nr.le large G1 T1 (one_le_logBudget n) vTop vLower gCap xLo logBound
      aCap sCap rCap endCap small I Icap copI α β aw bw dA divR
    exact b.trans_eq (by rw [vEq])
  · have kBig : (26 : ℝ) ≤ k := by exact_mod_cast (show 26 ≤ k by omega)
    have vHi : V ≤ N^(1/2+x/2-7/256) :=
      vTop.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by unfold x y; linarith only [kBig]))
    have vMid : V ≤ N^(5/8-x/3) :=
      vTop.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by linarith only [xHi]))
    have b := norm_expanded_modulus_ratio_hyperbola_le (m := v) (c := ((n/g : ℕ) : ZMod v)) (g := g)
      castGcd nr.le G1 T1 (one_le_logBudget n) vHi vMid vLo.le gCap xLo xHi logBound aCap sCap rCap wideEndCap
      A1 Av I Icap copI α β aw bw divV divR
    exact b.trans_eq (by rw [vEq])

set_option maxHeartbeats 2300000 in
theorem norm_wider_low_far_window_le {n m g e k l₀ r₀ : ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (hsq : n ≤ m^2) (modLo : shortLowModulusCap n < m)
    (modCap : m ≤ widerLowFarModulusCap n)
    (charTop : m.gcd n ≤ targetDivisorCap n)
    (rUpper : r₀ ≤ extendedWideStepCap n) (rProd : r₀*m ≤ expandedHyperbolaProductCap n)
    (lFar : 2*n/m ≤ l₀)
    (gpos : 0 < g) (gn : g ∣ n) (gm : g ∣ m) (gSmall : g ≤ nearProductCommonDivisorCut n)
    (e0 : 0 < e) (eg : e ∣ g) (hk : k ∈ Icc 16 63)
    (ns : 1 < n) (huge : (6 : ℝ) < (n : ℝ)^(1/512 : ℝ)) {T : ℝ} (T1 : 1 ≤ T)
    (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖moderateLowDividedHyperbolaWindow n m g e k l₀ r₀‖ ≤
      1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3/(m : ℝ) := by
  unfold moderateLowDividedHyperbolaWindow
  dsimp only
  refine (norm_sub_le _ _).trans ?_
  let v := m/g
  let hi := v*(n/m)
  have h₁ := norm_wider_low_far_prefix_le (num := n/g-v) m0 mN hsq modLo modCap
    charTop rUpper rProd lFar gpos gn gm gSmall e0 eg hk ns huge
    (Nat.sub_le (n/g) v) T1 divisors
  have h₂ := norm_wider_low_far_prefix_le (num := n/g-hi-1) m0 mN hsq modLo modCap
    charTop rUpper rProd lFar gpos gn gm gSmall e0 eg hk ns huge
    ((Nat.sub_le (n/g-hi) 1).trans (Nat.sub_le (n/g) hi)) T1 divisors
  exact (add_le_add h₁ h₂).trans_eq (by ring)

end

end B13BoundedStepProductSavingProof

end

/- Moderate low divided hyperbola row bound -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def moderateLowDividedHyperbolaRow (n m : ℕ) (lower upper : ℕ → ℕ) : ℂ :=
  ∑ g ∈ expandedHighDividedHyperbolaDivisors n m, ∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63,
    moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)

theorem norm_moderate_low_divided_hyperbola_row_le {n m : ℕ} {lower upper : ℕ → ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (hsq : n ≤ m^2) (modCap : m ≤ shortLowModulusCap n)
    (charTop : m.gcd n ≤ targetDivisorCap n)
    (rUpper : ∀ g, upper g ≤ extendedWideStepCap n)
    (rProd : ∀ g, upper g*m ≤ expandedHyperbolaProductCap n)
    (lLower : ∀ g, subcriticalMediumProductCap n/m ≤ lower g)
    (ns : 1 < n) (huge : (6 : ℝ) < (n : ℝ)^(1/512 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T)
    (divN : ∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) :
    ‖moderateLowDividedHyperbolaRow n m lower upper‖ ≤
      (48*(1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3)*T^2)*(1/(m : ℝ)) := by
  let B := 1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3
  let M := (m : ℝ)
  let V := 48*B/M
  let G := expandedHighDividedHyperbolaDivisors n m
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have V0 : 0 ≤ V := by unfold V M B; positivity
  have natCard : G.card ≤ n.divisors.card := card_le_card (filter_subset _ n.divisors)
  have nG : (G.card : ℝ) ≤ T := (show (G.card : ℝ) ≤ (n.divisors.card : ℝ) by exact_mod_cast natCard).trans (divN n le_rfl)
  have per (g : ℕ) (hg : g ∈ G) : ‖∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63,
      moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)‖ ≤ T*V := by
    obtain ⟨data,gS,_,gq⟩ := mem_filter.mp hg
    have gn := (Nat.mem_divisors.mp data).1
    have g0 := Nat.pos_of_dvd_of_pos gn (zero_lt_one.trans ns)
    have en : (g.divisors.card : ℝ) ≤ T := divN g (Nat.le_of_dvd (zero_lt_one.trans ns) gn)
    calc
      _ ≤ ∑ e ∈ g.divisors, ‖∑ k ∈ Icc 16 63, moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ g.divisors, V := by
        refine sum_le_sum fun e he => ?_
        have eg := (Nat.mem_divisors.mp he).1
        have e0 := Nat.pos_of_dvd_of_pos eg g0
        calc
          _ ≤ ∑ k ∈ Icc 16 63, ‖moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)‖ := norm_sum_le _ _
          _ ≤ ∑ _ ∈ Icc 16 63, B/M := sum_le_sum fun k hk =>
            norm_moderate_low_divided_hyperbola_window_le m0 mN hsq modCap charTop
              (rUpper g) (rProd g) (lLower g) g0 gn gq gS e0 eg hk ns huge T1 divisors
          _ = V := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,V]; norm_num; ring
      _ = (g.divisors.card : ℝ)*V := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right en V0
  change ‖∑ g ∈ G, ∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63, moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)‖ ≤
    (48*B*T^2)*(1/(m : ℝ))
  calc
    _ ≤ ∑ g ∈ G, ‖∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63, moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ ∈ G, T*V := sum_le_sum per
    _ = (G.card : ℝ)*(T*V) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ T*(T*V) := mul_le_mul_of_nonneg_right nG (by positivity)
    _ = _ := by unfold V M; ring

end

end B13BoundedStepProductSavingProof

end

/- Moderate low divided hyperbola row selection -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4PairIntegral
open scoped Classical Finset

noncomputable section

def moderateLowDividedHyperbolaRowItems (n m : ℕ) (lower upper : ℕ → ℕ) : Finset (ℕ × ℕ) :=
  (bilateralLeftWaveItems n).filter fun i =>
    let u := leftBilinearStep i
    let g := u.gcd m
    g ∈ expandedHighDividedHyperbolaDivisors n m ∧ lower g < u ∧ u ≤ upper g

theorem moderate_low_divided_hyperbola_row_eq_selected {n m : ℕ} {lower upper : ℕ → ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (lLeft : ∀ g, leftMediumCap n ≤ lower g) (rUpper : ∀ g, upper g ≤ extendedWideStepCap n) :
    moderateLowDividedHyperbolaRow n m lower upper =
      ∑ i ∈ moderateLowDividedHyperbolaRowItems n m lower upper,
        leftBilinearWeight n i *
          (pairResidueError n (leftBilinearStep i) m 0 (n/leftBilinearStep i) 0 (n/m) : ℂ) := by
  let I := moderateLowDividedHyperbolaRowItems n m lower upper
  let G := expandedHighDividedHyperbolaDivisors n m
  let K := Icc 16 63
  let d (i : ℕ × ℕ) := (leftBilinearStep i).gcd m
  let w (i : ℕ × ℕ) := leftBilinearWeight n i *
    (pairResidueError n (leftBilinearStep i) m 0
      (n/leftBilinearStep i) 0 (n/m) : ℂ)
  have n1 : 1 ≤ n := m0.trans_le mN
  have mapsG : ∀ i ∈ I, d i ∈ G := fun _ hi => (mem_filter.mp hi).2.1
  change moderateLowDividedHyperbolaRow n m lower upper = ∑ i ∈ I, w i
  rw [← sum_fiberwise_of_maps_to mapsG w]
  unfold moderateLowDividedHyperbolaRow
  refine sum_congr rfl fun g hg => ?_
  let I₁ := I.filter fun i => d i = g
  let aGcd (i : ℕ × ℕ) := i.1.gcd g
  have gData := mem_filter.mp hg
  have gn := (Nat.mem_divisors.mp gData.1).1
  have g0 := Nat.pos_of_dvd_of_pos gn n1
  have gq := gData.2.2.2
  have mapsE : ∀ i ∈ I₁, aGcd i ∈ g.divisors :=
    fun i _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right i.1 g,g0.ne'⟩
  change (∑ e ∈ g.divisors, ∑ k ∈ K, moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)) = ∑ i ∈ I₁, w i
  rw [← sum_fiberwise_of_maps_to mapsE w]
  refine sum_congr rfl fun e he => ?_
  let I₂ := I₁.filter fun i => aGcd i=e
  have eg := (Nat.mem_divisors.mp he).1
  have e0 := Nat.pos_of_dvd_of_pos eg g0
  have eqFilter (k : ℕ) : moderateLowDividedHyperbolaLeftItems n m g e k (lower g) (upper g) =
      I₂.filter fun i => i.1 ∈ primeHyperbolaFactorBlock n k := by
    ext i
    constructor
    · intro hi
      obtain ⟨left,fac,gg,ee,lo,up⟩ := mem_filter.mp hi
      have dG : d i ∈ G := by
        change (leftBilinearStep i).gcd m ∈ expandedHighDividedHyperbolaDivisors n m
        rw [gg]
        exact hg
      have rel : (leftBilinearStep i).gcd m=g := gg
      have base : i ∈ I := mem_filter.mpr ⟨left,dG,by rw [rel]; exact lo,by rw [rel]; exact up⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨base,gg⟩,ee⟩,fac⟩
    · intro hi
      obtain ⟨hi₂,fac⟩ := mem_filter.mp hi
      obtain ⟨hi₁,ee⟩ := mem_filter.mp hi₂
      obtain ⟨hi₀,gg⟩ := mem_filter.mp hi₁
      obtain ⟨left,_,lo,up⟩ := mem_filter.mp hi₀
      have rel : (leftBilinearStep i).gcd m=g := gg
      exact mem_filter.mpr ⟨left,fac,gg,ee,by rwa [rel] at lo,by rwa [rel] at up⟩
  calc
    (∑ k ∈ K, moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)) =
        ∑ k ∈ K, ∑ i ∈ I₂.filter (fun i => i.1 ∈ primeHyperbolaFactorBlock n k), w i := by
      refine sum_congr rfl fun k _ => ?_
      rw [← eqFilter k]
      exact moderate_low_divided_hyperbola_window_eq_selected m0 mN (lLeft g) (rUpper g) g0 gn gq e0 eg
    _ = ∑ i ∈ I₂, ∑ k ∈ K, if i.1 ∈ primeHyperbolaFactorBlock n k then w i else 0 := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = ∑ i ∈ I₂, w i := by
      refine sum_congr rfl fun i hi => ?_
      have left : i ∈ bilateralLeftWaveItems n :=
        (mem_filter.mp (mem_filter.mp (mem_filter.mp hi).1).1).1
      have aRange := (mem_product.mp (mem_filter.mp (mem_filter.mp left).1).1).1
      obtain ⟨k,⟨kMem,hk⟩,unique⟩ := prime_hyperbola_factor_blocks_cover n1 aRange
      rw [sum_eq_single_of_mem k kMem]
      · exact ite_eq_left hk
      · intro k' hk' neq
        exact ite_eq_right (fun h => neq (unique k' ⟨hk',h⟩))

end

end B13BoundedStepProductSavingProof

end

/- Moderate low divided hyperbola saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

abbrev ModerateLowBounds := ℕ → RightLowWaveIndex → ℕ → ℕ

def moderateLowDividedHyperbolaResidueSlice (R : ℕ → Finset RightLowWaveIndex)
    (lower upper : ModerateLowBounds) (n : ℕ) : ℂ :=
  ∑ j ∈ R n, rightLowWaveWeight j *
    moderateLowDividedHyperbolaRow n (rightLowWaveStep j) (lower n j) (upper n j)

private theorem norm_moderate_low_divided_hyperbola_slice_le {n : ℕ}
    (R : ℕ → Finset RightLowWaveIndex) (lower upper : ModerateLowBounds)
    (support : ∀ j ∈ R n, j ∈ rightLowWaveItems n ∧ n ≤ (rightLowWaveStep j)^2 ∧
      rightLowWaveStep j ≤ shortLowModulusCap n ∧ (rightLowWaveStep j).gcd n ≤ targetDivisorCap n)
    (lLower : ∀ j ∈ R n, ∀ g, subcriticalMediumProductCap n/rightLowWaveStep j ≤ lower n j g)
    (rUpper : ∀ j ∈ R n, ∀ g, upper n j g ≤ extendedWideStepCap n)
    (rProd : ∀ j ∈ R n, ∀ g, (upper n j g)*(rightLowWaveStep j) ≤ expandedHyperbolaProductCap n)
    (nBig : 2 ≤ n) (huge : (6 : ℝ) < (n : ℝ)^(1/512 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖moderateLowDividedHyperbolaResidueSlice R lower upper n‖ ≤
      56832*(n : ℝ)^(1023/1024 : ℝ)*T^8*logBudget n^5 := by
  let L := logBudget n
  let C := n
  let B := 1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*L^3
  let W := T^3*L
  let J := R n
  have subset : J ⊆ rightLowWaveItems n := fun j hj => (support j hj).1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have B0 : 0 ≤ B := by unfold B; positivity
  have W0 : 0 ≤ W := by unfold W; positivity
  have n1 : 1 ≤ n := (show 1 ≤ (2 : ℕ) by decide).trans nBig
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have nPos : (0 : ℝ) < n := zero_lt_one.trans_le nR
  have C1 : 1 ≤ C := n1
  have Cn : (C : ℝ) ≤ (n : ℝ) := le_rfl
  have Cnat : C ≤ n := by exact_mod_cast Cn
  have divN (u : ℕ) (h : u ≤ n) : (u.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors u (h.trans nn)
  have ns : 1 < n := nBig
  have massH : (∑ m ∈ Icc 1 C, 1/(m : ℝ)) ≤ L := calc
    _ = (harmonic C : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    _ ≤ 1+Real.log C := by exact_mod_cast harmonic_le_one_add_log C
    _ ≤ L := by
      unfold L logBudget
      exact add_le_add_right (Real.log_le_log (by exact_mod_cast C1)
        (Cn.trans (by linarith : (n : ℝ) ≤ (n : ℝ)+2))) _
  have step (j : RightLowWaveIndex) (hj : j ∈ J) : rightLowWaveStep j ∈ Icc 1 C :=
    bilateral_right_low_step_range (subset hj)
  have weighted : (∑ j ∈ J, ‖rightLowWaveWeight j‖*(1/(rightLowWaveStep j : ℝ))) ≤ W*L := by
    refine (sum_norm_mul_le_of_step_mass J rightLowWaveStep rightLowWaveWeight (fun m => 1/(m : ℝ))
      step (fun _ _ => by positivity) ?_).trans (mul_le_mul_of_nonneg_left massH W0)
    intro m hm
    have h : m ∈ Icc 1 n := mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans Cnat⟩
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ subset)
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_right_low_step_mass T1 divN m h)
  have each (j : RightLowWaveIndex) (hj : j ∈ J) :
      ‖moderateLowDividedHyperbolaRow n (rightLowWaveStep j) (lower n j) (upper n j)‖ ≤ (48*B*T^2)*(1/(rightLowWaveStep j : ℝ)) := by
    obtain ⟨base,sq,cap,char⟩ := support j hj
    have data := mem_Icc.mp (bilateral_right_low_step_range base)
    exact norm_moderate_low_divided_hyperbola_row_le data.1 data.2 sq cap char (rUpper j hj)
      (rProd j hj) (lLower j hj) ns huge T1 divisors divN
  unfold moderateLowDividedHyperbolaResidueSlice
  change ‖∑ j ∈ J, rightLowWaveWeight j*moderateLowDividedHyperbolaRow n (rightLowWaveStep j) (lower n j) (upper n j)‖ ≤ _
  calc
    _ ≤ ∑ j ∈ J, ‖rightLowWaveWeight j*moderateLowDividedHyperbolaRow n (rightLowWaveStep j) (lower n j) (upper n j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ‖rightLowWaveWeight j‖*((48*B*T^2)*(1/(rightLowWaveStep j : ℝ))) := by
      refine sum_le_sum fun j hj => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (each j hj) (norm_nonneg _)
    _ = (48*B*T^2)*(∑ j ∈ J, ‖rightLowWaveWeight j‖*(1/(rightLowWaveStep j : ℝ))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (48*B*T^2)*(W*L) := mul_le_mul_of_nonneg_left weighted (by positivity)
    _ = _ := by unfold B W L; ring

theorem moderate_low_divided_hyperbola_residue_saving
    (R : ℕ → Finset RightLowWaveIndex) (lower upper : ModerateLowBounds)
    (support : ∀ n, ∀ j ∈ R n, j ∈ rightLowWaveItems n ∧ n ≤ (rightLowWaveStep j)^2 ∧
      rightLowWaveStep j ≤ shortLowModulusCap n ∧ (rightLowWaveStep j).gcd n ≤ targetDivisorCap n)
    (lLower : ∀ n, ∀ j ∈ R n, ∀ g, subcriticalMediumProductCap n/rightLowWaveStep j ≤ lower n j g)
    (rUpper : ∀ n, ∀ j ∈ R n, ∀ g, upper n j g ≤ extendedWideStepCap n)
    (rProd : ∀ n, ∀ j ∈ R n, ∀ g, (upper n j g)*(rightLowWaveStep j) ≤ expandedHyperbolaProductCap n) :
    saving (moderateLowDividedHyperbolaResidueSlice R lower upper) := by
  intro ε he
  obtain ⟨D,D1,db⟩ := divisor_envelope_at_power 65536 (by decide)
  let C := 56832*(4*D)^8
  have hlimit : Tendsto (fun n : ℕ => (n : ℝ)^(-(35/65536) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 35/65536)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(35/65536) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlimit
  have large : ∀ᶠ n : ℕ in atTop, (6 : ℝ) < (n : ℝ)^(1/512 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/512)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop 6
  have bound : ∀ᶠ n : ℕ in atTop, ‖moderateLowDividedHyperbolaResidueSlice R lower upper n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_log_budget_le_power (1/65536) (by norm_num),
      hl.eventually_lt_const he,large] with n nBig logb final huge
    have hn : 1 ≤ n := (show 1 ≤ (2 : ℕ) by decide).trans nBig
    have nr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have np : (0 : ℝ) < n := zero_lt_one.trans_le nr
    have D0 := zero_le_one.trans D1
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/65536 : ℝ)
    let T := (4*D)*X^3
    have X1 : 1 ≤ X := Real.one_le_rpow nr (by norm_num)
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) D1) (one_le_pow₀ X1)
    have cp : (4 : ℝ)^(1/65536 : ℝ) ≤ 4 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have divs (m : ℕ) (hm : m ≤ 4*n^3) : (m.divisors.card : ℝ) ≤ T := by
      calc
        _ ≤ D*((4*n^3 : ℕ) : ℝ)^(1/(65536 : ℕ) : ℝ) := db (4*n^3) m hm
        _ = D*((4 : ℝ)^(1/65536 : ℝ)*X^3) := by
          push_cast
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul np.le]
          unfold X
          rw [← Real.rpow_mul_natCast np.le]
          norm_num
        _ ≤ D*(4*X^3) := by gcongr
        _ = _ := by unfold T; ring
    have ex : (n : ℝ)^(1023/1024 : ℝ)*X^29 = (n : ℝ)^(-(35/65536) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast np.le, ← Real.rpow_add np, ← Real.rpow_add_one np.ne']
      congr 1
      norm_num
    calc
      _ ≤ 56832*(n : ℝ)^(1023/1024 : ℝ)*T^8*logBudget n^5 := norm_moderate_low_divided_hyperbola_slice_le R lower upper (support n) (lLower n) (rUpper n) (rProd n) nBig huge T1 divs
      _ ≤ 56832*(n : ℝ)^(1023/1024 : ℝ)*T^8*X^5 := by gcongr
      _ = C*((n : ℝ)^(1023/1024 : ℝ)*X^29) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(35/65536) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right final.le np.le
  obtain ⟨N,h⟩ := eventually_atTop.mp bound
  exact ⟨N,fun n hn _ => h n hn⟩

end

end B13BoundedStepProductSavingProof

end

/- Moderate low slices -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical

noncomputable section

def moderateLowActualSlice (R : ℕ → Finset RightLowWaveIndex)
    (lower upper : ModerateLowBounds) (n : ℕ) : ℂ :=
  ∑ j ∈ R n, rightLowWaveWeight j *
    ∑ i ∈ moderateLowDividedHyperbolaRowItems n (rightLowWaveStep j) (lower n j) (upper n j),
      leftBilinearWeight n i *
        (pairResidueError n (leftBilinearStep i) (rightLowWaveStep j) 0 (n/leftBilinearStep i)
          0 (rightLowWaveUpper n j) : ℂ)

theorem moderate_low_actual_slice_eq (R : ℕ → Finset RightLowWaveIndex)
    (lower upper : ModerateLowBounds) {n : ℕ}
    (support : ∀ j ∈ R n, j ∈ rightLowWaveItems n ∧ n ≤ (rightLowWaveStep j)^2)
    (lLeft : ∀ j ∈ R n, ∀ g, leftMediumCap n ≤ lower n j g)
    (rUpper : ∀ j ∈ R n, ∀ g, upper n j g ≤ extendedWideStepCap n) :
    moderateLowDividedHyperbolaResidueSlice R lower upper n = moderateLowActualSlice R lower upper n := by
  unfold moderateLowDividedHyperbolaResidueSlice moderateLowActualSlice
  refine sum_congr rfl fun j hj => ?_
  have h := support j hj
  have range := mem_Icc.mp (bilateral_right_low_step_range h.1)
  rw [moderate_low_divided_hyperbola_row_eq_selected range.1 range.2 (lLeft j hj) (rUpper j hj),
    right_low_full_upper_of_root_le h.1 h.2]

theorem moderate_low_actual_slice_saving (R : ℕ → Finset RightLowWaveIndex)
    (lower upper : ModerateLowBounds)
    (support : ∀ n, ∀ j ∈ R n, j ∈ rightLowWaveItems n ∧ n ≤ (rightLowWaveStep j)^2 ∧
      rightLowWaveStep j ≤ shortLowModulusCap n ∧ (rightLowWaveStep j).gcd n ≤ targetDivisorCap n)
    (lLeft : ∀ n, ∀ j ∈ R n, ∀ g, leftMediumCap n ≤ lower n j g)
    (lLower : ∀ n, ∀ j ∈ R n, ∀ g, subcriticalMediumProductCap n/rightLowWaveStep j ≤ lower n j g)
    (rUpper : ∀ n, ∀ j ∈ R n, ∀ g, upper n j g ≤ extendedWideStepCap n)
    (rProd : ∀ n, ∀ j ∈ R n, ∀ g, (upper n j g)*(rightLowWaveStep j) ≤ expandedHyperbolaProductCap n) :
    saving (moderateLowActualSlice R lower upper) := by
  intro ε he
  obtain ⟨N,h⟩ := moderate_low_divided_hyperbola_residue_saving R lower upper support lLower rUpper rProd ε he
  refine ⟨N,fun n hn even => ?_⟩
  rw [← moderate_low_actual_slice_eq R lower upper (n := n)
    (fun j hj => ⟨(support n j hj).1,(support n j hj).2.1⟩) (lLeft n) (rUpper n)]
  exact h n hn even

end

end B13BoundedStepProductSavingProof

end

/- Wider low far saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

theorem norm_wider_low_far_row_le {n m : ℕ} {lower upper : ℕ → ℕ}
    (m0 : 0 < m) (mN : m ≤ n) (hsq : n ≤ m^2) (modLo : shortLowModulusCap n < m)
    (modCap : m ≤ widerLowFarModulusCap n)
    (charTop : m.gcd n ≤ targetDivisorCap n)
    (rUpper : ∀ g, upper g ≤ extendedWideStepCap n)
    (rProd : ∀ g, upper g*m ≤ expandedHyperbolaProductCap n)
    (lLower : ∀ g, 2*n/m ≤ lower g)
    (ns : 1 < n) (huge : (6 : ℝ) < (n : ℝ)^(1/512 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T)
    (divN : ∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) :
    ‖moderateLowDividedHyperbolaRow n m lower upper‖ ≤
      (48*(1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3)*T^2)*(1/(m : ℝ)) := by
  let B := 1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*logBudget n^3
  let M := (m : ℝ)
  let V := 48*B/M
  let G := expandedHighDividedHyperbolaDivisors n m
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have V0 : 0 ≤ V := by unfold V M B; positivity
  have natCard : G.card ≤ n.divisors.card := card_le_card (filter_subset _ n.divisors)
  have nG : (G.card : ℝ) ≤ T := (show (G.card : ℝ) ≤ (n.divisors.card : ℝ) by exact_mod_cast natCard).trans (divN n le_rfl)
  have per (g : ℕ) (hg : g ∈ G) : ‖∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63,
      moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)‖ ≤ T*V := by
    obtain ⟨data,gS,_,gq⟩ := mem_filter.mp hg
    have gn := (Nat.mem_divisors.mp data).1
    have g0 := Nat.pos_of_dvd_of_pos gn (zero_lt_one.trans ns)
    have en : (g.divisors.card : ℝ) ≤ T := divN g (Nat.le_of_dvd (zero_lt_one.trans ns) gn)
    calc
      _ ≤ ∑ e ∈ g.divisors, ‖∑ k ∈ Icc 16 63, moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ g.divisors, V := by
        refine sum_le_sum fun e he => ?_
        have eg := (Nat.mem_divisors.mp he).1
        have e0 := Nat.pos_of_dvd_of_pos eg g0
        calc
          _ ≤ ∑ k ∈ Icc 16 63, ‖moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)‖ := norm_sum_le _ _
          _ ≤ ∑ _ ∈ Icc 16 63, B/M := sum_le_sum fun k hk =>
            norm_wider_low_far_window_le m0 mN hsq modLo modCap charTop
              (rUpper g) (rProd g) (lLower g) g0 gn gq gS e0 eg hk ns huge T1 divisors
          _ = V := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,V]; norm_num; ring
      _ = (g.divisors.card : ℝ)*V := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right en V0
  change ‖∑ g ∈ G, ∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63, moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)‖ ≤
    (48*B*T^2)*(1/(m : ℝ))
  calc
    _ ≤ ∑ g ∈ G, ‖∑ e ∈ g.divisors, ∑ k ∈ Icc 16 63, moderateLowDividedHyperbolaWindow n m g e k (lower g) (upper g)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ ∈ G, T*V := sum_le_sum per
    _ = (G.card : ℝ)*(T*V) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ T*(T*V) := mul_le_mul_of_nonneg_right nG (by positivity)
    _ = _ := by unfold V M; ring

private theorem norm_wider_low_far_slice_le {n : ℕ}
    (R : ℕ → Finset RightLowWaveIndex) (lower upper : ModerateLowBounds)
    (support : ∀ j ∈ R n, j ∈ rightLowWaveItems n ∧ n ≤ (rightLowWaveStep j)^2 ∧
      shortLowModulusCap n < rightLowWaveStep j ∧ rightLowWaveStep j ≤ widerLowFarModulusCap n ∧
      (rightLowWaveStep j).gcd n ≤ targetDivisorCap n)
    (lLower : ∀ j ∈ R n, ∀ g, 2*n/rightLowWaveStep j ≤ lower n j g)
    (rUpper : ∀ j ∈ R n, ∀ g, upper n j g ≤ extendedWideStepCap n)
    (rProd : ∀ j ∈ R n, ∀ g, (upper n j g)*(rightLowWaveStep j) ≤ expandedHyperbolaProductCap n)
    (nBig : 2 ≤ n) (huge : (6 : ℝ) < (n : ℝ)^(1/512 : ℝ))
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖moderateLowDividedHyperbolaResidueSlice R lower upper n‖ ≤
      56832*(n : ℝ)^(1023/1024 : ℝ)*T^8*logBudget n^5 := by
  let L := logBudget n
  let C := n
  let B := 1184*(n : ℝ)^(1023/1024 : ℝ)*T^3*L^3
  let W := T^3*L
  let J := R n
  have subset : J ⊆ rightLowWaveItems n := fun j hj => (support j hj).1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have B0 : 0 ≤ B := by unfold B; positivity
  have W0 : 0 ≤ W := by unfold W; positivity
  have n1 : 1 ≤ n := (show 1 ≤ (2 : ℕ) by decide).trans nBig
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have nPos : (0 : ℝ) < n := zero_lt_one.trans_le nR
  have C1 : 1 ≤ C := n1
  have Cn : (C : ℝ) ≤ (n : ℝ) := le_rfl
  have Cnat : C ≤ n := by exact_mod_cast Cn
  have divN (u : ℕ) (h : u ≤ n) : (u.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors u (h.trans nn)
  have ns : 1 < n := nBig
  have massH : (∑ m ∈ Icc 1 C, 1/(m : ℝ)) ≤ L := calc
    _ = (harmonic C : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    _ ≤ 1+Real.log C := by exact_mod_cast harmonic_le_one_add_log C
    _ ≤ L := by
      unfold L logBudget
      exact add_le_add_right (Real.log_le_log (by exact_mod_cast C1)
        (Cn.trans (by linarith : (n : ℝ) ≤ (n : ℝ)+2))) _
  have step (j : RightLowWaveIndex) (hj : j ∈ J) : rightLowWaveStep j ∈ Icc 1 C :=
    bilateral_right_low_step_range (subset hj)
  have weighted : (∑ j ∈ J, ‖rightLowWaveWeight j‖*(1/(rightLowWaveStep j : ℝ))) ≤ W*L := by
    refine (sum_norm_mul_le_of_step_mass J rightLowWaveStep rightLowWaveWeight (fun m => 1/(m : ℝ))
      step (fun _ _ => by positivity) ?_).trans (mul_le_mul_of_nonneg_left massH W0)
    intro m hm
    have h : m ∈ Icc 1 n := mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans Cnat⟩
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ subset)
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_right_low_step_mass T1 divN m h)
  have each (j : RightLowWaveIndex) (hj : j ∈ J) :
      ‖moderateLowDividedHyperbolaRow n (rightLowWaveStep j) (lower n j) (upper n j)‖ ≤ (48*B*T^2)*(1/(rightLowWaveStep j : ℝ)) := by
    obtain ⟨base,sq,lo,cap,char⟩ := support j hj
    have data := mem_Icc.mp (bilateral_right_low_step_range base)
    exact norm_wider_low_far_row_le data.1 data.2 sq lo cap char (rUpper j hj)
      (rProd j hj) (lLower j hj) ns huge T1 divisors divN
  unfold moderateLowDividedHyperbolaResidueSlice
  change ‖∑ j ∈ J, rightLowWaveWeight j*moderateLowDividedHyperbolaRow n (rightLowWaveStep j) (lower n j) (upper n j)‖ ≤ _
  calc
    _ ≤ ∑ j ∈ J, ‖rightLowWaveWeight j*moderateLowDividedHyperbolaRow n (rightLowWaveStep j) (lower n j) (upper n j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ‖rightLowWaveWeight j‖*((48*B*T^2)*(1/(rightLowWaveStep j : ℝ))) := by
      refine sum_le_sum fun j hj => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (each j hj) (norm_nonneg _)
    _ = (48*B*T^2)*(∑ j ∈ J, ‖rightLowWaveWeight j‖*(1/(rightLowWaveStep j : ℝ))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (48*B*T^2)*(W*L) := mul_le_mul_of_nonneg_left weighted (by positivity)
    _ = _ := by unfold B W L; ring

theorem wider_low_far_residue_saving
    (R : ℕ → Finset RightLowWaveIndex) (lower upper : ModerateLowBounds)
    (support : ∀ n, ∀ j ∈ R n, j ∈ rightLowWaveItems n ∧ n ≤ (rightLowWaveStep j)^2 ∧
      shortLowModulusCap n < rightLowWaveStep j ∧ rightLowWaveStep j ≤ widerLowFarModulusCap n ∧
      (rightLowWaveStep j).gcd n ≤ targetDivisorCap n)
    (lLower : ∀ n, ∀ j ∈ R n, ∀ g, 2*n/rightLowWaveStep j ≤ lower n j g)
    (rUpper : ∀ n, ∀ j ∈ R n, ∀ g, upper n j g ≤ extendedWideStepCap n)
    (rProd : ∀ n, ∀ j ∈ R n, ∀ g, (upper n j g)*(rightLowWaveStep j) ≤ expandedHyperbolaProductCap n) :
    saving (moderateLowDividedHyperbolaResidueSlice R lower upper) := by
  intro ε he
  obtain ⟨D,D1,db⟩ := divisor_envelope_at_power 65536 (by decide)
  let C := 56832*(4*D)^8
  have hlimit : Tendsto (fun n : ℕ => (n : ℝ)^(-(35/65536) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 35/65536)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(35/65536) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlimit
  have large : ∀ᶠ n : ℕ in atTop, (6 : ℝ) < (n : ℝ)^(1/512 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/512)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop 6
  have bound : ∀ᶠ n : ℕ in atTop, ‖moderateLowDividedHyperbolaResidueSlice R lower upper n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_log_budget_le_power (1/65536) (by norm_num),
      hl.eventually_lt_const he,large] with n nBig logb final huge
    have hn : 1 ≤ n := (show 1 ≤ (2 : ℕ) by decide).trans nBig
    have nr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have np : (0 : ℝ) < n := zero_lt_one.trans_le nr
    have D0 := zero_le_one.trans D1
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/65536 : ℝ)
    let T := (4*D)*X^3
    have X1 : 1 ≤ X := Real.one_le_rpow nr (by norm_num)
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) D1) (one_le_pow₀ X1)
    have cp : (4 : ℝ)^(1/65536 : ℝ) ≤ 4 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have divs (m : ℕ) (hm : m ≤ 4*n^3) : (m.divisors.card : ℝ) ≤ T := by
      calc
        _ ≤ D*((4*n^3 : ℕ) : ℝ)^(1/(65536 : ℕ) : ℝ) := db (4*n^3) m hm
        _ = D*((4 : ℝ)^(1/65536 : ℝ)*X^3) := by
          push_cast
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul np.le]
          unfold X
          rw [← Real.rpow_mul_natCast np.le]
          norm_num
        _ ≤ D*(4*X^3) := by gcongr
        _ = _ := by unfold T; ring
    have ex : (n : ℝ)^(1023/1024 : ℝ)*X^29 = (n : ℝ)^(-(35/65536) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast np.le, ← Real.rpow_add np, ← Real.rpow_add_one np.ne']
      congr 1
      norm_num
    calc
      _ ≤ 56832*(n : ℝ)^(1023/1024 : ℝ)*T^8*logBudget n^5 := norm_wider_low_far_slice_le R lower upper (support n) (lLower n) (rUpper n) (rProd n) nBig huge T1 divs
      _ ≤ 56832*(n : ℝ)^(1023/1024 : ℝ)*T^8*X^5 := by gcongr
      _ = C*((n : ℝ)^(1023/1024 : ℝ)*X^29) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(35/65536) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right final.le np.le
  obtain ⟨N,h⟩ := eventually_atTop.mp bound
  exact ⟨N,fun n hn _ => h n hn⟩

end

end B13BoundedStepProductSavingProof

end

/- Outer far cofactor size -/
section

namespace B13BoundedStepProductSavingProof

noncomputable section

theorem scaled_long_cofactor_size_for_outer_far_wider_factor {n p q A S d : ℕ} {x T : ℝ}
    (n1 : 1 ≤ (n : ℝ)) (p0 : (0 : ℝ) < p) (m1 : 1 ≤ ((p*q : ℕ) : ℝ)) (d1 : 1 ≤ (d : ℝ)) (T1 : 1 ≤ T)
    (mHi : ((p*q : ℕ) : ℝ) ≤ (n : ℝ)^(1/2 : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ ((p*q : ℕ) : ℝ))
    (qCap : (q : ℝ) ≤ (n : ℝ)^(5/2048 : ℝ))
    (xLo : 27/4096 ≤ x) (xHi : x ≤ 1/3)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+9/32768))
    (cofactorCap : (S : ℝ)*((p*q : ℕ) : ℝ)*(d : ℝ)^2 ≤ 2*(n : ℝ)^(4097/4096-x)) :
    longCofactorSize (p*q) p A S T ≤
      24*T*(n : ℝ)^(1023/1024 : ℝ)/(((p*q : ℕ) : ℝ)*(d : ℝ)^(3/2 : ℝ)) := by
  let N := (n : ℝ)
  let P := ((p*q : ℕ) : ℝ)
  let Q := (q : ℝ)
  let B := (A : ℝ)
  let K := (S : ℝ)
  let D := (d : ℝ)
  let Y := K*P*D^2
  let X := Y^(3/4 : ℝ)
  let H := N^(1023/1024 : ℝ)
  have np : 0 < N := zero_lt_one.trans_le n1
  have pp : 0 < P := zero_lt_one.trans_le m1
  have dp : 0 < D := zero_lt_one.trans_le d1
  have B0 : 0 ≤ B := by positivity
  have Y0 : 0 ≤ Y := by unfold Y; positivity
  have T0 := zero_le_one.trans T1
  have Ahalf : B^(1/2 : ℝ) ≤ N^((x+9/32768)*(1/2)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow B0 aCap (by norm_num)
  have Aextra : B^(7/8 : ℝ) ≤ N^((x+9/32768)*(7/8)) := by
    rw [Real.rpow_mul np.le]
    exact Real.rpow_le_rpow B0 aCap (by norm_num)
  have Phalf : P^(1/2 : ℝ) ≤ N^(1/4 : ℝ) := by
    have h := Real.rpow_le_rpow pp.le mHi (by norm_num : (0 : ℝ) ≤ 1/2)
    rw [← Real.rpow_mul np.le] at h
    norm_num at h ⊢
    exact h
  have Pthree : P^(3/8 : ℝ) ≤ N^(3/16 : ℝ) := by
    have h := Real.rpow_le_rpow pp.le mHi (by norm_num : (0 : ℝ) ≤ 3/8)
    rw [← Real.rpow_mul np.le] at h
    norm_num at h ⊢
    exact h
  have Pneg : P^(-1/8 : ℝ) ≤ N^(-1/24 : ℝ) := by
    have cmp := Real.rpow_le_rpow (by positivity : 0 ≤ N^(1/3 : ℝ)) mLo (by norm_num : (0 : ℝ) ≤ 1/8)
    rw [← Real.rpow_mul np.le] at cmp
    norm_num at cmp
    rw [show (-1/8 : ℝ) = -(1/8 : ℝ) by ring, show (-1/24 : ℝ) = -(1/24 : ℝ) by ring,
      Real.rpow_neg pp.le, Real.rpow_neg np.le]
    have cast : P = (p : ℝ)*(q : ℝ) := by unfold P; push_cast; rfl
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (by simpa only [cast] using cmp)
  have xCap : X ≤ 2*N^((4097/4096-x)*(3/4)) := by
    calc
      _ ≤ (2*N^(4097/4096-x))^(3/4 : ℝ) := Real.rpow_le_rpow Y0 cofactorCap (by norm_num)
      _ = (2 : ℝ)^(3/4 : ℝ)*N^((4097/4096-x)*(3/4)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity),Real.rpow_mul np.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by positivity)
  have e1 : X*P^(1/2 : ℝ)*B^(1/2 : ℝ) ≤ 2*H := by
    calc
      _ ≤ (2*N^((4097/4096-x)*(3/4)))*N^(1/4 : ℝ)*N^((x+9/32768)*(1/2)) := by gcongr
      _ = 2*N^((4097/4096-x)*(3/4)+1/4+(x+9/32768)*(1/2)) := by
        rw [Real.rpow_add np,Real.rpow_add np]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)
  have e2 : X*P^(3/8 : ℝ)*B^(7/8 : ℝ) ≤ 2*H := by
    calc
      _ ≤ (2*N^((4097/4096-x)*(3/4)))*N^(3/16 : ℝ)*N^((x+9/32768)*(7/8)) := by gcongr
      _ = 2*N^((4097/4096-x)*(3/4)+3/16+(x+9/32768)*(7/8)) := by
        rw [Real.rpow_add np,Real.rpow_add np]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)
  have qQuarter : Q^(1/4 : ℝ) ≤ N^(5/8192 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ Q) qCap (by norm_num : (0 : ℝ) ≤ 1/4)
    rw [← Real.rpow_mul np.le] at h
    norm_num at h ⊢
    exact h
  have e3 : 2*Y*Q^(1/4 : ℝ)*B^(1/2 : ℝ) ≤ 4*H := by
    calc
      _ ≤ 2*(2*N^(4097/4096-x))*N^(5/8192 : ℝ)*N^((x+9/32768)*(1/2)) := by gcongr
      _ = 4*N^((4097/4096-x)+5/8192+(x+9/32768)*(1/2)) := by rw [Real.rpow_add np,Real.rpow_add np]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)
  have e4 : 2*Y*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ) ≤ 4*H := by
    calc
      _ ≤ 2*(2*N^(4097/4096-x))*N^(5/8192 : ℝ)*N^(-1/24 : ℝ)*N^((x+9/32768)*(7/8)) := by gcongr
      _ = 4*N^((4097/4096-x)+5/8192+(-1/24)+(x+9/32768)*(7/8)) := by
        rw [Real.rpow_add np ((4097/4096-x)+5/8192+(-1/24)), Real.rpow_add np ((4097/4096-x)+5/8192) (-1/24),
          Real.rpow_add np (4097/4096-x) (5/8192)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le n1 (by linarith only [xLo,xHi])) (by norm_num)

  have powerX : (K*P)^(3/4 : ℝ)*D^(3/2 : ℝ) = X := by
    unfold X Y
    have pow : (D^2)^(3/4 : ℝ) = D^(3/2 : ℝ) := by
      rw [← Real.rpow_natCast_mul dp.le 2]
      norm_num
    rw [Real.mul_rpow (by positivity : 0 ≤ K*P) (by positivity : 0 ≤ D^2),pow]
  have yd : (K*P)*D^(3/2 : ℝ) ≤ Y := by
    have dLe : D^(3/2 : ℝ) ≤ D^2 := calc
      _ ≤ D^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le d1 (by norm_num)
      _ = _ := by simpa only [Nat.cast_ofNat] using Real.rpow_natCast D 2
    exact mul_le_mul_of_nonneg_left dLe (by positivity)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < P*D^(3/2 : ℝ))).mpr
  change longCofactorSize (p*q) p A S T*(P*D^(3/2 : ℝ)) ≤ 24*T*H
  calc
    _ = (longCofactorSize (p*q) p A S T*P)*D^(3/2 : ℝ) := by ring
    _ ≤ (2*T*((K*P)^(3/4 : ℝ)*P^(1/2 : ℝ)*B^(1/2 : ℝ)+
      (K*P)^(3/4 : ℝ)*P^(3/8 : ℝ)*B^(7/8 : ℝ)+2*(K*P)*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+
        2*(K*P)*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ)))*D^(3/2 : ℝ) :=
      mul_le_mul_of_nonneg_right (long_cofactor_size_mul_modulus_le p0 m1 T1) (by positivity)
    _ = 2*T*(X*P^(1/2 : ℝ)*B^(1/2 : ℝ)+X*P^(3/8 : ℝ)*B^(7/8 : ℝ)+
        2*((K*P)*D^(3/2 : ℝ))*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+
        2*((K*P)*D^(3/2 : ℝ))*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ)) := by
      rw [← powerX]
      ring
    _ ≤ 2*T*(X*P^(1/2 : ℝ)*B^(1/2 : ℝ)+X*P^(3/8 : ℝ)*B^(7/8 : ℝ)+
        2*Y*Q^(1/4 : ℝ)*B^(1/2 : ℝ)+2*Y*Q^(1/4 : ℝ)*P^(-1/8 : ℝ)*B^(7/8 : ℝ)) := by gcongr
    _ ≤ 2*T*(2*H+2*H+4*H+4*H) := by gcongr
    _ = _ := by ring

end

end B13BoundedStepProductSavingProof

end

/- Outer far fixed residue -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

theorem norm_gated_outer_far_fixed_endpoints_le_wider_factor {n m g A S : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(1/2 : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ))
    (xLo : 27/4096 ≤ x) (xHi : x ≤ 1/3) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+9/32768))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(4097/4096-x))
    (A0 : 0 < A) (Am : A < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi a b : ℕ → ℤ) (ab : ∀ i ∈ I, a i ≤ b i)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ T*L) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T)
    (divisors : ∀ z ≤ 4*m^3, (z.divisors.card : ℝ) ≤ T) :
    ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun i j => centeredIntIntervalResidue m (a i) (b i) (c*((i : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      98*(n : ℝ)^(1023/1024 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)^(3/2 : ℝ)) := by
  let N := (n : ℝ)
  let M := (m : ℝ)
  let G := (g : ℝ)
  let H := N^(1023/1024 : ℝ)
  let D := ⌊N^(1/512 : ℝ)⌋₊
  let B := 96*H*T^3*L^2/(M*G^(3/2 : ℝ))
  let J := intIntervalModUnits m 0 S
  have np : 0 < N := zero_lt_one.trans_le n1
  have m0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have m1 : 1 ≤ M := show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast m0
  have mp : 0 < M := zero_lt_one.trans_le m1
  have gp : 0 < G := zero_lt_one.trans_le g1
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans L1
  have log0 := Real.log_nonneg m1
  have log2 : 2+Real.log (m : ℝ) ≤ 2*L := by linarith only [L1,logBound]
  have B0 : 0 ≤ B := by unfold B H; positivity
  have jProp (j : ℤ) (hj : j ∈ J) : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hj
  have uniform (h : ZMod m) (_ : h ≠ 0) (good : m.gcd h.val ≤ D)
      (weight : ℕ → ℂ) (wBound : ∀ i ∈ I, ‖weight i‖ ≤ ‖α i‖) :
      ‖gatedBilinearSum I J weight β lo hi
        (fun i j => ZMod.stdAddChar ((-(h*c))*(i : ZMod m)⁻¹*(j : ZMod m)⁻¹))‖ ≤ B := by
    let z := -(h*c)
    let q := m.gcd z.val
    let p := inverseFrequencyPeriod m z
    have product : p*q=m := Nat.div_mul_cancel (Nat.gcd_dvd_left m z.val)
    have p0 : 0 < p := inverse_frequency_period_pos z
    have pr : (0 : ℝ) < p := by exact_mod_cast p0
    have a : (m.gcd h.val : ℝ) ≤ N^(1/512 : ℝ) :=
      (by exact_mod_cast good : (m.gcd h.val : ℝ) ≤ (D : ℝ)).trans (Nat.floor_le (by positivity))
    have qCap : (q : ℝ) ≤ N^(5/2048 : ℝ) := calc
      _ ≤ (m.gcd h.val : ℝ)*(m.gcd c.val : ℝ) := by
        change (m.gcd (-(h*c)).val : ℝ) ≤ _
        exact_mod_cast gcd_fourier_phase_product_le h c
      _ ≤ N^(1/512 : ℝ)*N^(1/2048 : ℝ) := mul_le_mul a charBound (by positivity) (by positivity)
      _ ≤ _ := by rw [← Real.rpow_add np]; exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
    have long := scaled_long_cofactor_size_for_outer_far_wider_factor (n := n) (p := p) (q := q) (A := A) (S := S)
      (d := g) (T := 2*T) n1 pr (by simpa only [product] using m1) g1 (by linarith)
      (by simpa only [product] using mHi) (by simpa only [product] using mLo) qCap xLo xHi aCap
      (by simpa only [product] using cofactorCap)
    have long' : longCofactorSize m p A S (2*T) ≤ 24*(2*T)*H/(M*G^(3/2 : ℝ)) := by
      simpa only [product,H,M,G] using long
    have long0 : 0 ≤ longCofactorSize m p A S (2*T) := by
      unfold longCofactorSize reciprocalBilinearBound inverseFibreBudget
      positivity
    have est := norm_gated_long_cofactor_inverse_le_with_reduced_period z (p := p) le_rfl p0 I J
      (fun j hj => (jProp j hj).1) (fun j hj => (jProp j hj).2) weight β lo hi (mul_nonneg T0 L0) T0
      (by positivity : 0 ≤ 2*T) (fun i hi => (wBound i hi).trans (aw i hi)) bw
      (fun weight {_} X0 xw => inverse_frequency_fourth_moment_composite_le A0 Am I Icap copI weight X0 xw T1 divisors)
    refine est.trans ?_
    calc
      _ ≤ (2*L)*(T*L)*T*(24*(2*T)*H/(M*G^(3/2 : ℝ))) := by gcongr
      _ = _ := by unfold B; ring
  have est := norm_gated_residue_of_short_index_endpoints D I (fun i => (i : ZMod m))
    (fun i hi => (ZMod.isUnit_iff_coprime _ _).mpr (copI i hi)) α β lo hi a b
    (L := 0) (R := (S : ℤ)) ab B0 uniform
  have lMass : (∑ i ∈ I, ‖α i‖) ≤ (A : ℝ)*(T*L) := calc
    _ ≤ ∑ _ ∈ I, T*L := sum_le_sum aw
    _ = (I.card : ℝ)*(T*L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (card_le_card Icap).trans_eq (by simp [Nat.card_Icc])) (by positivity)
  have jSub : J ⊆ Ioc (0 : ℤ) (S : ℤ) := fun j hj => (jProp j hj).1
  have jSize : (J.card : ℝ) ≤ S := by
    exact_mod_cast (card_le_card jSub).trans_eq (by rw [Int.card_Ioc,sub_zero,Int.toNat_natCast])
  have rMass : (∑ j ∈ J, ‖β j‖) ≤ (S : ℝ)*T := calc
    _ ≤ ∑ _ ∈ J, T := sum_le_sum bw
    _ = (J.card : ℝ)*T := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right jSize (by positivity)
  have div_m : (m.divisors.card : ℝ) ≤ T := divisors m (by
    have h : m ≤ m^3 := by simpa only [pow_one] using pow_le_pow_right₀ m0 (show 1 ≤ 3 by decide)
    omega)
  have divisorFactor : (m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1) ≤ T*L/N^(1/512 : ℝ) := by
    have d : N^(1/512 : ℝ) ≤ (D : ℝ)+1 := (Nat.lt_floor_add_one (N^(1/512 : ℝ))).le
    calc
      _ ≤ T*L/((D : ℝ)+1) := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) d
  have core : (A : ℝ)*(S : ℝ) ≤ 2*N^(4097/4096+9/32768 : ℝ)/(M*G^2) := by
    apply (le_div_iff₀ (by positivity : 0 < M*G^2)).mpr
    calc
      _ = (A : ℝ)*((S : ℝ)*M*G^2) := by ring
      _ ≤ N^(x+9/32768)*(2*N^(4097/4096-x)) := mul_le_mul aCap cofactorCap (by positivity) (by positivity)
      _ = _ := by
        have sum : N^(x+9/32768)*N^(4097/4096-x) = N^(4097/4096+9/32768 : ℝ) := by rw [← Real.rpow_add np]; congr 1; ring
        calc
          _ = 2*(N^(x+9/32768)*N^(4097/4096-x)) := by ring
          _ = _ := by rw [sum]
  have gpow : G^(3/2 : ℝ) ≤ G^2 := by
    rw [← Real.rpow_natCast G 2]
    exact Real.rpow_le_rpow_of_exponent_le g1 (by norm_num)
  have tail : ((m.divisors.card : ℝ)*(1+Real.log m)/((D : ℝ)+1))*
       ((∑ i ∈ I, ‖α i‖)*(∑ j ∈ J, ‖β j‖)) ≤ 2*H*T^3*L^3/(M*G^(3/2 : ℝ)) := by
    calc
      _ ≤ (T*L/N^(1/512 : ℝ))*(((A : ℝ)*(T*L))*((S : ℝ)*T)) := by gcongr
      _ = (T*L/N^(1/512 : ℝ))*(((A : ℝ)*(S : ℝ))*T^2*L) := by ring
      _ ≤ (T*L/N^(1/512 : ℝ))*((2*N^(4097/4096+9/32768 : ℝ)/(M*G^2))*T^2*L) := by gcongr
      _ = 2*N^(32721/32768 : ℝ)*T^3*L^2/(M*G^2) := by
        have pow : N^(4097/4096+9/32768 : ℝ)/N^(1/512 : ℝ)=N^(32721/32768 : ℝ) := by rw [← Real.rpow_sub np]; norm_num
        rw [← pow]
        ring
      _ ≤ _ := by
        have h : N^(32721/32768 : ℝ) ≤ H := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        have l : L^2 ≤ L^3 := pow_le_pow_right₀ L1 (by decide)
        gcongr
  exact est.trans ((add_le_add (mul_le_mul_of_nonneg_right logBound B0) tail).trans_eq (by unfold B H; ring))

theorem norm_gated_outer_far_fixed_endpoints_le {n m g A S : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(1/2 : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ))
    (xLo : 31/4096 ≤ x) (xHi : x ≤ 1/3) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+9/32768))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(4097/4096-x))
    (A0 : 0 < A) (Am : A < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (lo hi a b : ℕ → ℤ) (ab : ∀ i ∈ I, a i ≤ b i)
    (aw : ∀ i ∈ I, ‖α i‖ ≤ T*L) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T)
    (divisors : ∀ z ≤ 4*m^3, (z.divisors.card : ℝ) ≤ T) :
    ‖gatedBilinearSum I (intIntervalModUnits m 0 S) α β lo hi
      (fun i j => centeredIntIntervalResidue m (a i) (b i) (c*((i : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      98*(n : ℝ)^(1023/1024 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)^(3/2 : ℝ)) :=
  norm_gated_outer_far_fixed_endpoints_le_wider_factor
    charBound n1 g1 T1 L1 mHi mLo (by linarith only [xLo]) xHi logBound aCap cofactorCap A0 Am I Icap copI α β lo hi a b ab aw bw divisors

end

end B13BoundedStepProductSavingProof

end

/- Outer far endpoint bucket -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

theorem outer_far_endpoint_bucket_budget {n m g : ℕ}
    (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ)) :
    let cap := ⌊(m : ℝ)*(g : ℝ)*(n : ℝ)^(1/8192 : ℝ)⌋₊
    let d := ⌊(m : ℝ)*(n : ℝ)^(-1/2048 : ℝ)⌋₊
    0 < d ∧ ((cap/d+1 : ℕ) : ℝ) ≤ 3*(g : ℝ)*(n : ℝ)^(5/8192 : ℝ) ∧
      (d : ℝ)/(m : ℝ) ≤ (n : ℝ)^(-1/2048 : ℝ) := by
  dsimp only
  let N := (n : ℝ)
  let P := (m : ℝ)
  let G := (g : ℝ)
  let cap := ⌊P*G*N^(1/8192 : ℝ)⌋₊
  let d := ⌊P*N^(-1/2048 : ℝ)⌋₊
  have np : 0 < N := zero_lt_one.trans_le n1
  have pp : 0 < P := (Real.rpow_pos_of_pos np _).trans_le mLo
  have gp : 0 < G := zero_lt_one.trans_le g1
  have v1 : 1 ≤ P*N^(-1/2048 : ℝ) := calc
    1 ≤ N^(1/3-1/2048 : ℝ) := Real.one_le_rpow n1 (by norm_num)
    _ = N^(1/3 : ℝ)*N^(-1/2048 : ℝ) := by rw [sub_eq_add_neg,Real.rpow_add np]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right mLo (by positivity)
  have d1 : 1 ≤ d := Nat.le_floor v1
  have dp : (0 : ℝ) < d := by exact_mod_cast d1
  have low : P*N^(-1/2048 : ℝ) ≤ 2*(d : ℝ) := by
    have dR : (1 : ℝ) ≤ d := by exact_mod_cast d1
    have fl := Nat.lt_floor_add_one (P*N^(-1/2048 : ℝ))
    change P*N^(-1/2048 : ℝ) < (d : ℝ)+1 at fl
    linarith only [dR,fl]
  have upper : (d : ℝ) ≤ P*N^(-1/2048 : ℝ) := Nat.floor_le (by positivity)
  have capUp : (cap : ℝ) ≤ P*G*N^(1/8192 : ℝ) := Nat.floor_le (by positivity)
  have divided : ((cap/d : ℕ) : ℝ) ≤ (cap : ℝ)/(d : ℝ) :=
    (le_div_iff₀ dp).mpr (by exact_mod_cast Nat.div_mul_le_self cap d)
  have est : (cap : ℝ) ≤ (2*G*N^(5/8192 : ℝ))*(d : ℝ) := calc
    _ ≤ P*G*N^(1/8192 : ℝ) := capUp
    _ = (G*N^(5/8192 : ℝ))*(P*N^(-1/2048 : ℝ)) := by
      have r : N^(5/8192 : ℝ)*N^(-1/2048 : ℝ) = N^(1/8192 : ℝ) := by rw [← Real.rpow_add np]; norm_num
      calc
        _ = P*G*(N^(5/8192 : ℝ)*N^(-1/2048 : ℝ)) := by rw [r]
        _ = _ := by ring
    _ ≤ (G*N^(5/8192 : ℝ))*(2*(d : ℝ)) := mul_le_mul_of_nonneg_left low (by positivity)
    _ = _ := by ring
  have q := divided.trans ((div_le_iff₀ dp).mpr est)
  have one : 1 ≤ G*N^(5/8192 : ℝ) := one_le_mul_of_one_le_of_one_le g1 (Real.one_le_rpow n1 (by norm_num))
  refine ⟨d1,?_,(div_le_iff₀ pp).mpr (by simpa only [mul_comm] using upper)⟩
  change ((cap/d+1 : ℕ) : ℝ) ≤ 3*G*N^(5/8192 : ℝ)
  push_cast
  linarith only [q,one]

end

end B13BoundedStepProductSavingProof

end

/- Outer far ratio hyperbola -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical

noncomputable section

set_option maxHeartbeats 1500000 in
theorem norm_outer_far_ratio_hyperbola_le_wider_factor {n m g A S num l r : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(1/2 : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ))
    (gCap : (g : ℝ) ≤ (n : ℝ)^(1/4096 : ℝ))
    (xLo : 27/4096 ≤ x) (xHi : x ≤ 1/3) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+9/32768))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(4097/4096-x))
    (rCap : (r : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(4097/4096 : ℝ))
    (endCap : num/(l+1) ≤ ⌊(m : ℝ)*(g : ℝ)*(n : ℝ)^(1/8192 : ℝ)⌋₊)
    (A0 : 0 < A) (Am : A < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (baseLo baseHi : ℕ → ℤ)
    (aw : ∀ a ∈ I, ‖α a‖ ≤ T*L) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T)
    (divisors : ∀ z ≤ 4*m^3, (z.divisors.card : ℝ) ≤ T)
    (dR : ∀ z ≤ r, (z.divisors.card : ℝ) ≤ T) :
    let J := intIntervalModUnits m 0 S
    let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (baseLo a)
    let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (baseHi a)
    ‖gatedBilinearSum I J α β lo hi
        (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
          (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      592*(n : ℝ)^(4095/4096 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)) := by
  dsimp only
  let P := (m : ℝ)
  let N := (n : ℝ)
  let G := (g : ℝ)
  let C := G^(1/2 : ℝ)
  let H := N^(4095/4096 : ℝ)
  let J := intIntervalModUnits m 0 S
  let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (baseLo a)
  let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (baseHi a)
  let R := 98*N^(1023/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ))
  let d := ⌊P*N^(-1/2048 : ℝ)⌋₊
  let cap := ⌊P*G*N^(1/8192 : ℝ)⌋₊
  have m1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have pp : 0 < P := zero_lt_one.trans_le m1
  have np : 0 < N := zero_lt_one.trans_le n1
  have gp : 0 < G := zero_lt_one.trans_le g1
  have cp : 0 < C := by unfold C; positivity
  have t0 := zero_le_one.trans T1
  have l0 := zero_le_one.trans L1
  have log0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg m1
  have R0 : 0 ≤ R := by unfold R; positivity
  have bound : R ≤ 98*N^(1023/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ)) := le_rfl
  obtain ⟨d0,dcount,dsmall⟩ := outer_far_endpoint_bucket_budget n1 g1 mLo
  have rUp : (r : ℝ) ≤ 2*N^(4097/4096 : ℝ)/(P*G^2) := (le_div_iff₀ (by positivity)).mpr (by
    have h := rCap
    change (r : ℝ)*P*G^2 ≤ 2*N^(4097/4096 : ℝ) at h
    convert h using 1
    ring)
  have jPos (j : ℤ) (hj : j ∈ J) : 0 < j := by
    have data : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod m) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    exact (mem_Ioc.mp data.1).1
  let mass := ∑ j ∈ J, ‖β j‖*∑ a ∈ I, if lo a < j ∧ j ≤ hi a then ‖α a‖ else 0
  have mass0 : 0 ≤ mass := by
    unfold mass
    exact sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (sum_nonneg fun a _ => by split_ifs <;> positivity)
  have massCut : mass ≤ (2*N^(4097/4096 : ℝ)/(P*G^2))*T^3*L := by
    have b := gated_left_weight_mass_le α β lo hi (mul_nonneg t0 l0) t0
      (fun u hu => dR u (mem_Icc.mp hu).2) (fun a ha => (mem_Icc.mp (Icap ha)).1)
      (fun j hj => (jPos j hj).le) (fun a ha j hj active => ?_) aw bw
    · refine b.trans ?_
      calc
        _ ≤ (2*N^(4097/4096 : ℝ)/(P*G^2))*T*(T*L)*T := by gcongr
        _ = _ := by ring
    · have ja : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (jPos j hj).le
      have jR : j.toNat ≤ r/a := by
        have h : (j.toNat : ℤ) ≤ ((r/a : ℕ) : ℤ) := by rw [ja]; exact active.2.trans (min_le_left _ _)
        exact_mod_cast h
      have ap := (mem_Icc.mp (Icap ha)).1
      have jn : 0 < j.toNat := by have := jPos j hj; omega
      exact mem_Icc.mpr ⟨mul_pos ap jn,by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ap).mp jR⟩
  have est : ‖gatedBilinearSum I J α β lo hi
      (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
        (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
          ((cap/d+1 : ℕ) : ℝ)*(2*R)+(2*((d : ℝ)/P))*mass := by
    let phase (a : ℕ) (j : ℤ) := c*((a : ZMod m)*(j : ZMod m))⁻¹
    let e (a : ℕ) (j : ℤ) := (num : ℤ)/((a*j.toNat : ℕ) : ℤ)
    rw [gated_bilinear_sum_eq_pair_sum]
    refine norm_gated_product_interval_le_of_ratio_window (num := num) (p := m) I J α β _ baseLo baseHi (fun a ha => (mem_Icc.mp (Icap ha)).1)
      jPos d0 endCap ?_
    intro u v b t vb bt bracket
    rw [← gated_bilinear_sum_eq_pair_sum]
    refine norm_gated_residue_variable_endpoint_le m I J α β u v vb bt phase e
      (fun a ha j hj gate => (bracket a ha j hj gate).2) ?_ ?_
    · exact norm_gated_outer_far_fixed_endpoints_le_wider_factor charBound n1 g1 T1 L1 mHi mLo xLo xHi
        logBound aCap cofactorCap A0 Am I Icap copI α β u v (fun _ => 0) (fun _ => b) (fun _ _ => vb) aw bw divisors
    · apply norm_gated_outer_far_fixed_endpoints_le_wider_factor charBound n1 g1 T1 L1 mHi mLo xLo xHi
        logBound aCap cofactorCap A0 Am I Icap copI _ _ u v (fun _ => b) (fun _ => t) (fun _ _ => bt) ?_ ?_ divisors
      · intro a ha
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (α a))] using aw a ha
      · intro j hj
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (β j))] using bw j hj
  have e1 : ((cap/d+1 : ℕ) : ℝ)*(2*R) ≤ 588*H*T^3*L^3/(P*G) := by
    have Ghalf : G^(3/2 : ℝ) = G*C := by
      unfold C
      rw [mul_comm G,← Real.rpow_add_one gp.ne']
      norm_num
    have CC : C^2 = G := by unfold C; rw [← Real.rpow_mul_natCast gp.le]; norm_num
    have cpow : C ≤ N^(1/8192 : ℝ) := by
      have b := Real.rpow_le_rpow gp.le gCap (by norm_num : (0 : ℝ) ≤ 1/2)
      rw [← Real.rpow_mul np.le] at b
      norm_num at b ⊢
      exact b
    calc
      _ ≤ (3*G*N^(5/8192 : ℝ))*(2*(98*N^(1023/1024 : ℝ)*T^3*L^3/(P*G^(3/2 : ℝ)))) := by gcongr
      _ = 588*N^(8189/8192 : ℝ)*T^3*L^3*C/(P*G) := by
        have add : N^(5/8192 : ℝ)*N^(1023/1024 : ℝ) = N^(8189/8192 : ℝ) := by
          rw [← Real.rpow_add np]
          norm_num
        calc
          _ = 588*(N^(5/8192 : ℝ)*N^(1023/1024 : ℝ))*T^3*L^3*G/(P*G^(3/2 : ℝ)) := by ring
          _ = _ := by
            have frac : G/(P*(G*C)) = C/(P*G) := by
              rw [← CC]
              field_simp [pp.ne',cp.ne']
            rw [add,Ghalf]
            calc
              _ = (588*N^(8189/8192 : ℝ)*T^3*L^3)*(G/(P*(G*C))) := by ring
              _ = _ := by rw [frac]; ring
      _ ≤ 588*N^(8189/8192 : ℝ)*T^3*L^3*N^(1/8192 : ℝ)/(P*G) := by gcongr
      _ ≤ _ := by
        have add : N^(8189/8192 : ℝ)*N^(1/8192 : ℝ) ≤ H := by
          unfold H
          rw [← Real.rpow_add np]
          exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        calc
          _ = 588*(N^(8189/8192 : ℝ)*N^(1/8192 : ℝ))*T^3*L^3/(P*G) := by ring
          _ ≤ _ := by gcongr
  have e2 : (2*((d : ℝ)/P))*mass ≤ 4*H*T^3*L^3/(P*G) := by
    have lg : L ≤ L^3 := by simpa only [pow_one] using pow_le_pow_right₀ L1 (show 1 ≤ 3 by decide)
    have pow : N^(-1/2048 : ℝ)*N^(4097/4096 : ℝ) = H := by
      unfold H
      rw [← Real.rpow_add np]
      norm_num
    calc
      _ ≤ (2*N^(-1/2048 : ℝ))*((2*N^(4097/4096 : ℝ)/(P*G^2))*T^3*L) := by gcongr
      _ = 4*H*T^3*L/(P*G^2) := by
        calc
          _ = 4*(N^(-1/2048 : ℝ)*N^(4097/4096 : ℝ))*T^3*L/(P*G^2) := by ring
          _ = _ := by rw [pow]
      _ ≤ 4*H*T^3*L^3/(P*G^2) := by gcongr
      _ ≤ _ := by
        have gPow : G ≤ G^2 := by simpa only [pow_one] using pow_le_pow_right₀ g1 (show 1 ≤ 2 by decide)
        gcongr
  exact est.trans ((add_le_add e1 e2).trans_eq (by ring))

set_option maxHeartbeats 1500000 in
theorem norm_outer_far_ratio_hyperbola_le {n m g A S num l r : ℕ} [NeZero m]
    {c : ZMod m} (charBound : (m.gcd c.val : ℝ) ≤ (n : ℝ)^(1/2048 : ℝ))
    {T L x : ℝ} (n1 : 1 ≤ (n : ℝ)) (g1 : 1 ≤ (g : ℝ)) (T1 : 1 ≤ T) (L1 : 1 ≤ L)
    (mHi : (m : ℝ) ≤ (n : ℝ)^(1/2 : ℝ)) (mLo : (n : ℝ)^(1/3 : ℝ) ≤ (m : ℝ))
    (gCap : (g : ℝ) ≤ (n : ℝ)^(1/4096 : ℝ))
    (xLo : 31/4096 ≤ x) (xHi : x ≤ 1/3) (logBound : 1+Real.log (m : ℝ) ≤ L)
    (aCap : (A : ℝ) ≤ (n : ℝ)^(x+9/32768))
    (cofactorCap : (S : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(4097/4096-x))
    (rCap : (r : ℝ)*(m : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)^(4097/4096 : ℝ))
    (endCap : num/(l+1) ≤ ⌊(m : ℝ)*(g : ℝ)*(n : ℝ)^(1/8192 : ℝ)⌋₊)
    (A0 : 0 < A) (Am : A < m)
    (I : Finset ℕ) (Icap : I ⊆ Icc 1 A) (copI : ∀ i ∈ I, i.Coprime m)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (baseLo baseHi : ℕ → ℤ)
    (aw : ∀ a ∈ I, ‖α a‖ ≤ T*L) (bw : ∀ j ∈ intIntervalModUnits m 0 S, ‖β j‖ ≤ T)
    (divisors : ∀ z ≤ 4*m^3, (z.divisors.card : ℝ) ≤ T)
    (dR : ∀ z ≤ r, (z.divisors.card : ℝ) ≤ T) :
    let J := intIntervalModUnits m 0 S
    let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (baseLo a)
    let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (baseHi a)
    ‖gatedBilinearSum I J α β lo hi
        (fun a j => centeredIntIntervalResidue m 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
          (c*((a : ZMod m)*(j : ZMod m))⁻¹))‖ ≤
      592*(n : ℝ)^(4095/4096 : ℝ)*T^3*L^3/((m : ℝ)*(g : ℝ)) :=
  norm_outer_far_ratio_hyperbola_le_wider_factor
    charBound n1 g1 T1 L1 mHi mLo gCap (by linarith only [xLo]) xHi logBound aCap cofactorCap rCap endCap A0 Am I Icap copI α β baseLo baseHi aw bw divisors dR

end

end B13BoundedStepProductSavingProof

end

/- Right high factor support -/
section

namespace B13BoundedStepProductSavingProof

open Finset ArithmeticFunction DyadicMixedB4Scale
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

theorem right_high_wave_factor_eq_zero_below_square {n b : ℕ}
    (short : b < (rightVaughanCut n+1)^2) : rightHighWaveFactor n b = 0 := by
  unfold rightHighWaveFactor
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun x y => (((μ : ArithmeticFunction ℝ)-rightVaughanMoebius n) x)*
      ((vonMangoldt-rightVaughanMangoldt n) y))]
  refine sum_eq_zero fun d hd => ?_
  let P := rightVaughanCut n
  by_cases h : d ≤ P
  · have zero : (((μ : ArithmeticFunction ℝ)-rightVaughanMoebius n) d) = 0 := by
      change (μ d : ℝ)-(if d ≤ P then (μ d : ℝ) else 0) = 0
      rw [ite_eq_left h,sub_self]
    rw [zero,zero_mul]
  · have q : b/d ≤ P := by
      by_contra! hq
      have mulTop : (P+1)^2 ≤ d*(b/d) := by
        rw [pow_two]
        exact Nat.mul_le_mul (Nat.succ_le_of_lt (lt_of_not_ge h)) (Nat.succ_le_of_lt hq)
      have hdv := Nat.dvd_of_mem_divisors hd
      rw [Nat.mul_div_cancel' hdv] at mulTop
      exact (not_le_of_gt short) mulTop
    have zero : ((vonMangoldt-rightVaughanMangoldt n) (b/d)) = 0 := by
      change vonMangoldt (b/d) - (if b/d ≤ P then vonMangoldt (b/d) else 0) = 0
      rw [ite_eq_left q,sub_self]
    rw [zero,mul_zero]

theorem right_high_wave_factor_eq_zero_of_rpow_cut {n b : ℕ}
    (short : b ≤ ⌊(n : ℝ)^(1/128 : ℝ)⌋₊) : rightHighWaveFactor n b = 0 := by
  apply right_high_wave_factor_eq_zero_below_square
  let N := (n : ℝ)
  let Q := N^(1/256 : ℝ)
  let P := rightVaughanCut n
  have q0 : 0 ≤ Q := by unfold Q; positivity
  have q : Q < (P : ℝ)+1 := Nat.lt_floor_add_one _
  have s : Q^2 < ((P : ℝ)+1)^2 := by
    have pos : 0 < (P : ℝ)+1+Q := by positivity
    nlinarith only [mul_pos (sub_pos.mpr q) pos]
  have e : Q^2 = N^(1/128 : ℝ) := by
    unfold Q
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ N)]
    norm_num
  have bTop : (b : ℝ) ≤ N^(1/128 : ℝ) :=
    ((show (b : ℝ) ≤ (⌊N^(1/128 : ℝ)⌋₊ : ℝ) by exact_mod_cast short)).trans (Nat.floor_le (by positivity))
  have done : (b : ℝ) < ((P : ℝ)+1)^2 := bTop.trans_lt (e ▸ s)
  exact_mod_cast done

end

end B13BoundedStepProductSavingProof

end

/- High far strip windows geometry -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def highFarStripProductCap (n : ℕ) : ℕ := 2*⌊(n : ℝ)^(4097/4096 : ℝ)⌋₊

def highFarStripFactorCut (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/128 : ℝ)⌋₊

def highFarStripFactorLower (n k : ℕ) : ℕ :=
  max (highFarStripFactorCut n) (swappedHighFactorFloor n k)

def highFarStripFactorBlock (n k : ℕ) : Finset ℕ :=
  Ioc (highFarStripFactorLower n k) (min (outerRightFactorCap n) (swappedHighFactorFloor n (k+1)))

def highFarStripStepUpper (n m : ℕ) : ℕ :=
  min (expandedWideStepCap n) (highFarStripProductCap n/m)

def highFarStripFactors (n m g e k : ℕ) : Finset ℕ :=
  (Ioc (highFarStripFactorLower n k/e)
      (min (outerRightFactorCap n) (swappedHighFactorFloor n (k+1))/e)).filter
    (fun a => (e*a).gcd g=e ∧ a.Coprime (m/g))

def highFarStripCofactorCap (n m g e k : ℕ) : ℕ :=
  (highFarStripStepUpper n m/g)/(highFarStripFactorLower n k/e+1)

end

end B13BoundedStepProductSavingProof

end

/- High far strip gate -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

theorem expanded_high_modulus_cap_le_short_low {n : ℕ} (n0 : 0 < n) :
    expandedHighModulusCap n ≤ shortLowModulusCap n :=
  Nat.floor_mono
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n0) (by norm_num : (515/1024 : ℝ) ≤ 133/256))

theorem twice_le_high_far_strip_cap (n : ℕ) : 2*n ≤ highFarStripProductCap n := by
  rcases eq_or_ne n 0 with rfl | n0
  · norm_num [highFarStripProductCap, Real.zero_rpow]
  · apply Nat.mul_le_mul_left
    apply Nat.le_floor
    have nr : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero n0
    calc
      (n : ℝ) = (n : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le nr (by norm_num)

theorem high_far_strip_cap_le_expanded_product (n : ℕ) :
    highFarStripProductCap n ≤ expandedHyperbolaProductCap n := by
  rcases eq_or_ne n 0 with rfl | n0
  · norm_num [highFarStripProductCap,expandedHyperbolaProductCap,Real.zero_rpow]
  · apply Nat.mul_le_mul_left
    exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero n0)
      (by norm_num : (4097/4096 : ℝ) ≤ 513/512))

def highFarStripGate (n : ℕ) (row : ℕ × ℕ) (v : ℕ) : Prop :=
  let u := leftBilinearStep row
  u ≤ extendedWideStepCap n ∧ v ≤ expandedWideStepCap n ∧ shortLowModulusCap n < v ∧
    prefixStepGate n u v ∧ 2*n < u*v ∧ thinHighProductCap n < u*v ∧ u*v ≤ highFarStripProductCap n ∧
    u.gcd v ≤ thinHighGcdCap n ∧ u.gcd n ≤ thinHighLeftDivisorCap n

theorem high_far_strip_row_mem {n v : ℕ} {row : ℕ × ℕ}
    (large : (2 : ℝ) ≤ (n : ℝ)^(1/64 : ℝ))
    (hi : row ∈ bilateralLeftWaveItems n)
    (hg : highFarStripGate n row v) : row ∈ outerRightRows n := by
  let u := leftBilinearStep row
  let N := (n : ℝ)
  let U := (u : ℝ)
  let V := (v : ℝ)
  obtain ⟨_,hiV,loV,_,_,loP,hiP,_,char⟩ := hg
  have step := mem_Icc.mp (bilateral_left_step_range hi)
  have n0 : 0 < n := step.1.trans step.2
  have nr : 1 ≤ N := by change (1 : ℝ) ≤ (n : ℝ); exact_mod_cast n0
  have np : 0 < N := zero_lt_one.trans_le nr
  have vLo : N^(133/256 : ℝ) < V := (Nat.lt_floor_add_one _).trans_le (by
    change (shortLowModulusCap n : ℝ)+1 ≤ (v : ℝ)
    exact_mod_cast Nat.succ_le_of_lt loV)
  have vHi : V ≤ N^(511/768 : ℝ) :=
    (show V ≤ (expandedWideStepCap n : ℝ) by
      change (v : ℝ) ≤ (expandedWideStepCap n : ℝ)
      exact_mod_cast hiV).trans (Nat.floor_le (by positivity))
  have prodLower : N^(8191/8192 : ℝ) ≤ U*V := (Nat.lt_floor_add_one _).le.trans (by
    change (thinHighProductCap n : ℝ)+1 ≤ (u : ℝ)*(v : ℝ)
    exact_mod_cast Nat.succ_le_of_lt loP)
  have prodUpper : U*V ≤ 2*N^(4097/4096 : ℝ) := by
    calc
      _ ≤ (highFarStripProductCap n : ℝ) := by
        change (u : ℝ)*(v : ℝ) ≤ (highFarStripProductCap n : ℝ)
        exact_mod_cast hiP
      _ ≤ _ := by unfold highFarStripProductCap; push_cast; gcongr; exact Nat.floor_le (by positivity)
  have geoLo : N^(171/512 : ℝ) ≤ U := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (511/768 : ℝ))).mp
    calc
      _ ≤ N^(8191/8192 : ℝ) := by
        rw [← Real.rpow_add np]
        exact Real.rpow_le_rpow_of_exponent_le nr (by norm_num)
      _ ≤ U*V := prodLower
      _ ≤ _ := mul_le_mul_of_nonneg_left vHi (by positivity)
  have geoHi : U ≤ N^(1/2 : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (133/256 : ℝ))).mp
    calc
      _ ≤ U*V := mul_le_mul_of_nonneg_left vLo.le (by positivity)
      _ ≤ 2*N^(4097/4096 : ℝ) := prodUpper
      _ ≤ N^(1/64 : ℝ)*N^(4097/4096 : ℝ) := mul_le_mul_of_nonneg_right large (by positivity)
      _ ≤ N^(1/2 : ℝ)*N^(133/256 : ℝ) := by
        rw [← Real.rpow_add np,← Real.rpow_add np]
        exact Real.rpow_le_rpow_of_exponent_le nr (by norm_num)
  have square : u^2 ≤ n := by
    rw [← Real.sqrt_eq_rpow] at geoHi
    have sq : (u : ℝ)^2 ≤ (n : ℝ) := (Real.le_sqrt (by positivity) (by positivity)).mp geoHi
    exact_mod_cast sq
  exact mem_filter.mpr ⟨hi,square,geoLo,char⟩

theorem eventually_high_far_strip_scale : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (n : ℝ)^(1/64 : ℝ) := by
  exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/64)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2

end

end B13BoundedStepProductSavingProof

end

/- Wider low far selection -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

theorem subcritical_product_cap_le_n {n : ℕ} (n0 : 0 < n) :
    subcriticalMediumProductCap n ≤ n := by
  refine (thin_high_product_cap_ge_old n).trans ?_
  have h : (thinHighProductCap n : ℝ) ≤ (n : ℝ) :=
    (Nat.floor_le (by positivity)).trans
      (Real.rpow_le_self_of_one_le (by exact_mod_cast n0) (by norm_num : (8191/8192 : ℝ) ≤ 1))
  exact_mod_cast h

end

end B13BoundedStepProductSavingProof

end

/- Small modulus product geometry -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def smallModulusProductGate (n u v : ℕ) : Prop :=
  v ≤ expandedHighModulusCap n ∧ prefixStepGate n u v ∧ u*v ≤ highFarStripProductCap n

def smallModulusProductRows (n : ℕ) {κ : Type} (J : Finset κ) (v b c : κ → ℕ) : Finset κ :=
  J.filter fun j =>
    (n : ℝ)^(171/512 : ℝ) ≤ (v j : ℝ) ∧ v j ≤ expandedHighModulusCap n ∧
      (v j).gcd n ≤ targetDivisorCap n ∧ b j < c j

def smallModulusProductLower (n v : ℕ) : ℕ :=
  max (primeHyperbolaShortLeftLo n v) (thinHighProductCap n/v)

def smallModulusProductUpper (n v : ℕ) : ℕ :=
  min (expandedWideStepCap n) (highFarStripProductCap n/v)

theorem small_modulus_product_range {n v : ℕ} (n0 : 0 < n) :
    smallModulusProductUpper n v ≤ n ∧
      smallModulusProductUpper n v*v ≤ expandedHyperbolaProductCap n ∧
      subcriticalMediumProductCap n/v ≤ smallModulusProductLower n v := by
  refine ⟨(min_le_left _ _).trans (expanded_wide_step_le n0), ?_,
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)⟩
  exact (((Nat.mul_le_mul_right v (min_le_right _ _)).trans (Nat.div_mul_le_self _ _))).trans
    (high_far_strip_cap_le_expanded_product n)

theorem small_modulus_product_floor_le_expanded {n : ℕ} (n0 : 0 < n) :
    expandedHighModulusCap n ≤ expandedWideStepCap n :=
  Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n0)
    (by norm_num : (515/1024 : ℝ) ≤ 511/768))

theorem small_modulus_product_lower_bound {n u v : ℕ} (n0 : 0 < n)
    (uHi : u ≤ expandedWideStepCap n) (prod : thinHighProductCap n < u*v) :
    (n : ℝ)^(171/512 : ℝ) ≤ (v : ℝ) := by
  let N := (n : ℝ)
  let U := (u : ℝ)
  let V := (v : ℝ)
  have n1 : 1 ≤ N := by change (1 : ℝ) ≤ n; exact_mod_cast n0
  have np : 0 < N := zero_lt_one.trans_le n1
  have uR : U ≤ N^(511/768 : ℝ) :=
    (show U ≤ (expandedWideStepCap n : ℝ) by
      change (u : ℝ) ≤ (expandedWideStepCap n : ℝ)
      exact_mod_cast uHi).trans (Nat.floor_le (by positivity))
  have lower : N^(8191/8192 : ℝ) ≤ U*V := (Nat.lt_floor_add_one _).le.trans (by
    change (thinHighProductCap n : ℝ)+1 ≤ (u : ℝ)*(v : ℝ)
    exact_mod_cast Nat.succ_le_of_lt prod)
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (511/768 : ℝ))).mp
  calc
    _ ≤ N^(8191/8192 : ℝ) := by
      rw [← Real.rpow_add np]
      exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
    _ ≤ U*V := lower
    _ ≤ _ := by rw [mul_comm U V]; exact mul_le_mul_of_nonneg_left uR (by positivity)

theorem small_modulus_product_membership {κ : Type} {n : ℕ} {J : Finset κ} {v b c : κ → ℕ}
    {i : ℕ × ℕ} {j : κ}
    (hi : i ∈ bilateralLeftWaveItems n) (hj : j ∈ J) (v0 : 0 < v j) :
    (j ∈ smallModulusProductRows n J v b c ∧ i ∈ boundedOuterLeftRowItems n (v j)
      (smallModulusProductLower n (v j)) (smallModulusProductUpper n (v j))) ↔
      (leftBilinearStep i ≤ expandedWideStepCap n ∧ v j ≤ expandedWideStepCap n) ∧
        boundedOuterLeftKeptGate smallModulusProductGate n (leftBilinearStep i) (v j) ∧
        b j < c j ∧ (leftBilinearStep i).gcd (v j) ∣ n := by
  let u := leftBilinearStep i
  let m := v j
  have range := mem_Icc.mp (bilateral_left_step_range hi)
  have n0 : 0 < n := range.1.trans range.2
  constructor
  · rintro ⟨hr,hc⟩
    obtain ⟨_,_,modTop,char,ends⟩ := mem_filter.mp hr
    obtain ⟨_,hG,lo,up⟩ := mem_filter.mp hc
    obtain ⟨div,gSmall,gMax,_⟩ := mem_filter.mp hG
    have compat := (Nat.mem_divisors.mp div).1
    have thin : thinHighProductCap n < u*m :=
      (Nat.div_lt_iff_lt_mul v0).mp ((le_max_right _ _).trans_lt lo)
    have product : maximumStep n^2 < u*m := (Nat.div_lt_iff_lt_mul v0).mp
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt ((le_max_left _ _).trans_lt lo))
    have top : u*m ≤ highFarStripProductCap n :=
      (Nat.le_div_iff_mul_le v0).mp (up.trans (min_le_right _ _))
    exact ⟨⟨up.trans (min_le_left _ _),modTop.trans (small_modulus_product_floor_le_expanded n0)⟩,
      ⟨⟨modTop,⟨product,gMax⟩,top⟩,thin,gSmall,char⟩,ends,compat⟩
  · rintro ⟨⟨uHi,_⟩,⟨⟨modTop,pref,top⟩,thin,gSmall,char⟩,ends,compat⟩
    have hr : j ∈ smallModulusProductRows n J v b c :=
      mem_filter.mpr ⟨hj,small_modulus_product_lower_bound n0 uHi thin,modTop,char,ends⟩
    have hG : u.gcd m ∈ swappedHighDivisors n m :=
      mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨compat,n0.ne'⟩,gSmall,pref.2,Nat.gcd_dvd_right _ _⟩
    have markedLeft := (mem_filter.mp (mem_filter.mp hi).1).2
    have lo : smallModulusProductLower n m < u :=
      max_lt (max_lt markedLeft (max_lt ((Nat.div_lt_iff_lt_mul v0).mpr pref.1)
        ((Nat.div_lt_iff_lt_mul v0).mpr ((thin_high_product_cap_ge_old n).trans_lt thin))))
        ((Nat.div_lt_iff_lt_mul v0).mpr thin)
    have up : u ≤ smallModulusProductUpper n m := le_min uHi ((Nat.le_div_iff_mul_le v0).mpr top)
    exact ⟨hr,mem_filter.mpr ⟨hi,hG,lo,up⟩⟩

end

end B13BoundedStepProductSavingProof

end

/- Small modulus product saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter
open scoped Classical Finset

noncomputable section

private theorem expand_outer_index {α : Type*} {S T : Finset α} (h : S ⊆ T)
    (f : α → ℂ) : (∑ a ∈ S, f a) = ∑ a ∈ T, if a ∈ S then f a else 0 := by
  rw [← sum_filter]
  have eq : T.filter (fun a => a ∈ S) = S := by
    ext a
    exact ⟨fun ha => (mem_filter.mp ha).2,fun ha => mem_filter.mpr ⟨h ha,ha⟩⟩
  rw [eq]

theorem small_modulus_product_residue_eq_kept_from {n : ℕ}
    {κ : Type}
    (J : Finset κ) (v b c : κ → ℕ) (w : κ → ℂ)
    (steps : ∀ j ∈ J, v j ∈ Icc 1 n) (ends : ∀ j ∈ J, c j ≤ n/v j) :
    boundedDividedResidueFrom smallModulusProductLower smallModulusProductUpper n (smallModulusProductRows n J v b c) v b c w = boundedOuterLeftKeptFrom smallModulusProductGate n J v b c w := by
  let X := bilateralLeftWaveItems n
  let R := smallModulusProductRows n J v b c
  let Q (j : κ) := boundedOuterLeftRowItems n (v j) (smallModulusProductLower n (v j)) (smallModulusProductUpper n (v j))
  let u := leftBilinearStep
  let V (i : ℕ × ℕ) (j : κ) := leftBilinearWeight n i*w j*
    (pairResidueError n (u i) (v j) 0 (n/u i) (b j) (c j) : ℂ)
  have lhs : boundedDividedResidueFrom smallModulusProductLower smallModulusProductUpper n (smallModulusProductRows n J v b c) v b c w =
      ∑ j ∈ J, ∑ i ∈ X, if j ∈ R ∧ i ∈ Q j then V i j else 0 := by
    unfold boundedDividedResidueFrom
    have outer : R ⊆ J := filter_subset _ _
    have inner (j : κ) : Q j ⊆ X := filter_subset _ _
    have point (j : κ) (hj : j ∈ R) :
        w j*boundedOuterLeftRow n (v j) (b j) (c j) (smallModulusProductLower n (v j)) (smallModulusProductUpper n (v j)) = ∑ i ∈ Q j, V i j := by
      have data := mem_filter.mp hj
      have r := mem_Icc.mp (steps j data.1)
      have e := Nat.mul_le_mul_left (v j) (ends j data.1)
      have lo : leftMediumCap n ≤ smallModulusProductLower n (v j) :=
        (le_max_left _ _).trans (le_max_left _ _)
      have up := (small_modulus_product_range (v := v j) (r.1.trans r.2)).1
      rw [bounded_outer_left_row_eq_selected r.1 r.2 data.2.2.2.2 (e.trans (Nat.mul_div_le n (v j))) lo up,mul_sum]
      refine sum_congr rfl fun i _ => ?_
      unfold V u
      ring
    calc
      _ = ∑ j ∈ R, ∑ i ∈ Q j, V i j := sum_congr rfl point
      _ = _ := by
        rw [expand_outer_index outer]
        refine sum_congr rfl fun j _ => ?_
        by_cases hj : j ∈ R
        · rw [ite_eq_left hj,expand_outer_index (inner j)]
          refine sum_congr rfl fun i _ => ?_
          by_cases h : i ∈ Q j
          · rw [ite_eq_left h,ite_eq_left (And.intro hj h)]
          · rw [ite_eq_right h,ite_eq_right (fun hx : j ∈ R ∧ i ∈ Q j => h hx.2)]
        · simp [hj]
  have rhs : boundedOuterLeftKeptFrom smallModulusProductGate n J v b c w =
      ∑ i ∈ X, ∑ j ∈ J,
        if (u i ≤ expandedWideStepCap n ∧ v j ≤ expandedWideStepCap n) ∧
          boundedOuterLeftKeptGate smallModulusProductGate n (u i) (v j) then V i j else 0 := by
    unfold boundedOuterLeftKeptFrom expandedWaveItems
    simp_rw [sum_filter]
    refine sum_congr rfl fun i _ => ?_
    by_cases hu : u i ≤ expandedWideStepCap n
    · have h' : leftBilinearStep i ≤ expandedWideStepCap n := hu
      rw [ite_eq_left h']
      refine sum_congr rfl fun j _ => ?_
      by_cases hv : v j ≤ expandedWideStepCap n <;> simp [hu,hv,V,u]
    · simp [hu,V,u]
  rw [lhs,rhs,sum_comm (s := J) (t := X)]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  let good := (u i ≤ expandedWideStepCap n ∧ v j ≤ expandedWideStepCap n) ∧ boundedOuterLeftKeptGate smallModulusProductGate n (u i) (v j)
  have v0 := (mem_Icc.mp (steps j hj)).1
  have eq := small_modulus_product_membership (v := v) (b := b) (c := c) hi hj v0
  by_cases h : good
  · by_cases endpoint : b j < c j
    · by_cases compatible : (u i).gcd (v j) ∣ n
      · have selected : j ∈ R ∧ i ∈ Q j := eq.mpr ⟨h.1,h.2,endpoint,compatible⟩
        rw [ite_eq_left selected,ite_eq_left h]
      · have bad : ¬(j ∈ R ∧ i ∈ Q j) := fun z => compatible (eq.mp z).2.2.2
        rw [ite_eq_right bad,ite_eq_left h]
        simp [V,pairResidueError,compatible]
    · have bad : ¬(j ∈ R ∧ i ∈ Q j) := fun z => endpoint (eq.mp z).2.2.1
      rw [ite_eq_right bad,ite_eq_left h]
      have up := (mem_Icc.mp (bilateral_left_step_range hi)).1
      have z := pair_residue_error_eq_zero_of_right_interval_empty (n := n) (l := 0)
        (r := n/u i) up v0 (not_lt.mp endpoint)
      change pairResidueError n (u i) (v j) 0 (n/u i) (b j) (c j) = 0 at z
      simp [V,z]
  · have bad : ¬(j ∈ R ∧ i ∈ Q j) := fun z => h ⟨(eq.mp z).1,(eq.mp z).2.1⟩
    rw [ite_eq_right bad,ite_eq_right h]

theorem small_modulus_product_kept_from_saving {κ : Type} (J : ℕ → Finset κ)
    (v : κ → ℕ) (b c : ℕ → κ → ℕ) (w : ℕ → κ → ℂ)
    (steps : ∀ n, ∀ j ∈ J n, v j ∈ Icc 1 n)
    (ends : ∀ n, ∀ j ∈ J n, c n j ≤ n/v j)
    (weights : ∀ n, ∀ {T : ℝ}, 1 ≤ T → (∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) →
      ∀ m ∈ Icc 1 n, (∑ j ∈ (J n).filter (fun j => v j=m), ‖w n j‖) ≤ T^3*DyadicMixedB4EnergyTail.logBudget n) :
    saving (fun n => boundedOuterLeftKeptFrom smallModulusProductGate n (J n) v (b n) (c n) (w n)) := by
  intro ε he
  have data (n : ℕ) (j : κ) (hj : j ∈ smallModulusProductRows n (J n) v (b n) (c n)) :
      (n : ℝ)^(171/512 : ℝ) ≤ (v j : ℝ) ∧
        (v j : ℝ) ≤ (n : ℝ)^(515/1024 : ℝ) ∧ (v j).gcd n ≤ targetDivisorCap n := by
    obtain ⟨_,lo,up,char,_⟩ := mem_filter.mp hj
    have cap : (v j : ℝ) ≤ (expandedHighModulusCap n : ℝ) := by exact_mod_cast up
    exact ⟨lo,cap.trans (Nat.floor_le (by positivity)),char⟩
  obtain ⟨N,h⟩ := bounded_divided_residue_saving smallModulusProductLower smallModulusProductUpper J
    (fun n => smallModulusProductRows n (J n) v (b n) (c n)) v b c w
    (fun _ => filter_subset _ _) data (fun _ n0 _ => small_modulus_product_range n0)
    steps weights ε he
  refine ⟨N, fun n hn even => ?_⟩
  have eq := small_modulus_product_residue_eq_kept_from (J n) v (b n) (c n) (w n) (steps n) (ends n)
  simpa only [eq] using h n hn even

theorem small_modulus_product_base_from_saving {κ : Type} (J : ℕ → Finset κ)
    (v : κ → ℕ) (b c : ℕ → κ → ℕ) (w : ℕ → κ → ℂ)
    (steps : ∀ n, ∀ j ∈ J n, v j ∈ Icc 1 n)
    (ends : ∀ n, ∀ j ∈ J n, c n j ≤ n/v j)
    (weights : ∀ n, ∀ {T : ℝ}, 1 ≤ T → (∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) →
      ∀ m ∈ Icc 1 n, (∑ j ∈ (J n).filter (fun j => v j=m), ‖w n j‖) ≤ T^3*DyadicMixedB4EnergyTail.logBudget n) :
    saving (fun n => boundedOuterLeftBaseFrom smallModulusProductGate n (J n) v (b n) (c n) (w n)) := by
  intro ε he
  obtain ⟨N,h⟩ := small_modulus_product_kept_from_saving J v b c w steps ends weights (ε/2) (by positivity)
  obtain ⟨M,hm⟩ := bounded_outer_left_cut_saving smallModulusProductGate J v b c w steps weights
    (ε/2) (by positivity)
  refine ⟨max N M,fun n hn even => ?_⟩
  dsimp only
  rw [bounded_outer_left_base_eq_partition]
  exact (norm_add_le _ _).trans (by linarith only [h n (by omega) even,hm n (by omega) even])

end

end B13BoundedStepProductSavingProof

end

/- Raw expanded reduction -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open scoped Classical Finset

noncomputable section

def rawWavePairSum (n : ℕ) {κ : Type} (I : Finset (ℕ × ℕ)) (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) (gate : ℕ → ℕ → Prop)
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J,
    let u := leftBilinearStep i
    let m := v j
    if gate u m then leftBilinearWeight n i*w j*f u m 0 (n/u) (p j) (s j) else 0

def rawExpandedWavePairSum (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  rawWavePairSum n (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep)
    (expandedWaveItems n J v) v p s w (prefixStepGate n) f

def rawExpandedResidue (n : ℕ) : ℂ :=
  rawExpandedWavePairSum n ((rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n))
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight
    (fun u v l r a b => (pairResidueError n u v l r a b : ℂ)) +
  rawExpandedWavePairSum n (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)
    (fun u v l r a b => (pairResidueError n u v l r a b : ℂ))

end

end B13BoundedStepProductSavingProof

end

/- Swapped ratio at step -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

set_option maxHeartbeats 1800000 in
theorem norm_swapped_ratio_at_step_le {n g e k mLo : ℕ} {row : ℕ × ℕ}
    (hrow : row ∈ swappedHighRows n)
    (gpos : 0 < g) (gn : g ∣ n) (gm : g ∣ leftBilinearStep row) (gSmall : g ≤ thinHighGcdCap n)
    (e0 : 0 < e) (eg : e ∣ g) (hk : k ∈ Icc 128 10581) (ns : 1 < n)
    (lower : thinHighProductCap n/leftBilinearStep row ≤ mLo)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T)
    (α : ℕ → ℂ) (β : ℤ → ℂ) (baseLo baseHi : ℕ → ℤ)
    (aw : ∀ a ∈ swappedHighFactors n (leftBilinearStep row) g e k, ‖α a‖ ≤ T*logBudget n)
    (bw : ∀ j ∈ intIntervalModUnits (leftBilinearStep row/g) 0
      (swappedHighCofactorCap n (leftBilinearStep row) g e k), ‖β j‖ ≤ T) :
    let m := leftBilinearStep row
    let v := m/g
    let l := mLo/g
    let r := swappedHighStepUpper n m/g
    let I := swappedHighFactors n m g e k
    let J := intIntervalModUnits v 0 (swappedHighCofactorCap n m g e k)
    let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (baseLo a)
    let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (baseHi a)
    let num := n/g-m/g
    ‖gatedBilinearSum I J α β lo hi
        (fun a j => centeredIntIntervalResidue v 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
          (((n/g : ℕ) : ZMod v)*((a : ZMod v)*(j : ZMod v))⁻¹))‖ ≤
      592*(n : ℝ)^(32767/32768 : ℝ)*T^3*logBudget n^3/(leftBilinearStep row : ℝ) := by
  dsimp only
  let m := leftBilinearStep row
  let v := m/g
  let N := (n : ℝ)
  let M := (m : ℝ)
  let V := (v : ℝ)
  let G := (g : ℝ)
  let E := (e : ℝ)
  let y := (k : ℝ)/32768
  let x := y-1/4096
  let A := swappedHighFactorFloor n (k+1)/e
  let aLo := swappedHighFactorLower n k
  let S := swappedHighCofactorCap n m g e k
  let I := swappedHighFactors n m g e k
  let mHi := swappedHighStepUpper n m
  let l := mLo/g
  let r := mHi/g
  let L := logBudget n
  let num := n/g-m/g
  have numN : num ≤ n/g := Nat.sub_le _ _
  have right : row ∈ bilateralLeftWaveItems n := (mem_filter.mp hrow).1
  obtain ⟨sq,origLo,charTop⟩ := (mem_filter.mp hrow).2
  have step := mem_Icc.mp (bilateral_left_step_range right)
  have m0 : 0 < m := step.1
  have mN : m ≤ n := step.2
  have v0 : 0 < v := Nat.div_pos (Nat.le_of_dvd m0 gm) gpos
  let _ : NeZero v := ⟨v0.ne'⟩
  have vprod : v*g=m := Nat.div_mul_cancel gm
  have npNat : 0 < n := zero_lt_one.trans ns
  have nr : 1 < N := show (1 : ℝ) < (n : ℝ) from by exact_mod_cast ns
  have np : 0 < N := zero_lt_one.trans nr
  have gp : 0 < G := show (0 : ℝ) < (g : ℝ) from by exact_mod_cast gpos
  have G1 : 1 ≤ G := show (1 : ℝ) ≤ (g : ℝ) from by exact_mod_cast gpos
  have vN : v ≤ n := (by simpa only [mul_one] using Nat.mul_le_mul_left v (show 1 ≤ g from gpos) : v ≤ v*g).trans
    (by rw [vprod]; exact mN)
  have vEq : V*G=M := by
    change (v : ℝ)*(g : ℝ) = (m : ℝ)
    exact_mod_cast vprod
  have origHi : M ≤ N^(1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.le_sqrt (by positivity) np.le).mpr
    change (m : ℝ)^2 ≤ (n : ℝ)
    exact_mod_cast sq
  have castGcd : (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ N^(1/2048 : ℝ) := by
    have vd : v ∣ m := ⟨g,vprod.symm⟩
    have nd : n/g ∣ n := ⟨g,(Nat.div_mul_cancel gn).symm⟩
    have d : v.gcd (n/g) ∣ m.gcd n := Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans vd) ((Nat.gcd_dvd_right _ _).trans nd)
    have relation := (gcd_val_nat_cast_le_gcd (m := v) (n/g)).trans
      ((Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ npNat) d).trans charTop)
    exact (show (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ (thinHighLeftDivisorCap n : ℝ) by
      exact_mod_cast relation).trans (Nat.floor_le (by positivity))
  have vHi : V ≤ N^(1/2 : ℝ) := by
    have h : V ≤ M := by
      rw [← vEq]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left G1 (by positivity : 0 ≤ V)
    exact h.trans origHi
  have gReal : G ≤ (thinHighGcdCap n : ℝ) := by
    change (g : ℝ) ≤ (thinHighGcdCap n : ℝ)
    exact_mod_cast gSmall
  have gCap : G ≤ N^(1/4096 : ℝ) :=
    gReal.trans (Nat.floor_le (Real.rpow_nonneg np.le _))
  have egNat : e ≤ g := Nat.le_of_dvd gpos eg
  have egReal : E ≤ G := by
    change (e : ℝ) ≤ (g : ℝ)
    exact_mod_cast egNat
  have eCap : E ≤ N^(1/4096 : ℝ) := egReal.trans gCap
  have vLo : N^(1/3 : ℝ) < V := by
    apply (mul_lt_mul_iff_left₀ gp).mp
    calc
      _ ≤ N^(1/3 : ℝ)*N^(1/4096 : ℝ) := mul_le_mul_of_nonneg_left gCap (by positivity)
      _ < N^(87/256 : ℝ) := by rw [← Real.rpow_add np]; exact Real.rpow_lt_rpow_of_exponent_lt nr (by norm_num)
      _ ≤ M := origLo
      _ = _ := vEq.symm
  obtain ⟨kminNat, kmaxNat⟩ : 128 ≤ k ∧ k ≤ 10581 := mem_Icc.mp hk
  have kmin : (128 : ℝ) ≤ k := by exact_mod_cast kminNat
  have kmax : (k : ℝ) ≤ 10581 := by exact_mod_cast kmaxNat
  have xLo : 15/4096 ≤ x := by unfold x y; linarith only [kmin]
  have xHi : x ≤ 1/3 := by unfold x y; linarith only [kmax]
  have aFormula : swappedHighFactorFloor n (k+1) = ⌊N^(x+9/32768)⌋₊ := by
    unfold swappedHighFactorFloor N x y
    rw [Nat.cast_add,Nat.cast_one,add_div]
    congr 2
    ring
  have aCap : (A : ℝ) ≤ N^(x+9/32768) :=
    (by exact_mod_cast Nat.div_le_self (swappedHighFactorFloor n (k+1)) e :
      (A : ℝ) ≤ (swappedHighFactorFloor n (k+1) : ℝ)).trans (by rw [aFormula]; exact Nat.floor_le (by positivity))
  have A1 : 0 < A := by
    change 1 ≤ swappedHighFactorFloor n (k+1)/e
    apply (Nat.le_div_iff_mul_le e0).mpr
    rw [one_mul,aFormula]
    exact Nat.le_floor (eCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by linarith only [xLo])))
  have aQ : (A : ℝ) ≤ N^(1/3 : ℝ) :=
    aCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by unfold x y; linarith only [kmax]))
  have Av : A < v := by
    have h := aQ.trans_lt vLo
    change (A : ℝ) < (v : ℝ) at h
    exact_mod_cast h
  have Icap : I ⊆ Icc 1 A := by
    intro a ha
    have h := mem_Ioc.mp (mem_filter.mp ha).1
    exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt h.1,h.2.trans (Nat.div_le_div_right (min_le_right (swappedHighFactorCap n) _))⟩
  have copI (a : ℕ) (ha : a ∈ I) : a.Coprime v := (mem_filter.mp ha).2.2
  have rN : mHi ≤ n := (min_le_left _ _).trans (extended_wide_step_le npNat)
  have rG : r*g ≤ mHi := Nat.div_mul_le_self mHi g
  have sR : S ≤ r := Nat.div_le_self _ _
  have rp : r*v*g^2 ≤ 2*n := calc
    _ = (r*g)*(v*g) := by ring
    _ = (r*g)*m := by rw [vprod]
    _ ≤ mHi*m := Nat.mul_le_mul_right m rG
    _ ≤ (2*n/m)*m := Nat.mul_le_mul_right m (min_le_right _ _)
    _ ≤ _ := Nat.div_mul_le_self _ _
  have rCap : (r : ℝ)*V*G^2 ≤ 2*N := by
    change (r : ℝ)*(v : ℝ)*(g : ℝ)^2 ≤ 2*(n : ℝ)
    exact_mod_cast rp
  have cofactorFloor : N^x ≤ (aLo/e : ℕ)+1 := by
    have more : aLo < (aLo/e+1)*e := (Nat.div_lt_iff_lt_mul e0).mp (Nat.lt_succ_self _)
    have rank : (swappedHighFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*E := by
      have le : swappedHighFactorFloor n k+1 ≤ (aLo/e+1)*e :=
        Nat.succ_le_of_lt ((le_max_right _ _).trans_lt more)
      change (swappedHighFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*(e : ℝ)
      exact_mod_cast le
    have ground : N^y ≤ (((aLo/e : ℕ) : ℝ)+1)*E := (Nat.lt_floor_add_one (N^y)).le.trans rank
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (1/4096 : ℝ))).mp
    calc
      _ = N^y := by rw [← Real.rpow_add np]; unfold x; simp
      _ ≤ (((aLo/e : ℕ) : ℝ)+1)*E := ground
      _ ≤ _ := mul_le_mul_of_nonneg_left eCap (by positivity)
  have sCap : (S : ℝ)*V*G^2 ≤ 2*N^(1-x) := by
    have cut : S*(aLo/e+1) ≤ r := Nat.div_mul_le_self r (aLo/e+1)
    have scaled : (S : ℝ)*(((aLo/e : ℕ) : ℝ)+1) ≤ (r : ℝ) := by exact_mod_cast cut
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np x)).mp
    calc
      _ ≤ ((S : ℝ)*V*G^2)*(((aLo/e : ℕ) : ℝ)+1) :=
        mul_le_mul_of_nonneg_left cofactorFloor (by positivity)
      _ = ((S : ℝ)*(((aLo/e : ℕ) : ℝ)+1))*V*G^2 := by ring
      _ ≤ (r : ℝ)*V*G^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right scaled (by positivity)) (by positivity)
      _ ≤ 2*N := rCap
      _ = (2*N^(1-x))*N^x := by rw [mul_assoc,← Real.rpow_add np,sub_add_cancel,Real.rpow_one]
  have endCap : num/(l+1) ≤ ⌊V*G*N^(1/8192 : ℝ)⌋₊ := by
    have endOrig := swapped_high_endpoint_cap_of_size npNat m0 lower (le_rfl : n ≤ n)
    have s : mLo+1 ≤ (l+1)*g := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul gpos).mp (Nat.lt_succ_self (mLo/g)))
    rw [vEq]
    calc
      _ ≤ (n/g)/(l+1) := Nat.div_le_div_right numN
      _ = n/((l+1)*g) := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm g (l+1)]
      _ ≤ n/(mLo+1) := Nat.div_le_div_left s (Nat.succ_pos _)
      _ ≤ _ := endOrig
  have divN (z : ℕ) (h : z ≤ n) : (z.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ ns.le (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors z (h.trans nn)
  have divV (z : ℕ) (h : z ≤ 4*v^3) : (z.divisors.card : ℝ) ≤ T :=
    divisors z (h.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left vN 3)))
  have divR (z : ℕ) (h : z ≤ r) : (z.divisors.card : ℝ) ≤ T :=
    divN z (h.trans ((Nat.div_le_self _ _).trans rN))
  have logBound : 1+Real.log V ≤ L := by
    have pv : 0 < V := show (0 : ℝ) < (v : ℝ) from by exact_mod_cast v0
    have up : V ≤ (n : ℝ)+2 := by
      change (v : ℝ) ≤ (n : ℝ)+2
      exact_mod_cast vN.trans (by omega : n≤n+2)
    unfold L logBudget
    linarith only [Real.log_le_log pv up]
  have first := norm_swapped_high_ratio_hyperbola_le (m := v) (c := ((n/g : ℕ) : ZMod v)) (g := g)
    castGcd nr.le G1 T1 (one_le_logBudget n) vHi vLo.le gCap xLo xHi logBound aCap sCap rCap endCap
    A1 Av I Icap copI α β baseLo baseHi aw bw divV divR
  have eq : (v : ℝ)*(g : ℝ) = (m : ℝ) := vEq
  rw [eq] at first
  exact first

end

end B13BoundedStepProductSavingProof

end

/- Swapped low window -/
section

namespace B13BoundedStepProductSavingProof

open Finset ArithmeticFunction DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4MoebiusGauss
open scoped Classical

noncomputable section

def swappedLowStepLower (n m : ℕ) : ℕ :=
  max (expandedHighModulusCap n) (max (maximumStep n^2/m) (thinHighProductCap n/m))

def swappedLowShortWeight (g a : ℕ) : ℂ :=
  -(ArithmeticFunction.moebius (g*a) : ℂ)

def swappedLowPrimeWeight (n : ℕ) (j : ℤ) : ℂ :=
  if j.toNat.Prime ∧ ¬j.toNat ∣ n ∧ j.toNat ≤ n then (vonMangoldt j.toNat : ℂ) else 0

def swappedLowWindow (n : ℕ) (row : ℕ × ℕ) (g k : ℕ) : ℂ :=
  let m := leftBilinearStep row
  let v := m/g
  let l := swappedLowStepLower n m/g
  let r := swappedHighStepUpper n m/g
  let I := swappedHighFactors n m g g k
  let J := intIntervalModUnits v 0 (swappedHighCofactorCap n m g g k)
  let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (cutoffU n : ℤ)
  let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (min n (rightLargeCofactorCut n) : ℕ)
  let num := n/g-m/g
  gatedBilinearSum I J (swappedLowShortWeight g) (swappedLowPrimeWeight n) lo hi
    (fun a j => centeredIntIntervalResidue v 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
      (((n/g : ℕ) : ZMod v)*((a : ZMod v)*(j : ZMod v))⁻¹))

theorem norm_swapped_low_short_weight_le_one (g a : ℕ) : ‖swappedLowShortWeight g a‖ ≤ 1 := by
  simpa only [swappedLowShortWeight, norm_neg, moebiusComplex] using norm_moebiusComplex_le_one (g*a)

theorem norm_swapped_low_prime_weight_le_log (n : ℕ) (j : ℤ) :
    ‖swappedLowPrimeWeight n j‖ ≤ logBudget n := by
  unfold swappedLowPrimeWeight
  split_ifs with hp
  · rw [Complex.norm_real, Real.norm_of_nonneg (vonMangoldt_nonneg)]
    have p0 : (0 : ℝ) < j.toNat := by exact_mod_cast hp.1.pos
    have pn : (j.toNat : ℝ) ≤ (n : ℝ)+2 := by exact_mod_cast hp.2.2.trans (by omega : n ≤ n+2)
    refine vonMangoldt_le_log.trans ?_
    unfold logBudget
    linarith only [Real.log_le_log p0 pn]
  · rw [norm_zero]
    exact zero_le_one.trans (one_le_logBudget n)

theorem norm_swapped_low_window_le {n g k : ℕ} {row : ℕ × ℕ}
    (hrow : row ∈ swappedHighRows n)
    (g0 : 0 < g) (gn : g ∣ n) (gm : g ∣ leftBilinearStep row) (gSmall : g ≤ thinHighGcdCap n)
    (hk : k ∈ Icc 128 10581) (ns : 1 < n)
    {T : ℝ} (T1 : 1 ≤ T) (TL : logBudget n ≤ T)
    (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖swappedLowWindow n row g k‖ ≤
      592*(n : ℝ)^(32767/32768 : ℝ)*T^3*logBudget n^3/(leftBilinearStep row : ℝ) := by
  have low : thinHighProductCap n/leftBilinearStep row ≤ swappedLowStepLower n (leftBilinearStep row) :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact norm_swapped_ratio_at_step_le hrow g0 gn gm gSmall g0 (dvd_refl g) hk ns low T1 divisors
    (swappedLowShortWeight g) (swappedLowPrimeWeight n)
    (fun _ => (cutoffU n : ℤ)) (fun _ => (min n (rightLargeCofactorCut n) : ℕ))
    (fun a _ => (norm_swapped_low_short_weight_le_one g a).trans
      (one_le_mul_of_one_le_of_one_le T1 (one_le_logBudget n)))
    (fun j _ => (norm_swapped_low_prime_weight_le_log n j).trans TL)

end

end B13BoundedStepProductSavingProof

end

/- Swapped low saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def swappedLowRow (n : ℕ) (row : ℕ × ℕ) : ℂ :=
  ∑ g ∈ swappedHighDivisors n (leftBilinearStep row), ∑ k ∈ Icc 128 2047, swappedLowWindow n row g k

def swappedLowResidueSlice (n : ℕ) : ℂ :=
  ∑ row ∈ swappedHighRows n, leftBilinearWeight n row*swappedLowRow n row

theorem norm_swapped_low_row_le {n : ℕ} {j : (ℕ × ℕ)}
    (hj : j ∈ swappedHighRows n) (ns : 1 < n)
    {T : ℝ} (T1 : 1 ≤ T) (TL : logBudget n ≤ T)
    (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T)
    (divN : ∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) :
    ‖swappedLowRow n j‖ ≤
      (1920*(592*(n : ℝ)^(32767/32768 : ℝ)*T^3*logBudget n^3)*T)*(1/(leftBilinearStep j : ℝ)) := by
  let B := 592*(n : ℝ)^(32767/32768 : ℝ)*T^3*logBudget n^3
  let M := (leftBilinearStep j : ℝ)
  let V := 1920*B/M
  let G := swappedHighDivisors n (leftBilinearStep j)
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have V0 : 0 ≤ V := by unfold V M B; positivity
  have natCard : G.card ≤ n.divisors.card := card_le_card (filter_subset _ n.divisors)
  have nG : (G.card : ℝ) ≤ T := (show (G.card : ℝ) ≤ (n.divisors.card : ℝ) by exact_mod_cast natCard).trans (divN n le_rfl)
  have per (g : ℕ) (hg : g ∈ G) : ‖∑ k ∈ Icc 128 2047, swappedLowWindow n j g k‖ ≤ V := by
    obtain ⟨data,gS,_,gq⟩ := mem_filter.mp hg
    have gn := (Nat.mem_divisors.mp data).1
    have g0 := Nat.pos_of_dvd_of_pos gn (zero_lt_one.trans ns)
    calc
      _ ≤ ∑ k ∈ Icc 128 2047, ‖swappedLowWindow n j g k‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Icc 128 2047, B/M := sum_le_sum fun k hk =>
        norm_swapped_low_window_le hj g0 gn gq gS (Icc_subset_Icc_right (by decide) hk) ns T1 TL divisors
      _ = V := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,V]; norm_num; ring
  change ‖∑ g ∈ G, ∑ k ∈ Icc 128 2047, swappedLowWindow n j g k‖ ≤ (1920*B*T)*(1/M)
  calc
    _ ≤ ∑ g ∈ G, ‖∑ k ∈ Icc 128 2047, swappedLowWindow n j g k‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ G, V := sum_le_sum per
    _ = (G.card : ℝ)*V := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ T*V := mul_le_mul_of_nonneg_right nG V0
    _ = _ := by unfold V M; ring

private theorem norm_swapped_low_slice_le {n : ℕ} (nBig : 2 ≤ n)
    {T : ℝ} (T1 : 1 ≤ T) (TL : logBudget n ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖swappedLowResidueSlice n‖ ≤ 1136640*(n : ℝ)^(32767/32768 : ℝ)*T^7*logBudget n^5 := by
  let L := logBudget n
  let C := n
  let B := 592*(n : ℝ)^(32767/32768 : ℝ)*T^3*L^3
  let W := T^3*L
  let J := swappedHighRows n
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have B0 : 0 ≤ B := by unfold B; positivity
  have W0 : 0 ≤ W := by unfold W; positivity
  have n1 : 1 ≤ n := (show 1 ≤ 2 by decide).trans nBig
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have nPos : (0 : ℝ) < n := zero_lt_one.trans_le nR
  have C1 : 1 ≤ C := n1
  have Cn : (C : ℝ) ≤ (n : ℝ) := le_rfl
  have Cnat : C ≤ n := by exact_mod_cast Cn
  have divN (u : ℕ) (h : u ≤ n) : (u.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors u (h.trans nn)
  have ns : 1 < n := nBig
  have massH : (∑ m ∈ Icc 1 C, 1/(m : ℝ)) ≤ L := calc
    _ = (harmonic C : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    _ ≤ 1+Real.log C := by exact_mod_cast harmonic_le_one_add_log C
    _ ≤ L := by
      unfold L logBudget
      exact add_le_add_right (Real.log_le_log (by exact_mod_cast C1)
        (Cn.trans (by linarith : (n : ℝ) ≤ (n : ℝ)+2))) _
  have step (j : (ℕ × ℕ)) (hj : j ∈ J) : leftBilinearStep j ∈ Icc 1 C :=
    bilateral_left_step_range (mem_filter.mp hj).1
  have weighted : (∑ j ∈ J, ‖leftBilinearWeight n j‖*(1/(leftBilinearStep j : ℝ))) ≤ W*L := by
    refine (sum_norm_mul_le_of_step_mass J leftBilinearStep (leftBilinearWeight n) (fun m => 1/(m : ℝ))
      step (fun _ _ => by positivity) ?_).trans (mul_le_mul_of_nonneg_left massH W0)
    intro m hm
    have h : m ∈ Icc 1 n := mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans Cnat⟩
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_left_step_mass (zero_lt_one.trans_le n1) T0 divN m h)
  have each (j : (ℕ × ℕ)) (hj : j ∈ J) :
      ‖swappedLowRow n j‖ ≤ (1920*B*T)*(1/(leftBilinearStep j : ℝ)) := by
    exact norm_swapped_low_row_le hj ns T1 TL divisors divN
  unfold swappedLowResidueSlice
  change ‖∑ j ∈ J, leftBilinearWeight n j*swappedLowRow n j‖ ≤ _
  calc
    _ ≤ ∑ j ∈ J, ‖leftBilinearWeight n j*swappedLowRow n j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ‖leftBilinearWeight n j‖*((1920*B*T)*(1/(leftBilinearStep j : ℝ))) := by
      refine sum_le_sum fun j hj => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (each j hj) (norm_nonneg _)
    _ = (1920*B*T)*(∑ j ∈ J, ‖leftBilinearWeight n j‖*(1/(leftBilinearStep j : ℝ))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (1920*B*T)*(W*L) := mul_le_mul_of_nonneg_left weighted (by positivity)
    _ = _ := by unfold B W L; ring

theorem swapped_low_residue_saving : saving swappedLowResidueSlice := by
  intro ε he
  obtain ⟨D,D1,db⟩ := divisor_envelope_at_power 2097152 (by decide)
  let C := 1136640*(4*D)^7
  have hlimit : Tendsto (fun n : ℕ => (n : ℝ)^(-(38/2097152) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 38/2097152)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(38/2097152) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlimit
  have bound : ∀ᶠ n : ℕ in atTop, ‖swappedLowResidueSlice n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_log_budget_le_power (1/2097152) (by norm_num),
      hl.eventually_lt_const he] with n nBig logb final
    have hn : 1 ≤ n := (show 1 ≤ (2 : ℕ) by decide).trans nBig
    have nr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have np : (0 : ℝ) < n := zero_lt_one.trans_le nr
    have D0 := zero_le_one.trans D1
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/2097152 : ℝ)
    let T := (4*D)*X^3
    have X1 : 1 ≤ X := Real.one_le_rpow nr (by norm_num)
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) D1) (one_le_pow₀ X1)
    have TL : logBudget n ≤ T := logb.trans (by
      have xx : X ≤ X^3 := by simpa only [pow_one] using pow_le_pow_right₀ X1 (show 1 ≤ 3 by decide)
      exact xx.trans (le_mul_of_one_le_left (by positivity) (by nlinarith only [D1])))
    have cp : (4 : ℝ)^(1/2097152 : ℝ) ≤ 4 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have divs (m : ℕ) (hm : m ≤ 4*n^3) : (m.divisors.card : ℝ) ≤ T := by
      calc
        _ ≤ D*((4*n^3 : ℕ) : ℝ)^(1/(2097152 : ℕ) : ℝ) := db (4*n^3) m hm
        _ = D*((4 : ℝ)^(1/2097152 : ℝ)*X^3) := by
          push_cast
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul np.le]
          unfold X
          rw [← Real.rpow_mul_natCast np.le]
          norm_num
        _ ≤ D*(4*X^3) := by gcongr
        _ = _ := by unfold T; ring
    have ex : (n : ℝ)^(32767/32768 : ℝ)*X^26 = (n : ℝ)^(-(38/2097152) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast np.le, ← Real.rpow_add np, ← Real.rpow_add_one np.ne']
      congr 1
      norm_num
    calc
      _ ≤ 1136640*(n : ℝ)^(32767/32768 : ℝ)*T^7*logBudget n^5 := norm_swapped_low_slice_le nBig T1 TL divs
      _ ≤ 1136640*(n : ℝ)^(32767/32768 : ℝ)*T^7*X^5 := by gcongr
      _ = C*((n : ℝ)^(32767/32768 : ℝ)*X^26) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(38/2097152) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right final.le np.le
  obtain ⟨N,h⟩ := eventually_atTop.mp bound
  exact ⟨N,fun n hn _ => h n hn⟩

end

end B13BoundedStepProductSavingProof

end

/- Swapped low window selection -/
section

namespace B13BoundedStepProductSavingProof

open Finset ArithmeticFunction DyadicMixedB4Scale
open scoped Classical

noncomputable section

set_option maxHeartbeats 2200000 in
def swappedLowSelection (n : ℕ) (row : ℕ × ℕ) (g k : ℕ) : Finset RightLowWaveIndex :=
  let m := leftBilinearStep row
  (rightLowWaveItems n).filter fun j =>
    let w := rightLowWaveStep j
    j.1.Prime ∧ ¬j.1 ∣ n ∧ j.2 ∈ swappedHighFactorBlock n k ∧
      w.gcd m=g ∧ swappedLowStepLower n m < w ∧ w ≤ swappedHighStepUpper n m

set_option maxHeartbeats 2200000 in
def swappedLowResidueTerm (n m : ℕ) (j : RightLowWaveIndex) : ℂ :=
  rightLowWaveWeight j *
    (pairResidueError n (rightLowWaveStep j) m 0 (rightLowWaveUpper n j) 0 (n/m) : ℂ)

set_option maxHeartbeats 2200000 in
theorem right_low_common_gcd_dvd_short_factor {n m : ℕ} {j : RightLowWaveIndex}
    (hp : j.1.Prime) (hpn : ¬j.1 ∣ n) (hd : (rightLowWaveStep j).gcd m ∣ n) :
    (rightLowWaveStep j).gcd m ∣ j.2 :=
  (Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hd).trans (right_low_target_gcd_dvd_short_factor hp hpn)

set_option maxHeartbeats 2200000 in
theorem swapped_low_step_above_left {n m w : ℕ} (m0 : 0 < m) (msq : m^2 ≤ n)
    (step : swappedLowStepLower n m < w) : m < w :=
  ((square_le_implies_step_le_expanded_high_cap m0 msq).trans (le_max_left _ _)).trans_lt step

set_option maxHeartbeats 2200000 in
private theorem root_low_step_before_case {n w : ℕ} (n0 : 0 < n) (hw : expandedHighModulusCap n < w) :
    n ≤ w^2 := by
  have nr : (1 : ℝ) ≤ n := by exact_mod_cast n0
  have p : (n : ℝ)^(1/2 : ℝ) ≤ (w : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le nr (by norm_num : (1/2 : ℝ) ≤ 515/1024)).trans
      ((Nat.lt_floor_add_one ((n : ℝ)^(515/1024 : ℝ))).le.trans (by
        change (expandedHighModulusCap n : ℝ)+1 ≤ (w : ℝ)
        exact_mod_cast Nat.succ_le_of_lt hw))
  rw [← Real.sqrt_eq_rpow] at p
  exact_mod_cast (Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (w : ℝ))).mp p

set_option maxHeartbeats 2200000 in
theorem swapped_low_window_eq_selected {n g k : ℕ} {row : ℕ × ℕ}
    (hrow : row ∈ swappedHighRows n)
    (g0 : 0 < g) (gn : g ∣ n) (gm : g ∣ leftBilinearStep row)
    (kc : swappedHighFactorFloor n (k+1) ≤ cutoffU n) :
    swappedLowWindow n row g k = ∑ j ∈ swappedLowSelection n row g k,
      swappedLowResidueTerm n (leftBilinearStep row) j := by
  let m := leftBilinearStep row
  let v := m/g
  let l₀ := swappedLowStepLower n m
  let r₀ := swappedHighStepUpper n m
  let l := l₀/g
  let r := r₀/g
  let aLo := swappedHighFactorLower n k
  let aHi := min (swappedHighFactorCap n) (swappedHighFactorFloor n (k+1))
  let S := swappedHighCofactorCap n m g g k
  let I := swappedHighFactors n m g g k
  let J := intIntervalModUnits v 0 S
  let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (cutoffU n : ℤ)
  let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (min n (rightLargeCofactorCut n) : ℕ)
  let gate (a : ℕ) (j : ℤ) : Prop := lo a < j ∧ j ≤ hi a
  let admissible (j : ℤ) : Prop := j.toNat.Prime ∧ ¬j.toNat ∣ n
  let P := (J ×ˢ I).filter fun t => gate t.2 t.1 ∧ admissible t.1
  let f (t : ℤ × ℕ) : RightLowWaveIndex := ⟨t.1.toNat,g*t.2⟩
  let F (a : ℕ) (j : ℤ) := centeredIntIntervalResidue v 0
    (((n/g-m/g : ℕ) : ℤ)/((a*j.toNat : ℕ) : ℤ)) (((n/g : ℕ) : ZMod v)*((a : ZMod v)*(j : ZMod v))⁻¹)
  let W (t : ℤ × ℕ) := swappedLowShortWeight g t.2*(vonMangoldt t.1.toNat : ℂ)*F t.2 t.1
  have data := mem_filter.mp hrow
  have steps := mem_Icc.mp (bilateral_left_step_range data.1)
  have m0 : 0 < m := steps.1
  have mN : m ≤ n := steps.2
  have n0 := m0.trans_le mN
  have mSquare : m^2 ≤ n := data.2.1
  have gV : g*v=m := Nat.mul_div_cancel' gm
  have rN : r₀ ≤ n := (min_le_left _ _).trans (extended_wide_step_le n0)
  have aBounds (a : ℕ) : (aLo/g < a ∧ a ≤ aHi/g) ↔ aLo < g*a ∧ g*a ≤ aHi := by
    rw [Nat.div_lt_iff_lt_mul g0,Nat.le_div_iff_mul_le g0,Nat.mul_comm a g]
  have pBounds (u : ℕ) : (l < u ∧ u ≤ r) ↔ l₀ < g*u ∧ g*u ≤ r₀ := by
    change l₀/g < u ∧ u ≤ r₀/g ↔ _
    rw [Nat.div_lt_iff_lt_mul g0,Nat.le_div_iff_mul_le g0,Nat.mul_comm u g]
  have factsI {a : ℕ} (ha : a ∈ I) : aLo/g < a ∧ a ≤ aHi/g ∧ a.Coprime v :=
    ⟨(mem_Ioc.mp (mem_filter.mp ha).1).1,(mem_Ioc.mp (mem_filter.mp ha).1).2,(mem_filter.mp ha).2.2⟩
  have factsJ {b : ℤ} (hb : b ∈ J) : b ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (b : ZMod v) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hb
  have zCast {b : ℤ} (b0 : 0 ≤ b) : (b.toNat : ZMod v) = (b : ZMod v) := by
    simpa only [Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod v)) (Int.toNat_of_nonneg b0)
  have gateBounds {a : ℕ} (a0 : 0 < a) {b : ℤ} (b0 : 0 ≤ b) :
      gate a b ↔ (l < a*b.toNat ∧ a*b.toNat ≤ r) ∧
        cutoffU n < b.toNat ∧ b.toNat ≤ min n (rightLargeCofactorCut n) := by
    unfold gate lo hi
    rw [← Int.toNat_of_nonneg b0]
    simp only [max_lt_iff, le_min_iff, Int.ofNat_lt, Int.ofNat_le, Int.toNat_natCast,
      Nat.div_lt_iff_lt_mul a0, Nat.le_div_iff_mul_le a0, Nat.mul_comm b.toNat a]
    tauto
  have lift_mem (t : ℤ × ℕ) (ht : t ∈ P) : f t ∈ swappedLowSelection n row g k := by
    obtain ⟨hb,ha⟩ := mem_product.mp (mem_filter.mp ht).1
    obtain ⟨aLow,aTop,ac⟩ := factsI ha
    have a0 := (Nat.zero_le _).trans_lt aLow
    obtain ⟨bR,bUnit⟩ := factsJ hb
    have b0 := (mem_Ioc.mp bR).1
    have ab := (aBounds t.2).mp ⟨aLow,aTop⟩
    have ⟨pb,pl,pr⟩ := (gateBounds a0 b0.le).mp (mem_filter.mp ht).2.1
    have range := (pBounds _).mp pb
    have hp := (mem_filter.mp ht).2.2
    have qU : g*t.2 ≤ cutoffU n := (ab.2.trans (min_le_right _ _)).trans kc
    have prod : (g*t.2)*t.1.toNat=g*(t.2*t.1.toNat) := by ring
    have normStep : rightLowWaveStep (f t)=g*(t.2*t.1.toNat) := prod
    have items : f t ∈ rightLowWaveItems n := by
      refine mem_sigma.mpr ⟨mem_Ioc.mpr ⟨pl,pr⟩,mem_Icc.mpr ⟨mul_pos g0 a0,le_min qU ?_⟩⟩
      exact (Nat.le_div_iff_mul_le ((Nat.zero_le _).trans_lt pl)).mpr (prod ▸ range.2.trans rN)
    have cop : (t.2*t.1.toNat).Coprime v := by
      have bp : t.1.toNat.Coprime v :=
        (ZMod.isUnit_iff_coprime _ _).mp (zCast b0.le ▸ bUnit)
      exact ac.mul_left bp
    have gcd : (rightLowWaveStep (f t)).gcd m=g := by
      rw [normStep,← gV,Nat.gcd_mul_left,cop.gcd_eq_one,mul_one]
    exact mem_filter.mpr ⟨items,hp.1,hp.2,mem_Ioc.mpr ab,gcd,normStep ▸ range.1,normStep ▸ range.2⟩
  have lift_surj (j : RightLowWaveIndex) (hj : j ∈ swappedLowSelection n row g k) :
      ∃ t ∈ P, f t = j := by
    obtain ⟨items,hp,hpn,fac,gcd,sl,sr⟩ := mem_filter.mp hj
    have qs : g ∣ j.2 := gcd ▸ right_low_common_gcd_dvd_short_factor hp hpn (gcd.symm ▸ gn)
    let a := j.2/g
    let b := j.1
    have aEq : g*a=j.2 := Nat.mul_div_cancel' qs
    have aB : aLo/g < a ∧ a ≤ aHi/g := (aBounds a).mpr (by rw [aEq]; exact mem_Ioc.mp fac)
    have a0 := (Nat.zero_le _).trans_lt aB.1
    have pR := mem_Ioc.mp (mem_sigma.mp items).1
    have b0 : 0 < b := (Nat.zero_le _).trans_lt pR.1
    have wEq : rightLowWaveStep j = g*(a*b) := by
      rw [← mul_assoc,aEq]
      rfl
    have wG : rightLowWaveStep j/g = a*b := by rw [wEq,Nat.mul_div_cancel_left _ g0]
    have pb := (pBounds (a*b)).mpr (by rw [← wEq]; exact ⟨sl,sr⟩)
    have bS : b ≤ S := (Nat.le_div_iff_mul_le (Nat.succ_pos (aLo/g))).mpr (by
      rw [Nat.mul_comm]; exact (Nat.mul_le_mul_right b aB.1).trans pb.2)
    have cop : (a*b).Coprime v := by
      have h := Nat.coprime_div_gcd_div_gcd (m := rightLowWaveStep j) (n := m) (gcd.symm ▸ g0)
      rwa [gcd,wG] at h
    have jI : a ∈ I := mem_filter.mpr ⟨mem_Ioc.mpr aB,
      Nat.gcd_eq_right (dvd_mul_right g a),cop.coprime_dvd_left (dvd_mul_right _ _)⟩
    have jJ : (b : ℤ) ∈ J := by
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨by exact_mod_cast b0,by exact_mod_cast bS⟩,?_⟩
      rw [Int.cast_natCast]
      exact (ZMod.isUnit_iff_coprime _ _).mpr (cop.coprime_dvd_left (dvd_mul_left _ _))
    have ga : gate a (b : ℤ) := (gateBounds a0 (by positivity)).mpr (by
      simp only [Int.toNat_natCast]; exact ⟨pb,pR⟩)
    refine ⟨((b : ℤ),a),mem_filter.mpr ⟨mem_product.mpr ⟨jJ,jI⟩,ga,?_⟩,?_⟩
    · simpa only [admissible,Int.toNat_natCast] using And.intro hp hpn
    · change (⟨(b : ℤ).toNat,g*a⟩ : RightLowWaveIndex) = j
      rw [Int.toNat_natCast,aEq]
  have val (t : ℤ × ℕ) (ht : t ∈ P) : W t=swappedLowResidueTerm n m (f t) := by
    obtain ⟨items,_,_,_,gcd,loStep,_⟩ := mem_filter.mp (lift_mem t ht)
    let w := rightLowWaveStep (f t)
    have large : expandedHighModulusCap n < w := (le_max_left _ _).trans_lt loStep
    have high := root_low_step_before_case n0 large
    have order := swapped_low_step_above_left m0 mSquare loStep
    have e := right_low_residue_above_root_eq_single_prefix items high order m0 mN (gcd.symm ▸ gn)
    dsimp only at e
    change w.gcd m=g at gcd
    rw [gcd] at e
    have wG : w/g = t.2*t.1.toNat := by
      change (g*t.2*t.1.toNat)/g = _
      rw [mul_assoc,Nat.mul_div_cancel_left _ g0]
    have cast : (t.1.toNat : ZMod v) = (t.1 : ZMod v) :=
      zCast (mem_Ioc.mp (factsJ (mem_product.mp (mem_filter.mp ht).1).1).1).1.le
    have phase : ((t.2*t.1.toNat : ℕ) : ZMod v) = (t.2 : ZMod v)*(t.1 : ZMod v) := by
      rw [Nat.cast_mul,cast]
    rw [wG,Int.natCast_ediv,phase] at e
    unfold W swappedLowResidueTerm swappedLowShortWeight rightLowWaveWeight F
    rw [e]
  have flat : swappedLowWindow n row g k = ∑ t ∈ P, W t := by
    change gatedBilinearSum I J (swappedLowShortWeight g) (swappedLowPrimeWeight n) lo hi F = _
    rw [gated_bilinear_sum_eq_pair_sum]
    unfold P
    rw [sum_filter,sum_product]
    refine sum_congr rfl fun b hb => sum_congr rfl fun a ha => ?_
    change (if gate a b then _ else 0) = (if gate a b ∧ admissible b then W (b,a) else 0)
    by_cases h : gate a b
    · have a0 := (Nat.zero_le _).trans_lt (factsI ha).1
      have b0 := (mem_Ioc.mp (factsJ hb).1).1.le
      have bn := ((gateBounds a0 b0).mp h).2.2.trans (min_le_left _ _)
      by_cases p : admissible b
      · have on : b.toNat.Prime ∧ ¬b.toNat ∣ n ∧ b.toNat ≤ n := ⟨p.1,p.2,bn⟩
        rw [ite_eq_left h,ite_eq_left (And.intro h p)]
        simp only [W,swappedLowPrimeWeight,ite_eq_left on]
      · have off : ¬(b.toNat.Prime ∧ ¬b.toNat ∣ n ∧ b.toNat ≤ n) := fun hx => p ⟨hx.1,hx.2.1⟩
        rw [ite_eq_left h,ite_eq_right (fun hx : gate a b ∧ admissible b => p hx.2)]
        simp only [swappedLowPrimeWeight,ite_eq_right off,mul_zero,zero_mul]
    · simp [h]
  rw [flat]
  refine sum_bij (fun t _ => f t) lift_mem ?_ ?_ val
  swap
  · intro i hi
    obtain ⟨t,ht,eqt⟩ := lift_surj i hi
    exact ⟨t,ht,eqt⟩
  intro t ht u hu heq
  have positive {x : ℤ × ℕ} (hx : x ∈ P) : 0 ≤ x.1 :=
    (mem_Ioc.mp (factsJ (mem_product.mp (mem_filter.mp hx).1).1).1).1.le
  have fst : t.1.toNat=u.1.toNat := congrArg Sigma.fst heq
  have snd : g*t.2=g*u.2 := congrArg (fun j : RightLowWaveIndex => j.2) heq
  exact Prod.ext (by rw [← Int.toNat_of_nonneg (positive ht),← Int.toNat_of_nonneg (positive hu),fst])
    (Nat.eq_of_mul_eq_mul_left g0 snd)

end

end B13BoundedStepProductSavingProof

end

/- Swapped low row selection -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical

noncomputable section

private theorem floor_le_cutoffU_of_band {n k : ℕ} (n1 : 1 ≤ n) (hk : k ≤ 2047) :
    swappedHighFactorFloor n (k+1) ≤ cutoffU n := by
  have nr : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have kr : ((k+1 : ℕ) : ℝ) ≤ 2048 := by exact_mod_cast (show k+1 ≤ 2048 by omega)
  exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nr (by linarith only [kr]))

private theorem cutoffU_le_floor_of_band {n k : ℕ} (n1 : 1 ≤ n) (hk : 2048 ≤ k) :
    cutoffU n ≤ swappedHighFactorFloor n k := by
  have nr : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have kr : (2048 : ℝ) ≤ k := by exact_mod_cast hk
  exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nr (by linarith only [kr]))

theorem swapped_low_factor_blocks_cover {n q : ℕ} (n1 : 1 ≤ n)
    (qL : rightVaughanCut n < q) (qH : q ≤ cutoffU n) :
    ∃! k, k ∈ Icc 128 2047 ∧ q ∈ swappedHighFactorBlock n k := by
  have nr : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have cap : cutoffU n ≤ swappedHighFactorCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nr (by norm_num : (1/16 : ℝ) ≤ 31/96))
  obtain ⟨k,⟨km,kq⟩,uniq⟩ := swapped_high_factor_blocks_cover n1 (mem_Ioc.mpr ⟨qL,qH.trans cap⟩)
  have kHi : k ≤ 2047 := by
    by_contra! h
    have lower : cutoffU n ≤ swappedHighFactorLower n k :=
      (cutoffU_le_floor_of_band n1 (by omega)).trans (le_max_right _ _)
    exact (not_lt_of_ge qH) (lower.trans_lt (mem_Ioc.mp kq).1)
  refine ⟨k,⟨mem_Icc.mpr ⟨(mem_Icc.mp km).1,kHi⟩,kq⟩,?_⟩
  intro j hj
  exact uniq j ⟨Icc_subset_Icc_right (by decide) hj.1,hj.2⟩

def swappedLowRowItems (n : ℕ) (row : ℕ × ℕ) : Finset RightLowWaveIndex :=
  let m := leftBilinearStep row
  (rightLowWaveItems n).filter fun j =>
    let w := rightLowWaveStep j
    w.gcd m ∈ swappedHighDivisors n m ∧
      swappedLowStepLower n m < w ∧ w ≤ swappedHighStepUpper n m ∧
      rightVaughanCut n < j.2 ∧ j.1.Prime ∧ ¬j.1 ∣ n

theorem swapped_low_row_eq_selected {n : ℕ} {row : ℕ × ℕ} (hr : row ∈ swappedHighRows n) :
    swappedLowRow n row = ∑ j ∈ swappedLowRowItems n row,
      swappedLowResidueTerm n (leftBilinearStep row) j := by
  let m := leftBilinearStep row
  let I := swappedLowRowItems n row
  let G := swappedHighDivisors n m
  let K := Icc 128 2047
  let d (j : RightLowWaveIndex) := (rightLowWaveStep j).gcd m
  let w := swappedLowResidueTerm n m
  have step := mem_Icc.mp (bilateral_left_step_range (mem_filter.mp hr).1)
  have n1 : 1 ≤ n := step.1.trans step.2
  have mapsG : ∀ j ∈ I, d j ∈ G := fun _ hj => (mem_filter.mp hj).2.1
  change swappedLowRow n row = ∑ j ∈ I, w j
  rw [← sum_fiberwise_of_maps_to mapsG w]
  unfold swappedLowRow
  refine sum_congr rfl fun g hg => ?_
  let I₁ := I.filter fun j => d j=g
  have data := mem_filter.mp hg
  have gn := (Nat.mem_divisors.mp data.1).1
  have g0 := Nat.pos_of_dvd_of_pos gn n1
  have gm := data.2.2.2
  have eqFilter (k : ℕ) : swappedLowSelection n row g k =
      I₁.filter (fun j => j.2 ∈ swappedHighFactorBlock n k) := by
    ext j
    constructor
    · intro hj
      obtain ⟨items,prime,nd,fac,gg,lo,up⟩ := mem_filter.mp hj
      have dg : d j ∈ G := by change (rightLowWaveStep j).gcd m ∈ G; rw [gg]; exact hg
      have qL : rightVaughanCut n < j.2 := (le_max_left _ _).trans_lt (mem_Ioc.mp fac).1
      have jI : j ∈ I := mem_filter.mpr ⟨items,dg,lo,up,qL,prime,nd⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨jI,gg⟩,fac⟩
    · intro hj
      obtain ⟨j₁,fac⟩ := mem_filter.mp hj
      obtain ⟨j₀,gg⟩ := mem_filter.mp j₁
      obtain ⟨items,_,lo,up,_,prime,nd⟩ := mem_filter.mp j₀
      exact mem_filter.mpr ⟨items,prime,nd,fac,gg,lo,up⟩
  calc
    (∑ k ∈ K, swappedLowWindow n row g k) =
        ∑ k ∈ K, ∑ j ∈ I₁.filter (fun j => j.2 ∈ swappedHighFactorBlock n k), w j := by
      refine sum_congr rfl fun k hk => ?_
      rw [← eqFilter k]
      exact swapped_low_window_eq_selected hr g0 gn gm (floor_le_cutoffU_of_band n1 (mem_Icc.mp hk).2)
    _ = ∑ j ∈ I₁, ∑ k ∈ K, if j.2 ∈ swappedHighFactorBlock n k then w j else 0 := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = ∑ j ∈ I₁, w j := by
      refine sum_congr rfl fun j hj => ?_
      have j₀ : j ∈ I := (mem_filter.mp hj).1
      have info := mem_filter.mp j₀
      have qL : rightVaughanCut n < j.2 := info.2.2.2.2.1
      have qH : j.2 ≤ cutoffU n := (mem_Icc.mp (mem_sigma.mp info.1).2).2.trans (min_le_left _ _)
      obtain ⟨k,⟨kMem,kq⟩,uniq⟩ := swapped_low_factor_blocks_cover n1 qL qH
      rw [sum_eq_single_of_mem k kMem]
      · exact ite_eq_left kq
      · intro k' hk' neq
        exact ite_eq_right (fun h => neq (uniq k' ⟨hk',h⟩))

end

end B13BoundedStepProductSavingProof

end

/- Swapped low original saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def originalLowSwappedSlice (n : ℕ) : ℂ :=
  ∑ row ∈ swappedHighRows n, leftBilinearWeight n row *
    ∑ j ∈ swappedLowRowItems n row, rightLowWaveWeight j *
      (pairResidueError n (leftBilinearStep row) (rightLowWaveStep j) 0 (n/leftBilinearStep row)
        0 (rightLowWaveUpper n j) : ℂ)

def swappedLowVolumeCorrection (n : ℕ) : ℂ :=
  pairResidueSwapFamily n (swappedHighRows n) (rightLowWaveItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n)
    (leftBilinearWeight n) rightLowWaveWeight
    (fun i j => j ∈ swappedLowRowItems n i)

theorem original_low_swapped_eq_slice_add_correction (n : ℕ) :
    originalLowSwappedSlice n = swappedLowResidueSlice n + swappedLowVolumeCorrection n := by
  unfold originalLowSwappedSlice swappedLowResidueSlice swappedLowVolumeCorrection pairResidueSwapFamily
  rw [← sum_add_distrib]
  refine sum_congr rfl fun row hr => ?_
  rw [swapped_low_row_eq_selected hr]
  rw [mul_sum,mul_sum]
  let gate (j : RightLowWaveIndex) := j ∈ swappedLowRowItems n row
  have expand (f : RightLowWaveIndex → ℂ) :
      (∑ j ∈ swappedLowRowItems n row, f j) =
        ∑ j ∈ rightLowWaveItems n, if gate j then f j else 0 := by
    unfold swappedLowRowItems
    rw [sum_filter]
    refine sum_congr rfl fun j hj => ?_
    simp [gate,swappedLowRowItems,hj]
  rw [expand,expand,← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : j ∈ swappedLowRowItems n row
  · simp only [gate,ite_eq_left h]
    unfold swappedLowResidueTerm
    ring
  · simp only [gate,ite_eq_right h,zero_add]

private theorem norm_swapped_low_volume_correction_le {n : ℕ} (n0 : 0 < n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖swappedLowVolumeCorrection n‖ ≤ 24*(n : ℝ)^(21/32 : ℝ)*T^7*logBudget n^3 := by
  let A := extendedWideStepCap n
  let N := (n : ℝ)
  let L := logBudget n
  let W := T^3*L
  have nr : 0 < N := by change (0 : ℝ) < (n : ℝ); exact_mod_cast n0
  have A0 := extended_wide_step_pos n0
  have An := extended_wide_step_le n0
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have W0 : 0 ≤ W := by unfold W; positivity
  have leftRange (i : ℕ × ℕ) (hi : i ∈ swappedHighRows n) : leftBilinearStep i ∈ Icc 1 A := by
    have h := mem_filter.mp hi
    have step := mem_Icc.mp (bilateral_left_step_range h.1)
    exact mem_Icc.mpr ⟨step.1,
      (high_step_le_medium_of_square_le step.1 h.2.1).trans (old_step_cap_le_extended n)⟩
  have rightRange (j : RightLowWaveIndex) (hj : j ∈ rightLowWaveItems n) : rightLowWaveStep j ∈ Icc 1 A :=
    mem_Icc.mpr ⟨(mem_Icc.mp (bilateral_right_low_step_range hj)).1,
      (right_low_step_le_proved_medium_cap hj).trans (old_step_cap_le_extended n)⟩
  have leftMass (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ i ∈ (swappedHighRows n).filter (fun i => leftBilinearStep i=m), ‖leftBilinearWeight n i‖) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _)) (fun _ _ _ => norm_nonneg _)).trans
      (norm_bilateral_left_step_mass n0 T0 divisors m (Icc_subset_Icc_right An hm))
  have rightMass (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ j ∈ (rightLowWaveItems n).filter (fun j => rightLowWaveStep j=m), ‖rightLowWaveWeight j‖) ≤ W :=
    norm_bilateral_right_low_step_mass T1 divisors m (Icc_subset_Icc_right An hm)
  have logA : 1+Real.log (A : ℝ) ≤ L := by
    have h : (A : ℝ) ≤ N := by
      change (extendedWideStepCap n : ℝ) ≤ (n : ℝ)
      exact_mod_cast An
    have p : (0 : ℝ) < A := by exact_mod_cast A0
    unfold L logBudget
    linarith only [Real.log_le_log p (show (A : ℝ) ≤ (n : ℝ)+2 from h.trans (by simp [N]))]
  have aCap : (A : ℝ) ≤ N^(21/32 : ℝ) := Nat.floor_le (by positivity)
  have h := norm_pair_residue_swap_family_le n A n0 A0 (swappedHighRows n) (rightLowWaveItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) rightLowWaveStep (fun _ => 0)
    (rightLowWaveUpper n) (leftBilinearWeight n) rightLowWaveWeight
    (fun i j => j ∈ swappedLowRowItems n i) W0 leftRange rightRange leftMass rightMass
  calc
    _ ≤ 24*W^2*(A : ℝ)*(1+Real.log (A : ℝ))*(n.divisors.card : ℝ) := h
    _ ≤ 24*W^2*N^(21/32 : ℝ)*L*T := by gcongr; exact divisors n le_rfl
    _ = _ := by unfold W L N; ring

theorem swapped_low_volume_correction_saving : saving swappedLowVolumeCorrection := by
  intro ε he
  obtain ⟨D,D1,dBound⟩ := divisor_envelope_at_power 4096 (by decide)
  let C := 24*D^7
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-(1398/4096) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1398/4096)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(1398/4096) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have est : ∀ᶠ n : ℕ in atTop, ‖swappedLowVolumeCorrection n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le_power (1/4096) (by norm_num),
      scaled.eventually_lt_const he] with n hn logb small
    have nr : (0 : ℝ) < n := by exact_mod_cast hn
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/4096 : ℝ)
    let T := D*X
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1
      (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))
    have ex : (n : ℝ)^(21/32 : ℝ)*X^10 = (n : ℝ)^(-(1398/4096) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast nr.le,← Real.rpow_add nr,← Real.rpow_add_one nr.ne']
      congr 1
      norm_num
    calc
      _ ≤ 24*(n : ℝ)^(21/32 : ℝ)*T^7*logBudget n^3 :=
        norm_swapped_low_volume_correction_le hn T1 (dBound n)
      _ ≤ 24*(n : ℝ)^(21/32 : ℝ)*T^7*X^3 := by gcongr
      _ = C*((n : ℝ)^(21/32 : ℝ)*X^10) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(1398/4096) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
  obtain ⟨N,h⟩ := eventually_atTop.mp est
  exact ⟨N,fun n hn _ => h n hn⟩

theorem original_low_swapped_slice_saving : saving originalLowSwappedSlice := by
  intro ε he
  obtain ⟨N,h⟩ := swapped_low_residue_saving (ε/2) (by positivity)
  obtain ⟨M,hm⟩ := swapped_low_volume_correction_saving (ε/2) (by positivity)
  refine ⟨max N M,fun n hn even => ?_⟩
  rw [original_low_swapped_eq_slice_add_correction]
  exact (norm_add_le _ _).trans (by linarith only [h n (by omega) even,hm n (by omega) even])

end

end B13BoundedStepProductSavingProof

end

/- Thin low arithmetic cuts -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open scoped Classical Finset

noncomputable section

abbrev RightLowPairGate := ℕ → (ℕ × ℕ) → RightLowWaveIndex → Prop

def thinLowProductGate (gate : RightLowPairGate) (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  gate n i j ∧ thinHighProductCap n < leftBilinearStep i*rightLowWaveStep j

def thinLowRightItems (n : ℕ) : Finset RightLowWaveIndex :=
  extendedWaveItems n (rightLowWaveItems n) rightLowWaveStep

theorem thin_low_right_items_eq (n : ℕ) : thinLowRightItems n = rightLowWaveItems n := by
  apply filter_eq_self.mpr
  exact fun j hj => (right_low_step_le_proved_medium_cap hj).trans (old_step_cap_le_extended n)

def thinLowProductCut (gate : RightLowPairGate) (n : ℕ) : ℂ :=
  smallProductResidueFamily n (thinHighProductCap n) (thinHighLeftItems n) (thinLowRightItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n)
    (leftBilinearWeight n) (rightLowWaveWeight) (gate n)

def thinLowCommonCut (gate : RightLowPairGate) (n : ℕ) : ℂ :=
  gcdResidueFamily n (thinHighGcdCap n) (thinHighLeftItems n) (thinLowRightItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n)
    (leftBilinearWeight n) (rightLowWaveWeight) (thinLowProductGate gate n)

def thinLowTargetCut (gate : RightLowPairGate) (n : ℕ) : ℂ :=
  largeLeftDivisorResidueFamily n (thinHighLeftDivisorCap n) (thinHighGcdCap n)
    (thinHighLeftItems n) (thinLowRightItems n) leftBilinearStep rightLowWaveStep
    (fun _ => 0) (rightLowWaveUpper n)
    (leftBilinearWeight n) (rightLowWaveWeight) (thinLowProductGate gate n)

def thinLowCut (gate : RightLowPairGate) (n : ℕ) : ℂ :=
  thinLowProductCut gate n + thinLowCommonCut gate n + thinLowTargetCut gate n

theorem norm_thin_low_cut_le (gate : RightLowPairGate) {n : ℕ} (n0 : 0 < n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖thinLowCut gate n‖ ≤ 5*(n : ℝ)^(8191/8192 : ℝ)*T^9*logBudget n^4 := by
  let A := extendedWideStepCap n
  let N := (n : ℝ)
  let L := logBudget n
  let W := T^3*L
  let P := thinHighProductCap n
  let D := thinHighGcdCap n
  let E := thinHighLeftDivisorCap n
  have n1 : 1 ≤ N := by change (1 : ℝ) ≤ (n : ℝ); exact_mod_cast n0
  have np : 0 < N := zero_lt_one.trans_le n1
  have Ap := extended_wide_step_pos n0
  have An := extended_wide_step_le n0
  have T0 := zero_le_one.trans T1
  have L1 := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have W0 : 0 ≤ W := by unfold W; positivity
  have range {α : Type} {S : Finset α} {u : α → ℕ} (h : ∀ x ∈ S, u x ∈ Icc 1 n) (x : α)
      (hx : x ∈ extendedWaveItems n S u) : u x ∈ Icc 1 A := by
    obtain ⟨base,limit⟩ := mem_filter.mp hx
    exact mem_Icc.mpr ⟨(mem_Icc.mp (h x base)).1,limit⟩
  have mass {α : Type} {S : Finset α} {u : α → ℕ} {a : α → ℂ}
      (h : ∀ m ∈ Icc 1 n, (∑ i ∈ S.filter (fun i => u i=m), ‖a i‖) ≤ W)
      (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ i ∈ (extendedWaveItems n S u).filter (fun i => u i=m), ‖a i‖) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (h m (Icc_subset_Icc_right An hm))
  have leftRange (i : ℕ × ℕ) (hi : i ∈ thinHighLeftItems n) : leftBilinearStep i ∈ Icc 1 A :=
    range (u := leftBilinearStep) (fun _ h => bilateral_left_step_range h) i hi
  have rightRange (j : RightLowWaveIndex) (hj : j ∈ thinLowRightItems n) : rightLowWaveStep j ∈ Icc 1 A :=
    range (u := rightLowWaveStep) (fun _ h => bilateral_right_low_step_range h) j hj
  have leftMass := mass (norm_bilateral_left_step_mass n0 T0 divisors)
  have rightMass := mass (norm_bilateral_right_low_step_mass T1 divisors)
  have logN : 1+Real.log N ≤ L := by
    unfold L logBudget
    linarith only [Real.log_le_log np (show N ≤ (n : ℝ)+2 by dsimp [N]; linarith)]
  have logA : 1+Real.log (A : ℝ) ≤ L := by
    have h : (A : ℝ) ≤ N := by
      change (extendedWideStepCap n : ℝ) ≤ (n : ℝ)
      exact_mod_cast An
    linarith only [Real.log_le_log (by exact_mod_cast Ap : (0 : ℝ) < A) h, logN]
  have logN0 : 0 ≤ 1+Real.log N := add_nonneg zero_le_one (Real.log_nonneg n1)
  have product := norm_small_product_residue_family_le n P A (thinHighLeftItems n) (thinLowRightItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) rightLowWaveStep (fun _ => 0)
    (rightLowWaveUpper n) (leftBilinearWeight n) (rightLowWaveWeight)
    (gate n) W0 leftRange rightRange leftMass rightMass
  have common := norm_gcd_residue_family_le (D := D) n0 An (thinHighLeftItems n) (thinLowRightItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) rightLowWaveStep (fun _ => 0)
    (rightLowWaveUpper n) (leftBilinearWeight n) (rightLowWaveWeight)
    (thinLowProductGate gate n) W0 T0 divisors leftRange rightRange leftMass rightMass
  have target := norm_large_left_divisor_residue_family_le (D := E) (G := D) n0 An
    (thinHighLeftItems n) (thinLowRightItems n) leftBilinearStep rightLowWaveStep (fun _ => 0)
    (rightLowWaveUpper n) (leftBilinearWeight n) (rightLowWaveWeight)
    (thinLowProductGate gate n) W0 T0 divisors leftRange rightRange leftMass rightMass
  let H := N^(8191/8192 : ℝ)
  have Ptop : (P : ℝ) ≤ H := Nat.floor_le (by positivity)
  have Dtop : (D : ℝ) ≤ N^(1/4096 : ℝ) := Nat.floor_le (by positivity)
  have Ddiv : N/((D : ℝ)+1) ≤ N^(4095/4096 : ℝ) := by
    calc
      _ ≤ N/N^(1/4096 : ℝ) := div_le_div_of_nonneg_left np.le (by positivity) (Nat.lt_floor_add_one _).le
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub np]; norm_num
  have Ediv : N/((E : ℝ)+1) ≤ N^(2047/2048 : ℝ) := by
    calc
      _ ≤ N/N^(1/2048 : ℝ) := div_le_div_of_nonneg_left np.le (by positivity) (Nat.lt_floor_add_one _).le
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub np]; norm_num
  have bProduct : ‖thinLowProductCut gate n‖ ≤ H*T^9*L^4 := by
    refine product.trans ?_
    calc
      _ ≤ W^2*H*L := by gcongr
      _ = H*T^6*L^3 := by unfold W; ring
      _ ≤ _ := by
        have ht : T^6 ≤ T^9 := pow_le_pow_right₀ T1 (by decide)
        have hl : L^3 ≤ L^4 := pow_le_pow_right₀ L1 (by decide)
        gcongr
  have bCommon : ‖thinLowCommonCut gate n‖ ≤ 2*H*T^9*L^4 := by
    refine common.trans ?_
    have d := Ddiv.trans (Real.rpow_le_rpow_of_exponent_le n1 (by norm_num :
      (4095/4096 : ℝ) ≤ 8191/8192))
    have sq : (1+Real.log N)^2 ≤ L^2 := pow_le_pow_left₀ logN0 logN 2
    have l : T^2+(1+Real.log N)^2 ≤ 2*T^2*L^2 := by
      have x := le_mul_of_one_le_right (sq_nonneg T) (one_le_pow₀ L1 (n := 2))
      have y := sq.trans (le_mul_of_one_le_left (sq_nonneg L) (one_le_pow₀ T1 (n := 2)))
      linarith only [x,y]
    calc
      _ ≤ T*(W^2*H*(2*T^2*L^2)) := by gcongr
      _ = _ := by unfold W; ring
  have bTarget : ‖thinLowTargetCut gate n‖ ≤ 2*H*T^9*L^4 := by
    refine target.trans ?_
    have d : 1 ≤ N^(1/4096 : ℝ) := Real.one_le_rpow n1 (by norm_num)
    have ht : T^2+(D : ℝ)*L^2 ≤ 2*N^(1/4096 : ℝ)*T^2*L^2 := by
      have a := (le_mul_of_one_le_left (sq_nonneg T) d).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ L1 (n := 2)))
      have b := mul_le_mul_of_nonneg_right
        (Dtop.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ T1 (n := 2)))) (sq_nonneg L)
      linarith only [a,b]
    calc
      _ ≤ T*(W^2*N^(2047/2048 : ℝ)*(2*N^(1/4096 : ℝ)*T^2*L^2)) := by gcongr
      _ = 2*(N^(2047/2048 : ℝ)*N^(1/4096 : ℝ))*T^9*L^4 := by unfold W; ring
      _ ≤ _ := by
        have ex : N^(2047/2048 : ℝ)*N^(1/4096 : ℝ) ≤ H := by
          rw [← Real.rpow_add np]
          exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        gcongr
  exact (norm_add_le _ _).trans
    ((add_le_add ((norm_add_le _ _).trans (add_le_add bProduct bCommon)) bTarget).trans_eq (by unfold H N L; ring))
theorem thin_low_cut_saving (gate : RightLowPairGate) : saving (thinLowCut gate) := by
  intro ε he
  obtain ⟨D,D1,dBound⟩ := divisor_envelope_at_power 262144 (by decide)
  let C := 5*D^9
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-(19/262144) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 19/262144)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(19/262144) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have estimate : ∀ᶠ n : ℕ in atTop, ‖thinLowCut gate n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le_power (1/262144) (by norm_num),
      scaled.eventually_lt_const he] with n hn logb small
    have nr : (0 : ℝ) < n := by exact_mod_cast hn
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/262144 : ℝ)
    let T := D*X
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1
      (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))
    have ex : (n : ℝ)^(8191/8192 : ℝ)*X^13 =
        (n : ℝ)^(-(19/262144) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast nr.le,← Real.rpow_add nr,← Real.rpow_add_one nr.ne']
      congr 1
      norm_num
    calc
      _ ≤ 5*(n : ℝ)^(8191/8192 : ℝ)*T^9*logBudget n^4 :=
        norm_thin_low_cut_le gate hn T1 (dBound n)
      _ ≤ 5*(n : ℝ)^(8191/8192 : ℝ)*T^9*X^4 := by gcongr
      _ = C*((n : ℝ)^(8191/8192 : ℝ)*X^13) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(19/262144) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
  obtain ⟨N,h⟩ := eventually_atTop.mp estimate
  exact ⟨N,fun n hn _ => h n hn⟩

end

end B13BoundedStepProductSavingProof

end

/- Low large q near geometry -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical

noncomputable section

def lowLargeQNearGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  j.1.Prime ∧ ¬j.1 ∣ n ∧ rightVaughanCut n < j.2 ∧ expandedHighModulusCap n < v ∧
    prefixStepGate n u v ∧ subcriticalMediumProductCap n < u*v ∧ u*v ≤ 2*n

def lowLargeQNearKept (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  lowLargeQNearGate n i j ∧ thinHighProductCap n < u*v ∧
    u.gcd v ≤ thinHighGcdCap n ∧ u.gcd n ≤ thinHighLeftDivisorCap n ∧ u.gcd v ∣ n

private theorem low_large_q_row_mem {n v : ℕ} {row : ℕ × ℕ}
    (large : (2 : ℝ) ≤ (n : ℝ)^(3/1024 : ℝ))
    (hi : row ∈ bilateralLeftWaveItems n) (vTop : v ≤ extendedWideStepCap n)
    (vLower : expandedHighModulusCap n < v)
    (prodLo : thinHighProductCap n < leftBilinearStep row*v)
    (prodUp : leftBilinearStep row*v ≤ 2*n)
    (char : (leftBilinearStep row).gcd n ≤ thinHighLeftDivisorCap n) :
    row ∈ swappedHighRows n := by
  let u := leftBilinearStep row
  let M := (u : ℝ)
  let N := (n : ℝ)
  let V := (v : ℝ)
  have step := mem_Icc.mp (bilateral_left_step_range hi)
  have np : 0 < N := by
    change (0 : ℝ) < (n : ℝ)
    exact_mod_cast (Nat.zero_lt_one.trans_le (step.1.trans step.2))
  have hLo : N^(515/1024 : ℝ) < V := by
    refine (Nat.lt_floor_add_one _).trans_le ?_
    change (⌊N^(515/1024 : ℝ)⌋₊ : ℝ)+1 ≤ (v : ℝ)
    exact_mod_cast Nat.succ_le_of_lt vLower
  have productUpper : M*V ≤ 2*N := by
    change (u : ℝ)*(v : ℝ) ≤ 2*(n : ℝ)
    exact_mod_cast prodUp
  have uTop : M ≤ N^(1/2 : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (515/1024 : ℝ))).mp
    calc
      _ ≤ M*V := mul_le_mul_of_nonneg_left hLo.le (by positivity)
      _ ≤ 2*N := productUpper
      _ ≤ N^(3/1024 : ℝ)*N := mul_le_mul_of_nonneg_right large np.le
      _ = N^(1/2 : ℝ)*N^(515/1024 : ℝ) := by
        rw [← Real.rpow_add_one np.ne',← Real.rpow_add np]
        norm_num
  have sq : u^2 ≤ n := by
    have h : M ≤ Real.sqrt N := by rw [Real.sqrt_eq_rpow]; exact uTop
    have res := (Real.le_sqrt (by positivity : 0 ≤ M) np.le).mp h
    change (u : ℝ)^2 ≤ (n : ℝ) at res
    exact_mod_cast res
  have pro : N^(255/256 : ℝ) ≤ M*V := by
    apply (Nat.lt_floor_add_one (N^(255/256 : ℝ))).le.trans
    have nat := Nat.succ_le_of_lt ((thin_high_product_cap_ge_old n).trans_lt prodLo)
    change (⌊N^(255/256 : ℝ)⌋₊ : ℝ)+1 ≤ (u : ℝ)*(v : ℝ)
    exact_mod_cast nat
  have vR : V ≤ N^(21/32 : ℝ) :=
    (by exact_mod_cast vTop : (v : ℝ) ≤ (extendedWideStepCap n : ℝ)).trans (Nat.floor_le (by positivity))
  have lo : N^(87/256 : ℝ) ≤ M := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (21/32 : ℝ))).mp
    calc
      _ = N^(255/256 : ℝ) := by rw [← Real.rpow_add np]; norm_num
      _ ≤ M*V := pro
      _ ≤ M*N^(21/32 : ℝ) := mul_le_mul_of_nonneg_left vR (by positivity)
  exact mem_filter.mpr ⟨hi,sq,lo,char⟩

theorem low_large_q_near_mem_iff {n : ℕ} {i : ℕ × ℕ} {j : RightLowWaveIndex}
    (large : (2 : ℝ) ≤ (n : ℝ)^(3/1024 : ℝ))
    (hi : i ∈ bilateralLeftWaveItems n) (hj : j ∈ rightLowWaveItems n) :
    (i ∈ swappedHighRows n ∧ j ∈ swappedLowRowItems n i) ↔
      leftBilinearStep i ≤ extendedWideStepCap n ∧ lowLargeQNearKept n i j := by
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  let g := u.gcd v
  have uRange := mem_Icc.mp (bilateral_left_step_range hi)
  have u0 : 0 < u := uRange.1
  have n0 : 0 < n := u0.trans_le uRange.2
  have vTop := (right_low_step_le_proved_medium_cap hj).trans (old_step_cap_le_extended n)
  constructor
  · rintro ⟨row,col⟩
    obtain ⟨_,sq,_,char⟩ := mem_filter.mp row
    obtain ⟨_,hdiv,low,up,short,prime,notDiv⟩ := mem_filter.mp col
    obtain ⟨data,gcdSmall,gcdMax,_⟩ := mem_filter.mp hdiv
    have gSmall : g ≤ thinHighGcdCap n := by simpa only [g,Nat.gcd_comm] using gcdSmall
    have gMax : g ≤ maximumStep n := by simpa only [g,Nat.gcd_comm] using gcdMax
    have gn : g ∣ n := by simpa only [g,Nat.gcd_comm] using (Nat.mem_divisors.mp data).1
    have uTop := (high_step_le_medium_of_square_le u0 sq).trans (old_step_cap_le_extended n)
    have prodMax : maximumStep n^2 < u*v := by
      have hx : maximumStep n^2/u < v := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt low
      simpa only [mul_comm u v] using (Nat.div_lt_iff_lt_mul u0).mp hx
    have prodThin : thinHighProductCap n < u*v := by
      have hx : thinHighProductCap n/u < v := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt low
      simpa only [mul_comm u v] using (Nat.div_lt_iff_lt_mul u0).mp hx
    have prodUp : u*v ≤ 2*n := by
      simpa only [mul_comm u v] using (Nat.le_div_iff_mul_le u0).mp (up.trans (min_le_right _ _))
    have vL : expandedHighModulusCap n < v := (le_max_left _ _).trans_lt low
    exact ⟨uTop,⟨prime,notDiv,short,vL,⟨prodMax,gMax⟩,(thin_high_product_cap_ge_old n).trans_lt prodThin,prodUp⟩,
      prodThin,gSmall,char,gn⟩
  · rintro ⟨_,⟨prime,notDiv,short,vL,step,_,prodUp⟩,prodThin,gSmall,char,gn⟩
    have hm := low_large_q_row_mem large hi vTop vL prodThin prodUp char
    have d : v.gcd u ∈ swappedHighDivisors n u := by
      refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_,n0.ne'⟩,?_,?_,Nat.gcd_dvd_right v u⟩
      · simpa only [g,Nat.gcd_comm] using gn
      · simpa only [g,Nat.gcd_comm] using gSmall
      · simpa only [g,Nat.gcd_comm] using step.2
    have l : swappedLowStepLower n u < v := max_lt vL
      (max_lt ((Nat.div_lt_iff_lt_mul u0).mpr (by rw [Nat.mul_comm v u]; exact step.1))
        ((Nat.div_lt_iff_lt_mul u0).mpr (by rw [Nat.mul_comm v u]; exact prodThin)))
    have r : v ≤ swappedHighStepUpper n u := le_min vTop
      ((Nat.le_div_iff_mul_le u0).mpr (by rw [Nat.mul_comm v u]; exact prodUp))
    exact ⟨hm,mem_filter.mpr ⟨hj,d,l,r,short,prime,notDiv⟩⟩

end

end B13BoundedStepProductSavingProof

end

/- Low large q near saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter
open scoped Classical Finset

noncomputable section

def rightLowResidueTerm (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : ℂ :=
  leftBilinearWeight n i*rightLowWaveWeight j*
    (pairResidueError n (leftBilinearStep i) (rightLowWaveStep j) 0 (n/leftBilinearStep i)
      0 (rightLowWaveUpper n j) : ℂ)

def rightLowResidueFamily (gate : RightLowPairGate) (n : ℕ) : ℂ :=
  ∑ i ∈ thinHighLeftItems n, ∑ j ∈ thinLowRightItems n,
    if gate n i j then rightLowResidueTerm n i j else 0

theorem low_large_q_near_partition (n : ℕ) :
    rightLowResidueFamily lowLargeQNearGate n =
      rightLowResidueFamily lowLargeQNearKept n + thinLowCut lowLargeQNearGate n := by
  unfold rightLowResidueFamily thinLowCut thinLowProductCut thinLowCommonCut thinLowTargetCut
    smallProductResidueFamily gcdResidueFamily largeLeftDivisorResidueFamily
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  by_cases d : u.gcd v ∣ n
  · by_cases h : lowLargeQNearGate n i j
    · by_cases p : u*v ≤ thinHighProductCap n
      · simp [u,v,h,p,not_lt.mpr p,lowLargeQNearKept,thinLowProductGate,rightLowResidueTerm]
      · by_cases g : u.gcd v ≤ thinHighGcdCap n
        · by_cases l : u.gcd n ≤ thinHighLeftDivisorCap n <;>
            simp [u,v,h,p,lt_of_not_ge p,g,not_lt.mpr g,l,lt_of_not_ge,lowLargeQNearKept,
              thinLowProductGate,rightLowResidueTerm,d]
        · simp [u,v,h,p,lt_of_not_ge p,g,lt_of_not_ge g,lowLargeQNearKept,thinLowProductGate,rightLowResidueTerm]
    · simp [h,lowLargeQNearKept,thinLowProductGate]
  · simp [u,v,d,rightLowResidueTerm,pairResidueError]

private theorem sum_subset_with_membership_low_large_q_near_saving {α : Type*} {S T : Finset α} (h : S ⊆ T)
    (f : α → ℂ) : (∑ a ∈ S, f a) = ∑ a ∈ T, if a ∈ S then f a else 0 := by
  rw [← sum_filter]
  have eq : T.filter (fun a => a ∈ S) = S := by
    ext a
    exact ⟨fun ha => (mem_filter.mp ha).2,fun ha => mem_filter.mpr ⟨h ha,ha⟩⟩
  rw [eq]

theorem low_large_q_near_kept_eq_swapped {n : ℕ} (large : (2 : ℝ) ≤ (n : ℝ)^(3/1024 : ℝ)) :
    rightLowResidueFamily lowLargeQNearKept n = originalLowSwappedSlice n := by
  let I := bilateralLeftWaveItems n
  let J := rightLowWaveItems n
  let S := swappedHighRows n
  let R := fun i : ℕ × ℕ => swappedLowRowItems n i
  let V := rightLowResidueTerm n
  have out (i : ℕ × ℕ) (h : i ∈ S) : i ∈ I := (mem_filter.mp h).1
  have inside (i : ℕ × ℕ) : R i ⊆ J := filter_subset _ _
  have a : originalLowSwappedSlice n =
      ∑ i ∈ I, ∑ j ∈ J, if i ∈ S ∧ j ∈ R i then V i j else 0 := by
    unfold originalLowSwappedSlice
    have move (i : ℕ × ℕ) : leftBilinearWeight n i *
        (∑ j ∈ R i, rightLowWaveWeight j *
          (pairResidueError n (leftBilinearStep i) (rightLowWaveStep j) 0
            (n/leftBilinearStep i) 0 (rightLowWaveUpper n j) : ℂ)) = ∑ j ∈ R i, V i j := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      unfold V rightLowResidueTerm
      ring
    calc
      _ = ∑ i ∈ S, ∑ j ∈ R i, V i j := sum_congr rfl (fun i _ => move i)
      _ = _ := by
        rw [sum_subset_with_membership_low_large_q_near_saving (show S ⊆ I from fun i hi => out i hi)]
        refine sum_congr rfl fun i _ => ?_
        by_cases hi : i ∈ S
        · rw [ite_eq_left hi,sum_subset_with_membership_low_large_q_near_saving (inside i)]
          refine sum_congr rfl fun j _ => ?_
          by_cases hj : j ∈ R i
          · rw [ite_eq_left hj,ite_eq_left (And.intro hi hj)]
          · rw [ite_eq_right hj,ite_eq_right (fun h : i ∈ S ∧ j ∈ R i => hj h.2)]
        · simp [hi]
  have b : rightLowResidueFamily lowLargeQNearKept n =
      ∑ i ∈ I, ∑ j ∈ J, if leftBilinearStep i ≤ extendedWideStepCap n ∧ lowLargeQNearKept n i j then V i j else 0 := by
    unfold rightLowResidueFamily thinHighLeftItems extendedWaveItems
    rw [thin_low_right_items_eq, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : leftBilinearStep i ≤ extendedWideStepCap n
    · simp [h,V,J]
    · simp [h,V,J]
  rw [a,b]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have equivalence := low_large_q_near_mem_iff large hi hj
  by_cases h : i ∈ S ∧ j ∈ R i
  · rw [ite_eq_left h,ite_eq_left (equivalence.mp h)]
  · have k : ¬(leftBilinearStep i ≤ extendedWideStepCap n ∧ lowLargeQNearKept n i j) :=
      fun z => h (equivalence.mpr z)
    rw [ite_eq_right h,ite_eq_right k]

theorem low_large_q_near_saving : saving (rightLowResidueFamily lowLargeQNearGate) := by
  intro ε he
  obtain ⟨N,h⟩ := original_low_swapped_slice_saving (ε/2) (by positivity)
  obtain ⟨M,hm⟩ := thin_low_cut_saving lowLargeQNearGate (ε/2) (by positivity)
  obtain ⟨P,hp⟩ := eventually_atTop.mp eventually_swapped_high_large
  refine ⟨max P (max N M), fun n hn even => ?_⟩
  rw [low_large_q_near_partition,low_large_q_near_kept_eq_swapped (hp n (by omega))]
  exact (norm_add_le _ _).trans (by linarith only [h n (by omega) even,hm n (by omega) even])

end

end B13BoundedStepProductSavingProof

end

/- Outer left remainder -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4EnergyTail
open scoped Classical Finset

noncomputable section

def outerLeftLowItems (n : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n)

end

end B13BoundedStepProductSavingProof

end

/- Small modulus product remainder -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

def smallModulusProductSlice (n : ℕ) : ℂ :=
  boundedOuterLeftBaseFrom smallModulusProductGate n (outerLeftLowItems n) rightLowWaveStep (fun _ => 0)
    (rightLowWaveUpper n) rightLowWaveWeight +
  boundedOuterLeftBaseFrom smallModulusProductGate n (rightHighWaveItems n) rightHighWaveStep (rightHighWaveLower n)
    (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)

theorem small_modulus_product_slice_saving : saving smallModulusProductSlice := by
  have low := small_modulus_product_base_from_saving outerLeftLowItems rightLowWaveStep (fun _ _ => 0)
    rightLowWaveUpper (fun _ => rightLowWaveWeight)
    (fun _ _ hj => bilateral_right_low_step_range (mem_filter.mp hj).1) (fun _ _ _ => min_le_right _ _)
    (fun n T T1 divisors m hm =>
      (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
        (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_right_low_step_mass T1 divisors m hm))
  have high := small_modulus_product_base_from_saving rightHighWaveItems rightHighWaveStep
    rightHighWaveLower (fun n j => n/rightHighWaveStep j) rightHighWaveWeight
    (fun _ _ hj => bilateral_right_high_step_range hj) (fun _ _ _ => le_rfl)
    (fun n T T1 divisors m hm => norm_bilateral_right_high_step_mass (zero_le_one.trans T1) divisors m hm)
  intro ε he
  obtain ⟨N,h⟩ := low (ε/2) (by positivity)
  obtain ⟨M,hm⟩ := high (ε/2) (by positivity)
  refine ⟨max N M,fun n hn even => ?_⟩
  unfold smallModulusProductSlice
  exact (norm_add_le _ _).trans (by linarith only [h n (by omega) even,hm n (by omega) even])

def smallModulusProductBand (n u v : ℕ) : Prop :=
  v ≤ expandedHighModulusCap n ∧ u*v ≤ highFarStripProductCap n

def rawExpandedAboveSmallModulusFrom (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) : ℂ :=
  rawWavePairSum n (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep)
    (expandedWaveItems n J v) v p s w
    (fun x y => prefixStepGate n x y ∧ ¬smallModulusProductBand n x y)
    (fun u v l r a b => (pairResidueError n u v l r a b : ℂ))

def rawExpandedAfterSmallModulus (n : ℕ) : ℂ :=
  rawExpandedAboveSmallModulusFrom n (outerLeftLowItems n) rightLowWaveStep
    (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight +
  rawExpandedAboveSmallModulusFrom n (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)

private theorem raw_expanded_small_modulus_from_split (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) :
    rawExpandedWavePairSum n J v p s w (fun u v l r a b => (pairResidueError n u v l r a b : ℂ)) =
      rawExpandedAboveSmallModulusFrom n J v p s w +
      boundedOuterLeftBaseFrom smallModulusProductGate n J v p s w := by
  unfold rawExpandedWavePairSum rawExpandedAboveSmallModulusFrom rawWavePairSum boundedOuterLeftBaseFrom
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  let u := leftBilinearStep i
  let m := v j
  have gate : smallModulusProductGate n u m ↔ prefixStepGate n u m ∧ smallModulusProductBand n u m := by
    unfold smallModulusProductGate smallModulusProductBand
    tauto
  rw [gate]
  by_cases pre : prefixStepGate n u m <;>
    by_cases band : smallModulusProductBand n u m <;> simp [u,m,pre,band]

theorem raw_expanded_eq_small_modulus_split (n : ℕ) :
    rawExpandedResidue n = rawExpandedAfterSmallModulus n + smallModulusProductSlice n := by
  unfold rawExpandedResidue rawExpandedAfterSmallModulus smallModulusProductSlice outerLeftLowItems
  rw [raw_expanded_small_modulus_from_split,raw_expanded_small_modulus_from_split]
  abel

end

end B13BoundedStepProductSavingProof

end

/- High far strip factor cover -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical

noncomputable section

theorem high_far_strip_factor_blocks_cover {n a : ℕ} (n1 : 1 ≤ n)
    (ha : a ∈ Ioc (highFarStripFactorCut n) (outerRightFactorCap n)) :
    ∃! k, k ∈ Icc 256 10879 ∧ a ∈ highFarStripFactorBlock n k := by
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have mono : Monotone (swappedHighFactorFloor n) := by
    intro j k le
    have hr : (j : ℝ) ≤ k := by exact_mod_cast le
    exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR
      (div_le_div_of_nonneg_right hr (by norm_num)))
  have Lo : swappedHighFactorFloor n 256 = highFarStripFactorCut n := by
    unfold swappedHighFactorFloor highFarStripFactorCut
    norm_num
  have Hi : outerRightFactorCap n ≤ swappedHighFactorFloor n 10880 := by
    exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))
  have upper : a ≤ swappedHighFactorFloor n 10880 := (mem_Ioc.mp ha).2.trans Hi
  have existsBlock : ∃ t : ℕ, a ≤ swappedHighFactorFloor n t := ⟨10880,upper⟩
  let t := Nat.find existsBlock
  have tLe : t ≤ 10880 := Nat.find_min' existsBlock upper
  have tHi : a ≤ swappedHighFactorFloor n t := Nat.find_spec existsBlock
  have tLo : 256 < t := by
    apply lt_of_not_ge
    intro h
    have impossible := tHi.trans (mono h)
    rw [Lo] at impossible
    exact (not_le_of_gt (mem_Ioc.mp ha).1) impossible
  let k := t-1
  have kn : k+1=t := by unfold k; omega
  have kt : k<t := by unfold k; omega
  have kMem : k ∈ Icc 256 10879 := mem_Icc.mpr ⟨by omega,by omega⟩
  have lo : swappedHighFactorFloor n k < a := lt_of_not_ge (Nat.find_min existsBlock kt)
  have hi : a ≤ swappedHighFactorFloor n (k+1) := by rw [kn]; exact tHi
  have inK : a ∈ highFarStripFactorBlock n k :=
    mem_Ioc.mpr ⟨max_lt (mem_Ioc.mp ha).1 lo,le_min (mem_Ioc.mp ha).2 hi⟩
  refine ⟨k,⟨kMem,inK⟩,fun j hj => ?_⟩
  have separate (b c : ℕ) (hb : a ∈ highFarStripFactorBlock n b)
      (hc : a ∈ highFarStripFactorBlock n c) (bc : b < c) : False := by
    have upper : a ≤ swappedHighFactorFloor n (b+1) := (mem_Ioc.mp hb).2.trans (min_le_right _ _)
    have lower : swappedHighFactorFloor n c < a := (le_max_right _ _).trans_lt (mem_Ioc.mp hc).1
    exact (not_le_of_gt lower) (upper.trans (mono bc))
  exact le_antisymm (le_of_not_gt (separate k j inK hj.2)) (le_of_not_gt (separate j k hj.2 inK))

end

end B13BoundedStepProductSavingProof

end

/- Large high product geometry -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def largeHighProductStepLower (n : ℕ) (i : ℕ × ℕ) : ℕ :=
  let u := leftBilinearStep i
  max (expandedHighModulusCap n) (max (maximumStep n^2/u) (thinHighProductCap n/u))

def largeHighProductWindow (n : ℕ) (i : ℕ × ℕ) (g e k : ℕ) : ℂ :=
  let m := leftBilinearStep i
  let v := m/g
  let l := largeHighProductStepLower n i/g
  let r := highFarStripStepUpper n m/g
  let I := highFarStripFactors n m g e k
  let J := intIntervalModUnits v 0 (highFarStripCofactorCap n m g e k)
  let α (a : ℕ) : ℂ := (rightHighWaveFactor n (e*a) : ℂ)
  let β (j : ℤ) := groupedRightHighMoebius n ((g/e)*j.toNat)
  let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (swappedHighTailLower n g e)
  let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (swappedHighTailUpper n m g e a)
  let F (a : ℕ) (j : ℤ) (t : ℤ) :=
    centeredIntIntervalResidue v 0 t ((n/g : ℕ)*((a : ZMod v)*(j : ZMod v))⁻¹)
  gatedBilinearSum I J α β lo hi
      (fun a j => F a j (((n/g-m/g : ℕ) : ℤ)/((a*j.toNat : ℕ) : ℤ))) -
    gatedBilinearSum I J α β lo hi (fun a j => F a j (swappedHighPrefixLower n e a))

def largeHighProductGate (n : ℕ) (row : ℕ × ℕ) (v : ℕ) : Prop :=
  let u := leftBilinearStep row
  u ≤ extendedWideStepCap n ∧ v ≤ expandedWideStepCap n ∧ expandedHighModulusCap n < v ∧
    prefixStepGate n u v ∧ thinHighProductCap n < u*v ∧ u*v ≤ highFarStripProductCap n ∧
    u.gcd v ≤ thinHighGcdCap n ∧ u.gcd n ≤ thinHighLeftDivisorCap n

theorem large_high_product_step_gate_iff {n v : ℕ} {row : ℕ × ℕ}
    (u0 : 0 < leftBilinearStep row) :
    (largeHighProductStepLower n row < v ∧ v ≤ highFarStripStepUpper n (leftBilinearStep row)) ↔
      v ≤ expandedWideStepCap n ∧ expandedHighModulusCap n < v ∧
        maximumStep n^2 < leftBilinearStep row*v ∧
        thinHighProductCap n < leftBilinearStep row*v ∧
        leftBilinearStep row*v ≤ highFarStripProductCap n := by
  unfold largeHighProductStepLower highFarStripStepUpper
  dsimp only
  simp only [max_lt_iff,le_min_iff,Nat.div_lt_iff_lt_mul u0,Nat.le_div_iff_mul_le u0,
    Nat.mul_comm v (leftBilinearStep row)]
  tauto

theorem large_high_product_row_mem {n v : ℕ} {row : ℕ × ℕ}
    (large : (2 : ℝ) ≤ (n : ℝ)^(1/1024 : ℝ))
    (hi : row ∈ bilateralLeftWaveItems n)
    (hg : largeHighProductGate n row v) : row ∈ outerRightRows n := by
  let u := leftBilinearStep row
  let N := (n : ℝ)
  let U := (u : ℝ)
  let V := (v : ℝ)
  obtain ⟨_,hiV,loV,_,loP,hiP,_,char⟩ := hg
  have step := mem_Icc.mp (bilateral_left_step_range hi)
  have n0 : 0 < n := step.1.trans step.2
  have nr : 1 ≤ N := by change (1 : ℝ) ≤ (n : ℝ); exact_mod_cast n0
  have np : 0 < N := zero_lt_one.trans_le nr
  have vLo : N^(515/1024 : ℝ) < V := (Nat.lt_floor_add_one _).trans_le (by
    change (expandedHighModulusCap n : ℝ)+1 ≤ (v : ℝ)
    exact_mod_cast Nat.succ_le_of_lt loV)
  have vHi : V ≤ N^(511/768 : ℝ) :=
    (show V ≤ (expandedWideStepCap n : ℝ) by
      change (v : ℝ) ≤ (expandedWideStepCap n : ℝ)
      exact_mod_cast hiV).trans (Nat.floor_le (by positivity))
  have prodLower : N^(8191/8192 : ℝ) ≤ U*V := (Nat.lt_floor_add_one _).le.trans (by
    change (thinHighProductCap n : ℝ)+1 ≤ (u : ℝ)*(v : ℝ)
    exact_mod_cast Nat.succ_le_of_lt loP)
  have prodUpper : U*V ≤ 2*N^(4097/4096 : ℝ) := by
    calc
      _ ≤ (highFarStripProductCap n : ℝ) := by
        change (u : ℝ)*(v : ℝ) ≤ (highFarStripProductCap n : ℝ)
        exact_mod_cast hiP
      _ ≤ _ := by unfold highFarStripProductCap; push_cast; gcongr; exact Nat.floor_le (by positivity)
  have geoLo : N^(171/512 : ℝ) ≤ U := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (511/768 : ℝ))).mp
    calc
      _ ≤ N^(8191/8192 : ℝ) := by
        rw [← Real.rpow_add np]
        exact Real.rpow_le_rpow_of_exponent_le nr (by norm_num)
      _ ≤ U*V := prodLower
      _ ≤ _ := mul_le_mul_of_nonneg_left vHi (by positivity)
  have geoHi : U ≤ N^(1/2 : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (515/1024 : ℝ))).mp
    calc
      _ ≤ U*V := mul_le_mul_of_nonneg_left vLo.le (by positivity)
      _ ≤ 2*N^(4097/4096 : ℝ) := prodUpper
      _ ≤ N^(1/1024 : ℝ)*N^(4097/4096 : ℝ) := mul_le_mul_of_nonneg_right large (by positivity)
      _ ≤ N^(1/2 : ℝ)*N^(515/1024 : ℝ) := by
        rw [← Real.rpow_add np,← Real.rpow_add np]
        exact Real.rpow_le_rpow_of_exponent_le nr (by norm_num)
  have square : u^2 ≤ n := by
    rw [← Real.sqrt_eq_rpow] at geoHi
    have sq : (u : ℝ)^2 ≤ (n : ℝ) := (Real.le_sqrt (by positivity) (by positivity)).mp geoHi
    exact_mod_cast sq
  exact mem_filter.mpr ⟨hi,square,geoLo,char⟩

theorem eventually_large_high_product_scale : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (n : ℝ)^(1/1024 : ℝ) := by
  exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/1024)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2

end

end B13BoundedStepProductSavingProof

end

/- Large high product window bridge -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def largeHighProductSelection (n : ℕ) (row : ℕ × ℕ) (g e k : ℕ) : Finset (ℕ × ℕ) :=
  let m := leftBilinearStep row
  (groupedRightHighItems n).filter fun t =>
    let v := swappedHighGroupedStep t
    t.2 ∈ highFarStripFactorBlock n k ∧ v.gcd m = g ∧ t.2.gcd g = e ∧
      largeHighProductStepLower n row < v ∧ v ≤ highFarStripStepUpper n m ∧
      rightLargeCofactorCut n/t.2 ≤ (n/g-m/g)/(v/g)

theorem large_high_product_window_eq_grouped_sum {n g e k : ℕ} {row : ℕ × ℕ}
    (hrow : row ∈ outerRightRows n)
    (g0 : 0 < g) (gn : g ∣ n) (gm : g ∣ leftBilinearStep row)
    (e0 : 0 < e) (eg : e ∣ g) :
    largeHighProductWindow n row g e k = ∑ t ∈ largeHighProductSelection n row g e k,
      swappedHighGroupedResidue n (leftBilinearStep row) t := by
  let m := leftBilinearStep row
  let v := m/g
  let h := g/e
  let l₀ := largeHighProductStepLower n row
  let r₀ := highFarStripStepUpper n m
  let l := l₀/g
  let r := r₀/g
  let aLo := highFarStripFactorLower n k
  let aHi := min (outerRightFactorCap n) (swappedHighFactorFloor n (k+1))
  let S := highFarStripCofactorCap n m g e k
  let I := highFarStripFactors n m g e k
  let J := intIntervalModUnits v 0 S
  let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (swappedHighTailLower n g e)
  let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (swappedHighTailUpper n m g e a)
  let gate (a : ℕ) (j : ℤ) : Prop := lo a < j ∧ j ≤ hi a
  let P := (J ×ˢ I).filter fun t => gate t.2 t.1
  let liftPoint (t : ℤ × ℕ) : ℕ × ℕ := (h*t.1.toNat,e*t.2)
  let value := swappedHighGroupedResidue n m
  let F (a : ℕ) (j t : ℤ) :=
    centeredIntIntervalResidue v 0 t ((n/g : ℕ)*((a : ZMod v)*(j : ZMod v))⁻¹)
  let W (t : ℤ × ℕ) := swappedHighGroupedWeight n (liftPoint t) *
    (F t.2 t.1 (((n/g-m/g : ℕ) : ℤ)/((t.2*t.1.toNat : ℕ) : ℤ)) -
      F t.2 t.1 (swappedHighPrefixLower n e t.2))
  have rowData := mem_filter.mp hrow
  have steps := mem_Icc.mp (bilateral_left_step_range rowData.1)
  have m0 : 0 < m := steps.1
  have mN : m ≤ n := steps.2
  have n0 := m0.trans_le mN
  have modTop : m ≤ expandedHighModulusCap n :=
    square_le_implies_step_le_expanded_high_cap m0 rowData.2.1
  have hd : e*h=g := Nat.mul_div_cancel' eg
  have h0 : 0 < h := Nat.div_pos (Nat.le_of_dvd g0 eg) e0
  have gV : g*v=m := Nat.mul_div_cancel' gm
  have rN : r₀ ≤ n := (min_le_left _ _).trans (expanded_wide_step_le n0)
  have sN : S ≤ n := (Nat.div_le_self r (aLo/e+1)).trans ((Nat.div_le_self r₀ g).trans rN)
  have infoI {a : ℕ} (ha : a ∈ I) :
      aLo/e < a ∧ a ≤ aHi/e ∧ (e*a).gcd g=e ∧ a.Coprime v := by
    have H := mem_filter.mp ha
    exact ⟨(mem_Ioc.mp H.1).1,(mem_Ioc.mp H.1).2,H.2.1,H.2.2⟩
  have infoJ {z : ℤ} (hz : z ∈ J) : z ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (z : ZMod v) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hz
  have copJ {z : ℤ} (hz : z ∈ J) : z.toNat.Coprime v := by
    have z0 := (mem_Ioc.mp (infoJ hz).1).1.le
    have ca : (z.toNat : ZMod v) = (z : ZMod v) := by
      simpa only [Int.cast_natCast] using congrArg (fun j : ℤ => (j : ZMod v)) (Int.toNat_of_nonneg z0)
    exact (ZMod.isUnit_iff_coprime _ _).mp (ca.symm ▸ (infoJ hz).2)
  have baseEq (a j : ℕ) : e*a*(h*j) = g*(a*j) := by rw [← hd]; ring
  have aBounds (a : ℕ) : (aLo/e < a ∧ a ≤ aHi/e) ↔ aLo < e*a ∧ e*a ≤ aHi := by
    rw [Nat.div_lt_iff_lt_mul e0,Nat.le_div_iff_mul_le e0,Nat.mul_comm a e]
  have prodBounds (u : ℕ) : (l < u ∧ u ≤ r) ↔ l₀ < g*u ∧ g*u ≤ r₀ := by
    change l₀/g < u ∧ u ≤ r₀/g ↔ _
    rw [Nat.div_lt_iff_lt_mul g0,Nat.le_div_iff_mul_le g0,Nat.mul_comm u g]
  have prodScaled (a j : ℕ) : e*a*(h*j)/g=a*j := by rw [baseEq,Nat.mul_div_cancel_left _ g0]
  have gateBounds {a : ℕ} (a0 : 0 < a) {z : ℤ} (z0 : 0 < z) (zn : z.toNat ≤ n) :
      gate a z ↔ (l < a*z.toNat ∧ a*z.toNat ≤ r) ∧
        (cutoffB n < h*z.toNat ∧ h*z.toNat ≤ min (splitCut n) (n/(rightLargeCofactorCut n+1))) ∧
        swappedHighPrefixLower n e a ≤ (n/g-m/g)/(a*z.toNat) :=
    swapped_high_full_gate_iff a0 z0 h0 zn
  have lift_mem (t : ℤ × ℕ) (ht : t ∈ P) : liftPoint t ∈ largeHighProductSelection n row g e k := by
    obtain ⟨hj,ha⟩ := mem_product.mp (mem_filter.mp ht).1
    obtain ⟨al,au,ag,ac⟩ := infoI ha
    have a0 := (Nat.zero_le _).trans_lt al
    have zR := mem_Ioc.mp (infoJ hj).1
    have jN : t.1.toNat ≤ n := (show t.1.toNat ≤ S by have := zR.2; omega).trans sN
    have ab := (aBounds t.2).mp ⟨al,au⟩
    have ⟨prod,kBounds,act⟩ := (gateBounds a0 zR.1 jN).mp (mem_filter.mp ht).2
    have pb := (prodBounds _).mp prod
    rw [← baseEq] at pb
    have bN : e*t.2 ≤ n := (show e*t.2 ≤ e*t.2*(h*t.1.toNat) by
      have j0 : 0 < t.1.toNat := by omega
      simpa only [mul_one] using Nat.mul_le_mul_left (e*t.2) (show 1 ≤ h*t.1.toNat from mul_pos h0 j0)).trans
        (pb.2.trans rN)
    have acj : (t.2*t.1.toNat).Coprime v := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa only [Nat.cast_mul] using ((ZMod.isUnit_iff_coprime _ _).mpr ac).mul
        ((ZMod.isUnit_iff_coprime _ _).mpr (copJ hj))
    have gcd : (swappedHighGroupedStep (liftPoint t)).gcd m=g := by
      change (e*t.2*(h*t.1.toNat)).gcd m=g
      rw [baseEq,← gV,Nat.gcd_mul_left,acj.gcd_eq_one,mul_one]
    have grouped : liftPoint t ∈ groupedRightHighItems n := by
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ioc.mpr kBounds,mem_Icc.mpr ⟨mul_pos e0 a0,bN⟩⟩,?_⟩
      change h*t.1.toNat*(e*t.2) ≤ n
      rw [mul_comm]
      exact pb.2.trans rN
    have acc : rightLargeCofactorCut n/(e*t.2) ≤ (n/g-m/g)/(e*t.2*(h*t.1.toNat)/g) := by
      rw [prodScaled]
      exact act
    exact mem_filter.mpr ⟨grouped,mem_Ioc.mpr ab,gcd,ag,pb.1,pb.2,acc⟩
  have lift_surj (t : ℕ × ℕ) (ht : t ∈ largeHighProductSelection n row g e k) :
      ∃ z ∈ P, liftPoint z=t := by
    obtain ⟨grouped,fac,gcd,egcd,upL,upR,activity⟩ := mem_filter.mp ht
    change (t.2*t.1).gcd m=g at gcd
    have eA : e ∣ t.2 := egcd ▸ Nat.gcd_dvd_left t.2 g
    have gU : g ∣ t.2*t.1 := gcd ▸ Nat.gcd_dvd_left (t.2*t.1) m
    have hJ : h ∣ t.1 := by
      have flat := (divide_left_product_of_gcd g0 gU).1
      rw [egcd] at flat
      exact flat
    let a := t.2/e
    let j := t.1/h
    have ea : e*a=t.2 := Nat.mul_div_cancel' eA
    have hj : h*j=t.1 := Nat.mul_div_cancel' hJ
    have aB : aLo/e < a ∧ a ≤ aHi/e := (aBounds a).mpr (by rw [ea]; exact mem_Ioc.mp fac)
    have a0 := (Nat.zero_le _).trans_lt aB.1
    have kBounds := mem_Ioc.mp (mem_product.mp (mem_filter.mp grouped).1).1
    have j0 : 0 < j := Nat.div_pos (Nat.le_of_dvd ((Nat.zero_le _).trans_lt kBounds.1) hJ) h0
    have poly : t.2*t.1=g*(a*j) := by rw [← baseEq,ea,hj]
    have ab : l < a*j ∧ a*j ≤ r := (prodBounds _).mpr (by rw [← poly]; exact ⟨upL,upR⟩)
    have jS : j ≤ S := (Nat.le_div_iff_mul_le (Nat.succ_pos (aLo/e))).mpr
      (by rw [Nat.mul_comm]; exact (Nat.mul_le_mul_right j aB.1).trans ab.2)
    have cop : (a*j).Coprime v := by
      have core : (t.2*t.1/(t.2*t.1).gcd m).Coprime (m/(t.2*t.1).gcd m) :=
        Nat.coprime_div_gcd_div_gcd (gcd.symm ▸ g0)
      rw [gcd,poly,Nat.mul_div_cancel_left _ g0] at core
      exact core
    have aI : a ∈ I := mem_filter.mpr ⟨mem_Ioc.mpr aB,by rw [ea]; exact egcd,cop.coprime_dvd_left (dvd_mul_right _ _)⟩
    have jJ : (j : ℤ) ∈ J := by
      have unit : IsUnit ((j : ℤ) : ZMod v) := by
        rw [Int.cast_natCast]
        exact (ZMod.isUnit_iff_coprime _ _).mpr (cop.coprime_dvd_left (dvd_mul_left _ _))
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by exact_mod_cast j0,by exact_mod_cast jS⟩,unit⟩
    have act : swappedHighPrefixLower n e a ≤ (n/g-m/g)/(a*j) := by
      change rightLargeCofactorCut n/t.2 ≤ (n/g-m/g)/(t.2*t.1/g) at activity
      rw [poly,Nat.mul_div_cancel_left _ g0] at activity
      unfold swappedHighPrefixLower
      rwa [ea]
    have jG : gate a (j : ℤ) := (gateBounds a0 (by exact_mod_cast j0) (by
      simpa only [Int.toNat_natCast] using jS.trans sN)).mpr
        (by simp only [Int.toNat_natCast,hj]; exact ⟨ab,kBounds,act⟩)
    exact ⟨((j : ℤ),a),mem_filter.mpr ⟨mem_product.mpr ⟨jJ,aI⟩,jG⟩,
      Prod.ext (by simpa only [liftPoint,Int.toNat_natCast] using hj) ea⟩
  have eval (t : ℤ × ℕ) (ht : t ∈ P) : W t=value (liftPoint t) := by
    obtain ⟨_,_,alg,_,step,_,activity⟩ := mem_filter.mp (lift_mem t ht)
    let v₀ := e*t.2*(h*t.1.toNat)
    have loose : expandedHighModulusCap n ≤ l₀ :=
      le_max_left _ _
    have mv : m < v₀ := (modTop.trans loose).trans_lt step
    have htJ := (mem_product.mp (mem_filter.mp ht).1).1
    have z0 := (mem_Ioc.mp (infoJ htJ).1).1
    have ca : (t.1.toNat : ZMod v) = (t.1 : ZMod v) := by
      simpa only [Int.cast_natCast] using congrArg (fun j : ℤ => (j : ZMod v)) (Int.toNat_of_nonneg z0.le)
    have E := swapped_capped_residue_two_prefixes (n := n) (b := swappedHighPrefixLower n e t.2)
      m0 mv mN (show v₀.gcd m ∣ n from alg.symm ▸ gn)
    dsimp only at E
    change v₀.gcd m=g at alg
    change swappedHighPrefixLower n e t.2 ≤ (n/g-m/g)/(v₀/g) at activity
    rw [alg,ite_eq_left activity,show v₀/g=t.2*t.1.toNat from prodScaled _ _,Int.natCast_ediv] at E
    unfold W value swappedHighGroupedResidue
    change _ * (F t.2 t.1 _ - F t.2 t.1 _) =
      _ * (pairResidueError n v₀ m (swappedHighPrefixLower n e t.2) (n/v₀) 0 (n/m) : ℂ)
    rw [E]
    unfold F
    have phase : ((t.2*t.1.toNat : ℕ) : ZMod v) = (t.2 : ZMod v)*(t.1 : ZMod v) := by
      rw [Nat.cast_mul,ca]
    rw [phase]
  have eq : largeHighProductWindow n row g e k = ∑ t ∈ P, W t := by
    change gatedBilinearSum I J (fun a => (rightHighWaveFactor n (e*a) : ℂ))
        (fun j => groupedRightHighMoebius n (h*j.toNat)) lo hi
          (fun a j => F a j (((n/g-m/g : ℕ) : ℤ)/((a*j.toNat : ℕ) : ℤ))) -
      gatedBilinearSum I J (fun a => (rightHighWaveFactor n (e*a) : ℂ))
        (fun j => groupedRightHighMoebius n (h*j.toNat)) lo hi
          (fun a j => F a j (swappedHighPrefixLower n e a)) = _
    rw [gated_bilinear_sum_eq_pair_sum,gated_bilinear_sum_eq_pair_sum,← sum_sub_distrib]
    unfold P
    rw [sum_filter,sum_product]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    change (ite (gate a j) _ 0 - ite (gate a j) _ 0) = ite (gate a j) _ 0
    by_cases hG : gate a j
    · rw [ite_eq_left hG,ite_eq_left hG,ite_eq_left hG]
      simp only [W,liftPoint,swappedHighGroupedWeight,← mul_sub]
    · simp only [ite_eq_right hG,sub_zero]
  rw [eq]
  refine sum_bij (fun t _ => liftPoint t) lift_mem ?_ ?_ eval
  swap
  · intro i hi
    obtain ⟨t,ht,eqt⟩ := lift_surj i hi
    exact ⟨t,ht,eqt⟩
  intro t ht u hu heq
  have positive {x : ℤ × ℕ} (hx : x ∈ P) : 0 ≤ x.1 :=
    (mem_Ioc.mp (infoJ (mem_product.mp (mem_filter.mp hx).1).1).1).1.le
  have fst : h*t.1.toNat=h*u.1.toNat := congrArg Prod.fst heq
  have snd : e*t.2=e*u.2 := congrArg Prod.snd heq
  have jEq := Nat.eq_of_mul_eq_mul_left h0 fst
  exact Prod.ext (by rw [← Int.toNat_of_nonneg (positive ht),← Int.toNat_of_nonneg (positive hu),jEq])
    (Nat.eq_of_mul_eq_mul_left e0 snd)

end

end B13BoundedStepProductSavingProof

end

/- Large high product row def -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def largeHighProductRow (n : ℕ) (j : (ℕ × ℕ)) : ℂ :=
  ∑ g ∈ swappedHighDivisors n (leftBilinearStep j), ∑ e ∈ g.divisors, ∑ k ∈ Icc 256 10879,
    largeHighProductWindow n j g e k

def largeHighProductResidueSlice (n : ℕ) : ℂ :=
  ∑ j ∈ outerRightRows n, leftBilinearWeight n j*largeHighProductRow n j

end

end B13BoundedStepProductSavingProof

end

/- Large high product row selection -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

def largeHighProductRowItems (n : ℕ) (row : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  let m := leftBilinearStep row
  (groupedRightHighItems n).filter fun t =>
    let v := swappedHighGroupedStep t
    let g := v.gcd m
    g ∈ swappedHighDivisors n m ∧
      largeHighProductStepLower n row < v ∧ v ≤ highFarStripStepUpper n m ∧
      t.2 ∈ Ioc (highFarStripFactorCut n) (outerRightFactorCap n) ∧
      rightLargeCofactorCut n/t.2 ≤ (n/g-m/g)/(v/g)

theorem large_high_product_row_eq_grouped_selected {n : ℕ} {row : ℕ × ℕ}
    (hr : row ∈ outerRightRows n) :
    largeHighProductRow n row = ∑ t ∈ largeHighProductRowItems n row,
      swappedHighGroupedResidue n (leftBilinearStep row) t := by
  let m := leftBilinearStep row
  let I := largeHighProductRowItems n row
  let G := swappedHighDivisors n m
  let K := Icc 256 10879
  let d (t : ℕ × ℕ) := (swappedHighGroupedStep t).gcd m
  let w := swappedHighGroupedResidue n m
  have range := mem_Icc.mp (bilateral_left_step_range (mem_filter.mp hr).1)
  have n1 : 1 ≤ n := range.1.trans range.2
  have mapsG : ∀ t ∈ I, d t ∈ G := fun _ ht => (mem_filter.mp ht).2.1
  change largeHighProductRow n row = ∑ t ∈ I, w t
  rw [← sum_fiberwise_of_maps_to mapsG w]
  unfold largeHighProductRow
  refine sum_congr rfl fun g hg => ?_
  let I₁ := I.filter fun t => d t=g
  let aGcd (t : ℕ × ℕ) := t.2.gcd g
  have gData := mem_filter.mp hg
  have gn := (Nat.mem_divisors.mp gData.1).1
  have g0 := Nat.pos_of_dvd_of_pos gn n1
  have gm := gData.2.2.2
  have mapsE : ∀ t ∈ I₁, aGcd t ∈ g.divisors :=
    fun t _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right t.2 g,g0.ne'⟩
  change (∑ e ∈ g.divisors, ∑ k ∈ K, largeHighProductWindow n row g e k) = ∑ t ∈ I₁, w t
  rw [← sum_fiberwise_of_maps_to mapsE w]
  refine sum_congr rfl fun e he => ?_
  let I₂ := I₁.filter fun t => aGcd t=e
  have eg := (Nat.mem_divisors.mp he).1
  have e0 := Nat.pos_of_dvd_of_pos eg g0
  have eqFilter (k : ℕ) : largeHighProductSelection n row g e k =
      I₂.filter (fun t => t.2 ∈ highFarStripFactorBlock n k) := by
    ext t
    constructor
    · intro ht
      obtain ⟨base,fac,gg,ee,lo,up,activity⟩ := mem_filter.mp ht
      have dG : d t ∈ G := by change (swappedHighGroupedStep t).gcd m ∈ G; rw [gg]; exact hg
      have facTop : t.2 ∈ Ioc (highFarStripFactorCut n) (outerRightFactorCap n) :=
        mem_Ioc.mpr ⟨(le_max_left _ _).trans_lt (mem_Ioc.mp fac).1,
          (mem_Ioc.mp fac).2.trans (min_le_left _ _)⟩
      have act : rightLargeCofactorCut n/t.2 ≤ (n/(d t)-m/(d t))/(swappedHighGroupedStep t/(d t)) := by
        change d t=g at gg
        rwa [gg]
      have tI : t ∈ I := mem_filter.mpr ⟨base,dG,lo,up,facTop,act⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨tI,gg⟩,ee⟩,fac⟩
    · intro ht
      obtain ⟨ht₂,fac⟩ := mem_filter.mp ht
      obtain ⟨ht₁,ee⟩ := mem_filter.mp ht₂
      obtain ⟨ht₀,gg⟩ := mem_filter.mp ht₁
      obtain ⟨base,_,lo,up,_,act⟩ := mem_filter.mp ht₀
      have act' : rightLargeCofactorCut n/t.2 ≤ (n/g-m/g)/(swappedHighGroupedStep t/g) := by
        change rightLargeCofactorCut n/t.2 ≤ (n/(d t)-m/(d t))/(swappedHighGroupedStep t/(d t)) at act
        rwa [gg] at act
      exact mem_filter.mpr ⟨base,fac,gg,ee,lo,up,act'⟩
  calc
    (∑ k ∈ K, largeHighProductWindow n row g e k) =
        ∑ k ∈ K, ∑ t ∈ I₂.filter (fun t => t.2 ∈ highFarStripFactorBlock n k), w t := by
      refine sum_congr rfl fun k _ => ?_
      rw [← eqFilter k]
      exact large_high_product_window_eq_grouped_sum hr g0 gn gm e0 eg
    _ = ∑ t ∈ I₂, ∑ k ∈ K, if t.2 ∈ highFarStripFactorBlock n k then w t else 0 := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = ∑ t ∈ I₂, w t := by
      refine sum_congr rfl fun t ht => ?_
      have ht₀ : t ∈ I := (mem_filter.mp (mem_filter.mp ht).1).1
      have aRange := (mem_filter.mp ht₀).2.2.2.2.1
      obtain ⟨k,⟨kMem,hk⟩,unique⟩ := high_far_strip_factor_blocks_cover n1 aRange
      rw [sum_eq_single_of_mem k kMem]
      · exact ite_eq_left hk
      · intro k' hk' neq
        exact ite_eq_right (fun h => neq (unique k' ⟨hk',h⟩))

end

end B13BoundedStepProductSavingProof

end

/- Large high product grouped -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def largeHighProductGrouped (n : ℕ) (row : ℕ × ℕ) : ℂ :=
  ∑ t ∈ groupedRightHighItems n,
    if largeHighProductGate n row (swappedHighGroupedStep t) then
      swappedHighGroupedResidue n (leftBilinearStep row) t else 0

private theorem large_high_product_row_membership {n : ℕ} {row t : ℕ × ℕ}
    (hr : row ∈ outerRightRows n) (ht : t ∈ groupedRightHighItems n) :
    t ∈ largeHighProductRowItems n row ↔
      let u := leftBilinearStep row
      let v := swappedHighGroupedStep t
      let g := v.gcd u
      largeHighProductGate n row v ∧ g ∣ n ∧ highFarStripFactorCut n < t.2 ∧
        rightLargeCofactorCut n/t.2 ≤ (n/g-u/g)/(v/g) := by
  dsimp only
  let u := leftBilinearStep row
  let v := swappedHighGroupedStep t
  let g := v.gcd u
  have data := mem_filter.mp hr
  have uRange := mem_Icc.mp (bilateral_left_step_range data.1)
  have u0 : 0 < u := uRange.1
  have n0 : 0 < n := u0.trans_le uRange.2
  have uTop : u ≤ extendedWideStepCap n :=
    (high_step_le_medium_of_square_le u0 data.2.1).trans (old_step_cap_le_extended n)
  have char : u.gcd n ≤ thinHighLeftDivisorCap n := data.2.2.2
  have group := mem_product.mp (mem_filter.mp ht).1
  have v0 : 0 < v := mul_pos (mem_Icc.mp group.2).1 ((Nat.zero_le _).trans_lt (mem_Ioc.mp group.1).1)
  constructor
  · intro h
    obtain ⟨_,gMem,lo,up,band,active⟩ := mem_filter.mp h
    obtain ⟨div,small,gMax,_⟩ := mem_filter.mp gMem
    obtain ⟨cap,large,pfx,thin,prod⟩ := (large_high_product_step_gate_iff u0).mp ⟨lo,up⟩
    have small' : u.gcd v ≤ thinHighGcdCap n := by rwa [Nat.gcd_comm]
    have gMax' : u.gcd v ≤ maximumStep n := by rwa [Nat.gcd_comm]
    exact ⟨⟨uTop,cap,large,⟨pfx,gMax'⟩,thin,prod,small',char⟩,
      (Nat.mem_divisors.mp div).1,(mem_Ioc.mp band).1,active⟩
  · rintro ⟨⟨_,vTop,vLo,pfx,thin,prod,small,_⟩,gn,factor,active⟩
    have ⟨lo,up⟩ := (large_high_product_step_gate_iff u0).mpr ⟨vTop,vLo,pfx.1,thin,prod⟩
    have div : g ∈ swappedHighDivisors n u := by
      refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨gn,n0.ne'⟩,?_,?_,Nat.gcd_dvd_right _ _⟩
      · simpa only [g,Nat.gcd_comm] using small
      · simpa only [g,Nat.gcd_comm] using pfx.2
    have bTop : t.2 ≤ outerRightFactorCap n :=
      grouped_right_high_factor_le_outer_cap ht (by simpa only [v,swappedHighGroupedStep,Nat.mul_comm] using vTop)
    exact mem_filter.mpr ⟨ht,div,lo,up,mem_Ioc.mpr ⟨factor,bTop⟩,active⟩

theorem large_high_product_row_eq_grouped {n : ℕ} {row : ℕ × ℕ} (hr : row ∈ outerRightRows n) :
    largeHighProductRow n row = largeHighProductGrouped n row := by
  rw [large_high_product_row_eq_grouped_selected hr]
  unfold largeHighProductRowItems largeHighProductGrouped
  simp_rw [sum_filter]
  refine sum_congr rfl fun t ht => ?_
  let u := leftBilinearStep row
  let v := swappedHighGroupedStep t
  let g := v.gcd u
  let P := largeHighProductGate n row v
  let W := swappedHighGroupedResidue n u t
  have iff := large_high_product_row_membership hr ht
  simp only [largeHighProductRowItems,mem_filter,ht,true_and] at iff
  by_cases gate : P
  · by_cases gd : g ∣ n
    · by_cases fac : highFarStripFactorCut n < t.2
      · by_cases active : rightLargeCofactorCut n/t.2 ≤ (n/g-u/g)/(v/g)
        · have p := iff.mpr ⟨gate,gd,fac,active⟩
          rw [ite_eq_left p,ite_eq_left gate]
        · have z : W = 0 := by
            have data := mem_filter.mp hr
            have rg := mem_Icc.mp (bilateral_left_step_range data.1)
            have n0 := rg.1.trans rg.2
            have mLo : u < v := (square_le_implies_step_le_expanded_high_cap rg.1 data.2.1).trans_lt gate.2.2.1
            have f := swapped_capped_residue_two_prefixes (b := rightLargeCofactorCut n/t.2)
              (show 0 < u from rg.1) mLo (show u ≤ n from rg.2) gd
            dsimp only at f
            rw [ite_eq_right active] at f
            change swappedHighGroupedWeight n t *
              (pairResidueError n v u (rightLargeCofactorCut n/t.2) (n/v) 0 (n/u) : ℂ) = 0
            rw [f,mul_zero]
          change (if _ then W else 0) = (if P then W else 0)
          simp [z]
      · have z : W = 0 := by
          have zero := right_high_wave_factor_eq_zero_of_rpow_cut (n := n) (not_lt.mp fac)
          unfold W swappedHighGroupedResidue swappedHighGroupedWeight
          simp [zero]
        change (if _ then W else 0) = (if P then W else 0)
        simp [z]
    · have z : W = 0 := by
        unfold W swappedHighGroupedResidue pairResidueError
        simp [g,u,v,gd]
      change (if _ then W else 0) = (if P then W else 0)
      simp [z]
  · have neq : ¬_ := fun h => gate (iff.mp h).1
    rw [ite_eq_right neq,ite_eq_right gate]

def largeHighProductGroupSum (n : ℕ) : ℂ :=
  ∑ row ∈ bilateralLeftWaveItems n, leftBilinearWeight n row*largeHighProductGrouped n row

theorem large_high_product_slice_eq_full (n : ℕ) (large : (2 : ℝ) ≤ (n : ℝ)^(1/1024 : ℝ)) :
    largeHighProductResidueSlice n = largeHighProductGroupSum n := by
  unfold largeHighProductResidueSlice largeHighProductGroupSum
  calc
    _ = ∑ row ∈ outerRightRows n, leftBilinearWeight n row*largeHighProductGrouped n row := by
      refine sum_congr rfl fun row hr => ?_
      rw [large_high_product_row_eq_grouped hr]
    _ = _ := sum_subset (filter_subset _ _) (fun row hr missing => by
      have zero : largeHighProductGrouped n row = 0 := by
        unfold largeHighProductGrouped
        refine sum_eq_zero fun t _ => ?_
        exact ite_eq_right (fun gate => missing (large_high_product_row_mem large hr gate))
      simp [zero])

end

end B13BoundedStepProductSavingProof

end

/- Large high product wave conversion -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

def largeHighProductWaveSum (n : ℕ) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ rightHighWaveItems n,
    if largeHighProductGate n i (rightHighWaveStep j) then
      leftBilinearWeight n i*rightHighWaveWeight n j*
        (pairResidueError n (rightHighWaveStep j) (leftBilinearStep i)
          (rightHighWaveLower n j) (n/rightHighWaveStep j) 0 (n/leftBilinearStep i) : ℂ)
    else 0

theorem large_high_product_wave_sum_eq_grouped (n : ℕ) :
    largeHighProductWaveSum n = largeHighProductGroupSum n := by
  unfold largeHighProductWaveSum largeHighProductGroupSum largeHighProductGrouped
  refine sum_congr rfl fun i _ => ?_
  let m := leftBilinearStep i
  let f (t : ℕ × ℕ) : ℂ :=
    let v := swappedHighGroupedStep t
    if largeHighProductGate n i v then
      (pairResidueError n v m (rightLargeCofactorCut n/t.2) (n/v) 0 (n/m) : ℂ) else 0
  have eq (j : RightHighWaveIndex) : swappedHighGroupedStep (rightHighGroupingKey j) = rightHighWaveStep j :=
    Nat.mul_comm _ _
  calc
    _ = leftBilinearWeight n i*∑ j ∈ rightHighWaveItems n, rightHighWaveWeight n j*f (rightHighGroupingKey j) := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      unfold f
      dsimp only
      rw [eq j]
      by_cases h : largeHighProductGate n i (rightHighWaveStep j) <;>
        simp [h, rightHighWaveLower, rightHighGroupingKey, m, mul_assoc]
    _ = _ := by
      rw [sum_right_high_wave_by_grouped_factors]
      apply congrArg (leftBilinearWeight n i * ·)
      refine sum_congr rfl fun t _ => ?_
      unfold f swappedHighGroupedResidue
      dsimp only
      by_cases h : largeHighProductGate n i (swappedHighGroupedStep t) <;> simp [h, m, swappedHighGroupedWeight, mul_comm]

def originalLargeHighProductWaveSum (n : ℕ) : ℂ :=
  highResidueSum n fun i j => largeHighProductGate n i (rightHighWaveStep j)

def largeHighProductVolumeCorrection (n : ℕ) : ℂ :=
  pairResidueSwapFamily n (thinHighLeftItems n) (outerRightHighItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightHighWaveStep (rightHighWaveLower n) (fun j => n/rightHighWaveStep j)
    (leftBilinearWeight n) (rightHighWaveWeight n)
    (fun i j => largeHighProductGate n i (rightHighWaveStep j))

private theorem sum_large_high_product_under_step_cap (n : ℕ)
    (f : (ℕ × ℕ) → RightHighWaveIndex → ℂ) :
    (∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ rightHighWaveItems n,
      if largeHighProductGate n i (rightHighWaveStep j) then f i j else 0) =
    ∑ i ∈ thinHighLeftItems n, ∑ j ∈ outerRightHighItems n,
      if largeHighProductGate n i (rightHighWaveStep j) then f i j else 0 := by
  unfold thinHighLeftItems outerRightHighItems extendedWaveItems expandedWaveItems
  simp_rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  by_cases hu : leftBilinearStep i ≤ extendedWideStepCap n
  · rw [ite_eq_left hu]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : largeHighProductGate n i (rightHighWaveStep j)
    · simp [h,h.2.1]
    · simp [h]
  · rw [ite_eq_right hu]
    refine sum_eq_zero fun j _ => ?_
    exact ite_eq_right (fun h => hu h.1)

theorem original_large_high_product_eq_swapped_add_correction (n : ℕ) :
    originalLargeHighProductWaveSum n = largeHighProductWaveSum n + largeHighProductVolumeCorrection n := by
  unfold originalLargeHighProductWaveSum highResidueSum largeHighProductWaveSum
  rw [sum_large_high_product_under_step_cap n, sum_large_high_product_under_step_cap n]
  unfold largeHighProductVolumeCorrection pairResidueSwapFamily
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  unfold highResidueTerm
  split_ifs <;> ring

end

end B13BoundedStepProductSavingProof

end

/- Large high product window budget -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

set_option maxHeartbeats 2500000 in
theorem norm_large_high_product_window_le {n g e k : ℕ} {row : ℕ × ℕ}
    (hrow : row ∈ outerRightRows n)
    (gpos : 0 < g) (gn : g ∣ n) (gm : g ∣ leftBilinearStep row) (gSmall : g ≤ thinHighGcdCap n)
    (e0 : 0 < e) (eg : e ∣ g) (hk : k ∈ Icc 256 10879) (ns : 1 < n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖largeHighProductWindow n row g e k‖ ≤
      690*(n : ℝ)^(4095/4096 : ℝ)*T^3*logBudget n^3/(leftBilinearStep row : ℝ) := by
  let m := leftBilinearStep row
  let v := m/g
  let N := (n : ℝ)
  let M := (m : ℝ)
  let V := (v : ℝ)
  let G := (g : ℝ)
  let E := (e : ℝ)
  let y := (k : ℝ)/32768
  let x := y-1/4096
  let A := swappedHighFactorFloor n (k+1)/e
  let aLo := highFarStripFactorLower n k
  let S := highFarStripCofactorCap n m g e k
  let I := highFarStripFactors n m g e k
  let J := intIntervalModUnits v 0 S
  let mLo := largeHighProductStepLower n row
  let mHi := highFarStripStepUpper n m
  let l := mLo/g
  let r := mHi/g
  let L := logBudget n
  let α (a : ℕ) : ℂ := rightHighWaveFactor n (e*a)
  let β (j : ℤ) : ℂ := groupedRightHighMoebius n ((g/e)*j.toNat)
  let baseLo (_ : ℕ) := swappedHighTailLower n g e
  let baseHi := swappedHighTailUpper n m g e
  let num := n/g-m/g
  have numN : num ≤ n/g := Nat.sub_le _ _
  have right : row ∈ bilateralLeftWaveItems n := (mem_filter.mp hrow).1
  obtain ⟨sq,origLo,charTop⟩ := (mem_filter.mp hrow).2
  have step := mem_Icc.mp (bilateral_left_step_range right)
  have m0 : 0 < m := step.1
  have mN : m ≤ n := step.2
  have v0 : 0 < v := Nat.div_pos (Nat.le_of_dvd m0 gm) gpos
  let _ : NeZero v := ⟨v0.ne'⟩
  have vprod : v*g=m := Nat.div_mul_cancel gm
  have npNat : 0 < n := zero_lt_one.trans ns
  have nr : 1 < N := show (1 : ℝ) < (n : ℝ) from by exact_mod_cast ns
  have np : 0 < N := zero_lt_one.trans nr
  have gp : 0 < G := show (0 : ℝ) < (g : ℝ) from by exact_mod_cast gpos
  have G1 : 1 ≤ G := show (1 : ℝ) ≤ (g : ℝ) from by exact_mod_cast gpos
  have vN : v ≤ n := (by simpa only [mul_one] using Nat.mul_le_mul_left v (show 1 ≤ g from gpos) : v ≤ v*g).trans
    (by rw [vprod]; exact mN)
  have vEq : V*G=M := by
    change (v : ℝ)*(g : ℝ) = (m : ℝ)
    exact_mod_cast vprod
  have origHi : M ≤ N^(1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.le_sqrt (by positivity) np.le).mpr
    change (m : ℝ)^2 ≤ (n : ℝ)
    exact_mod_cast sq
  have castGcd : (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ N^(1/2048 : ℝ) := by
    have vd : v ∣ m := ⟨g,vprod.symm⟩
    have nd : n/g ∣ n := ⟨g,(Nat.div_mul_cancel gn).symm⟩
    have d : v.gcd (n/g) ∣ m.gcd n := Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans vd) ((Nat.gcd_dvd_right _ _).trans nd)
    have relation := (gcd_val_nat_cast_le_gcd (m := v) (n/g)).trans
      ((Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ npNat) d).trans charTop)
    exact (show (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ (thinHighLeftDivisorCap n : ℝ) by
      exact_mod_cast relation).trans (Nat.floor_le (by positivity))
  have vHi : V ≤ N^(1/2 : ℝ) := by
    have h : V ≤ M := by
      rw [← vEq]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left G1 (by positivity : 0 ≤ V)
    exact h.trans origHi
  have gReal : G ≤ (thinHighGcdCap n : ℝ) := by
    change (g : ℝ) ≤ (thinHighGcdCap n : ℝ)
    exact_mod_cast gSmall
  have gCap : G ≤ N^(1/4096 : ℝ) :=
    gReal.trans (Nat.floor_le (Real.rpow_nonneg np.le _))
  have egNat : e ≤ g := Nat.le_of_dvd gpos eg
  have egReal : E ≤ G := by
    change (e : ℝ) ≤ (g : ℝ)
    exact_mod_cast egNat
  have eCap : E ≤ N^(1/4096 : ℝ) := egReal.trans gCap
  have vLo : N^(1/3 : ℝ) < V := by
    apply (mul_lt_mul_iff_left₀ gp).mp
    calc
      _ ≤ N^(1/3 : ℝ)*N^(1/4096 : ℝ) := mul_le_mul_of_nonneg_left gCap (by positivity)
      _ < N^(171/512 : ℝ) := by rw [← Real.rpow_add np]; exact Real.rpow_lt_rpow_of_exponent_lt nr (by norm_num)
      _ ≤ M := origLo
      _ = _ := vEq.symm
  obtain ⟨kminNat, kmaxNat⟩ : 256 ≤ k ∧ k ≤ 10879 := mem_Icc.mp hk
  have kmin : (256 : ℝ) ≤ k := by exact_mod_cast kminNat
  have kmax : (k : ℝ) ≤ 10879 := by exact_mod_cast kmaxNat
  have xLo : 31/4096 ≤ x := by unfold x y; linarith only [kmin]
  have xHi : x ≤ 1/3 := by unfold x y; linarith only [kmax]
  have aFormula : swappedHighFactorFloor n (k+1) = ⌊N^(x+9/32768)⌋₊ := by
    unfold swappedHighFactorFloor N x y
    rw [Nat.cast_add,Nat.cast_one,add_div]
    congr 2
    ring
  have aCap : (A : ℝ) ≤ N^(x+9/32768) :=
    (by exact_mod_cast Nat.div_le_self (swappedHighFactorFloor n (k+1)) e :
      (A : ℝ) ≤ (swappedHighFactorFloor n (k+1) : ℝ)).trans (by rw [aFormula]; exact Nat.floor_le (by positivity))
  have A1 : 0 < A := by
    change 1 ≤ swappedHighFactorFloor n (k+1)/e
    apply (Nat.le_div_iff_mul_le e0).mpr
    rw [one_mul,aFormula]
    exact Nat.le_floor (eCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by linarith only [xLo])))
  have aQ : (A : ℝ) ≤ N^(1/3 : ℝ) :=
    aCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by unfold x y; linarith only [kmax]))
  have Av : A < v := by
    have h := aQ.trans_lt vLo
    change (A : ℝ) < (v : ℝ) at h
    exact_mod_cast h
  have Icap : I ⊆ Icc 1 A := by
    intro a ha
    have h := mem_Ioc.mp (mem_filter.mp ha).1
    exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt h.1,h.2.trans (Nat.div_le_div_right (min_le_right (outerRightFactorCap n) _))⟩
  have copI (a : ℕ) (ha : a ∈ I) : a.Coprime v := (mem_filter.mp ha).2.2
  have rN : mHi ≤ n := (min_le_left _ _).trans (expanded_wide_step_le npNat)
  have rG : r*g ≤ mHi := Nat.div_mul_le_self mHi g
  have sR : S ≤ r := Nat.div_le_self _ _
  have rp : r*v*g^2 ≤ highFarStripProductCap n := calc
    _ = (r*g)*(v*g) := by ring
    _ = (r*g)*m := by rw [vprod]
    _ ≤ mHi*m := Nat.mul_le_mul_right m rG
    _ ≤ (highFarStripProductCap n/m)*m := Nat.mul_le_mul_right m (min_le_right _ _)
    _ ≤ _ := Nat.div_mul_le_self _ _
  have rCap : (r : ℝ)*V*G^2 ≤ 2*N^(4097/4096 : ℝ) := by
    calc
      _ ≤ (highFarStripProductCap n : ℝ) := by
        change (r : ℝ)*(v : ℝ)*(g : ℝ)^2 ≤ (highFarStripProductCap n : ℝ)
        exact_mod_cast rp
      _ ≤ _ := by
        unfold highFarStripProductCap
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
  have cofactorFloor : N^x ≤ (aLo/e : ℕ)+1 := by
    have more : aLo < (aLo/e+1)*e := (Nat.div_lt_iff_lt_mul e0).mp (Nat.lt_succ_self _)
    have rank : (swappedHighFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*E := by
      have le : swappedHighFactorFloor n k+1 ≤ (aLo/e+1)*e :=
        Nat.succ_le_of_lt ((le_max_right _ _).trans_lt more)
      change (swappedHighFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*(e : ℝ)
      exact_mod_cast le
    have ground : N^y ≤ (((aLo/e : ℕ) : ℝ)+1)*E := (Nat.lt_floor_add_one (N^y)).le.trans rank
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (1/4096 : ℝ))).mp
    calc
      _ = N^y := by rw [← Real.rpow_add np]; unfold x; simp
      _ ≤ (((aLo/e : ℕ) : ℝ)+1)*E := ground
      _ ≤ _ := mul_le_mul_of_nonneg_left eCap (by positivity)
  have sCap : (S : ℝ)*V*G^2 ≤ 2*N^(4097/4096-x) := by
    have cut : S*(aLo/e+1) ≤ r := Nat.div_mul_le_self r (aLo/e+1)
    have scaled : (S : ℝ)*(((aLo/e : ℕ) : ℝ)+1) ≤ (r : ℝ) := by exact_mod_cast cut
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np x)).mp
    calc
      _ ≤ ((S : ℝ)*V*G^2)*(((aLo/e : ℕ) : ℝ)+1) :=
        mul_le_mul_of_nonneg_left cofactorFloor (by positivity)
      _ = ((S : ℝ)*(((aLo/e : ℕ) : ℝ)+1))*V*G^2 := by ring
      _ ≤ (r : ℝ)*V*G^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right scaled (by positivity)) (by positivity)
      _ ≤ 2*N^(4097/4096 : ℝ) := rCap
      _ = (2*N^(4097/4096-x))*N^x := by rw [mul_assoc,← Real.rpow_add np,sub_add_cancel]
  have endCap : num/(l+1) ≤ ⌊V*G*N^(1/8192 : ℝ)⌋₊ := by
    have mSub : thinHighProductCap n/m ≤ mLo :=
      (le_max_right _ _).trans (le_max_right _ _)
    have endOrig := swapped_high_endpoint_cap_of_size npNat m0 mSub (le_rfl : n ≤ n)
    have s : mLo+1 ≤ (l+1)*g := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul gpos).mp (Nat.lt_succ_self (mLo/g)))
    rw [vEq]
    calc
      _ ≤ (n/g)/(l+1) := Nat.div_le_div_right numN
      _ = n/((l+1)*g) := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm g (l+1)]
      _ ≤ n/(mLo+1) := Nat.div_le_div_left s (Nat.succ_pos _)
      _ ≤ _ := endOrig
  have divN (z : ℕ) (h : z ≤ n) : (z.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ ns.le (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors z (h.trans nn)
  have divV (z : ℕ) (h : z ≤ 4*v^3) : (z.divisors.card : ℝ) ≤ T :=
    divisors z (h.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left vN 3)))
  have divR (z : ℕ) (h : z ≤ r) : (z.divisors.card : ℝ) ≤ T :=
    divN z (h.trans ((Nat.div_le_self _ _).trans rN))
  have aw (a : ℕ) (ha : a ∈ I) : ‖α a‖ ≤ T*L := by
    have h := (mem_Ioc.mp (mem_filter.mp ha).1).2
    have eLe : e*a ≤ outerRightFactorCap n := by
      have h' := (Nat.le_div_iff_mul_le e0).mp h
      exact (by simpa only [Nat.mul_comm] using h'.trans (min_le_left _ _) : e*a ≤ outerRightFactorCap n)
    have lowN : outerRightFactorCap n ≤ n := by
      have h : (outerRightFactorCap n : ℝ) ≤ (n : ℝ) :=
        (Nat.floor_le (by positivity)).trans (Real.rpow_le_self_of_one_le nr.le (by norm_num))
      exact_mod_cast h
    exact norm_right_high_wave_factor_le (eLe.trans lowN) divN
  have bw (j : ℤ) (hj : j ∈ J) : ‖β j‖ ≤ T := by
    have data : j ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (j : ZMod v) := by
      simpa only [J,intIntervalModUnits,mem_filter] using hj
    have jR : j.toNat ≤ r := (show j.toNat ≤ S by have := (mem_Ioc.mp data.1).2; omega).trans sR
    have h : (g/e)*j.toNat ≤ n := calc
      _ ≤ g*r := Nat.mul_le_mul (Nat.div_le_self g e) jR
      _ ≤ mHi := by simpa only [Nat.mul_comm] using rG
      _ ≤ _ := rN
    exact (norm_grouped_right_high_moebius_le n _).trans (divN _ h)
  have logBound : 1+Real.log V ≤ L := by
    have pv : 0 < V := show (0 : ℝ) < (v : ℝ) from by exact_mod_cast v0
    have up : V ≤ (n : ℝ)+2 := by
      change (v : ℝ) ≤ (n : ℝ)+2
      exact_mod_cast vN.trans (by omega : n≤n+2)
    unfold L logBudget
    linarith only [Real.log_le_log pv up]
  have first := norm_outer_far_ratio_hyperbola_le (m := v) (c := ((n/g : ℕ) : ZMod v)) (g := g)
    castGcd nr.le G1 T1 (one_le_logBudget n) vHi vLo.le gCap xLo xHi logBound aCap sCap rCap endCap
    A1 Av I Icap copI α β baseLo baseHi aw bw divV divR
  let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (baseLo a)
  let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (baseHi a)
  have second := norm_gated_outer_far_fixed_endpoints_le (m := v) (c := ((n/g : ℕ) : ZMod v)) (g := g)
    castGcd nr.le G1 T1 (one_le_logBudget n) vHi vLo.le xLo xHi logBound aCap sCap A1 Av
      I Icap copI α β lo hi (fun _ => 0) (fun a => (swappedHighPrefixLower n e a : ℤ))
      (fun _ _ => by positivity) aw bw divV
  have compare : 98*N^(1023/1024 : ℝ)*T^3*L^3/(V*G^(3/2 : ℝ)) ≤
      98*N^(4095/4096 : ℝ)*T^3*L^3/(V*G) := by
    have h : N^(1023/1024 : ℝ) ≤ N^(4095/4096 : ℝ) := Real.rpow_le_rpow_of_exponent_le nr.le (by norm_num)
    have gpower : G ≤ G^(3/2 : ℝ) := by
      calc
        G = G^(1 : ℝ) := (Real.rpow_one G).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le G1 (by norm_num)
    have L0 : 0 ≤ L := zero_le_one.trans (one_le_logBudget n)
    have T0 : 0 ≤ T := zero_le_one.trans T1
    gcongr <;> positivity
  unfold largeHighProductWindow
  dsimp only
  refine (norm_sub_le _ _).trans ?_
  exact (add_le_add first (second.trans compare)).trans_eq (by
    change 592*N^(4095/4096 : ℝ)*T^3*L^3/(V*G) +
      98*N^(4095/4096 : ℝ)*T^3*L^3/(V*G) = _
    rw [vEq]
    ring)

end

end B13BoundedStepProductSavingProof

end

/- Large high product row bound -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

theorem norm_large_high_product_row_le {n : ℕ} {j : (ℕ × ℕ)}
    (hj : j ∈ outerRightRows n)
    (ns : 1 < n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T)
    (divN : ∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) :
    ‖largeHighProductRow n j‖ ≤
      (10624*(690*(n : ℝ)^(4095/4096 : ℝ)*T^3*logBudget n^3)*T^2)*(1/(leftBilinearStep j : ℝ)) := by
  let B := 690*(n : ℝ)^(4095/4096 : ℝ)*T^3*logBudget n^3
  let M := (leftBilinearStep j : ℝ)
  let V := 10624*B/M
  let G := swappedHighDivisors n (leftBilinearStep j)
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have V0 : 0 ≤ V := by unfold V M B; positivity
  have natCard : G.card ≤ n.divisors.card := card_le_card (filter_subset _ n.divisors)
  have nG : (G.card : ℝ) ≤ T := (show (G.card : ℝ) ≤ (n.divisors.card : ℝ) by exact_mod_cast natCard).trans (divN n le_rfl)
  have per (g : ℕ) (hg : g ∈ G) : ‖∑ e ∈ g.divisors, ∑ k ∈ Icc 256 10879,
      largeHighProductWindow n j g e k‖ ≤ T*V := by
    obtain ⟨data,gS,_,gq⟩ := mem_filter.mp hg
    have gn := (Nat.mem_divisors.mp data).1
    have g0 := Nat.pos_of_dvd_of_pos gn (zero_lt_one.trans ns)
    have en : (g.divisors.card : ℝ) ≤ T := divN g (Nat.le_of_dvd (zero_lt_one.trans ns) gn)
    calc
      _ ≤ ∑ e ∈ g.divisors, ‖∑ k ∈ Icc 256 10879, largeHighProductWindow n j g e k‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ g.divisors, V := by
        refine sum_le_sum fun e he => ?_
        have eg := (Nat.mem_divisors.mp he).1
        have e0 := Nat.pos_of_dvd_of_pos eg g0
        calc
          _ ≤ ∑ k ∈ Icc 256 10879, ‖largeHighProductWindow n j g e k‖ := norm_sum_le _ _
          _ ≤ ∑ _ ∈ Icc 256 10879, B/M := sum_le_sum fun k hk =>
            norm_large_high_product_window_le hj g0 gn gq gS e0 eg hk ns T1 divisors
          _ = V := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,V]; norm_num; ring
      _ = (g.divisors.card : ℝ)*V := by simp only [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right en V0
  change ‖∑ g ∈ G, ∑ e ∈ g.divisors, ∑ k ∈ Icc 256 10879, largeHighProductWindow n j g e k‖ ≤
    (10624*B*T^2)*(1/(leftBilinearStep j : ℝ))
  calc
    _ ≤ ∑ g ∈ G, ‖∑ e ∈ g.divisors, ∑ k ∈ Icc 256 10879, largeHighProductWindow n j g e k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ ∈ G, T*V := sum_le_sum per
    _ = (G.card : ℝ)*(T*V) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ T*(T*V) := mul_le_mul_of_nonneg_right nG (by positivity)
    _ = _ := by unfold V M; ring

end

end B13BoundedStepProductSavingProof

end

/- Large high product saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

private theorem norm_large_high_product_slice_le {n : ℕ} (nBig : 2 ≤ n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖largeHighProductResidueSlice n‖ ≤ 7330560*(n : ℝ)^(4095/4096 : ℝ)*T^8*logBudget n^5 := by
  let L := logBudget n
  let C := n
  let B := 690*(n : ℝ)^(4095/4096 : ℝ)*T^3*L^3
  let W := T^3*L
  let J := outerRightRows n
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have B0 : 0 ≤ B := by unfold B; positivity
  have W0 : 0 ≤ W := by unfold W; positivity
  have n1 : 1 ≤ n := (show 1 ≤ 2 by decide).trans nBig
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have nPos : (0 : ℝ) < n := zero_lt_one.trans_le nR
  have C1 : 1 ≤ C := n1
  have Cn : (C : ℝ) ≤ (n : ℝ) := le_rfl
  have Cnat : C ≤ n := by exact_mod_cast Cn
  have divN (u : ℕ) (h : u ≤ n) : (u.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors u (h.trans nn)
  have ns : 1 < n := nBig
  have massH : (∑ m ∈ Icc 1 C, 1/(m : ℝ)) ≤ L := calc
    _ = (harmonic C : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    _ ≤ 1+Real.log C := by exact_mod_cast harmonic_le_one_add_log C
    _ ≤ L := by
      unfold L logBudget
      exact add_le_add_right (Real.log_le_log (by exact_mod_cast C1)
        (Cn.trans (by linarith : (n : ℝ) ≤ (n : ℝ)+2))) _
  have step (j : (ℕ × ℕ)) (hj : j ∈ J) : leftBilinearStep j ∈ Icc 1 C :=
    bilateral_left_step_range (mem_filter.mp hj).1
  have weighted : (∑ j ∈ J, ‖leftBilinearWeight n j‖*(1/(leftBilinearStep j : ℝ))) ≤ W*L := by
    refine (sum_norm_mul_le_of_step_mass J leftBilinearStep (leftBilinearWeight n) (fun m => 1/(m : ℝ))
      step (fun _ _ => by positivity) ?_).trans (mul_le_mul_of_nonneg_left massH W0)
    intro m hm
    have h : m ∈ Icc 1 n := mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans Cnat⟩
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_left_step_mass (zero_lt_one.trans_le n1) T0 divN m h)
  have each (j : (ℕ × ℕ)) (hj : j ∈ J) :
      ‖largeHighProductRow n j‖ ≤ (10624*B*T^2)*(1/(leftBilinearStep j : ℝ)) := by
    exact norm_large_high_product_row_le hj ns T1 divisors divN
  unfold largeHighProductResidueSlice
  change ‖∑ j ∈ J, leftBilinearWeight n j*largeHighProductRow n j‖ ≤ _
  calc
    _ ≤ ∑ j ∈ J, ‖leftBilinearWeight n j*largeHighProductRow n j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ‖leftBilinearWeight n j‖*((10624*B*T^2)*(1/(leftBilinearStep j : ℝ))) := by
      refine sum_le_sum fun j hj => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (each j hj) (norm_nonneg _)
    _ = (10624*B*T^2)*(∑ j ∈ J, ‖leftBilinearWeight n j‖*(1/(leftBilinearStep j : ℝ))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (10624*B*T^2)*(W*L) := mul_le_mul_of_nonneg_left weighted (by positivity)
    _ = _ := by unfold B W L; ring

theorem large_high_product_residue_saving : saving largeHighProductResidueSlice := by
  intro ε he
  obtain ⟨D,D1,db⟩ := divisor_envelope_at_power 262144 (by decide)
  let C := 7330560*(4*D)^8
  have hlimit : Tendsto (fun n : ℕ => (n : ℝ)^(-(35/262144) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 35/262144)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(35/262144) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlimit
  have bound : ∀ᶠ n : ℕ in atTop, ‖largeHighProductResidueSlice n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_log_budget_le_power (1/262144) (by norm_num),
      hl.eventually_lt_const he] with n nBig logb final
    have hn : 1 ≤ n := (show 1 ≤ (2 : ℕ) by decide).trans nBig
    have nr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have np : (0 : ℝ) < n := zero_lt_one.trans_le nr
    have D0 := zero_le_one.trans D1
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/262144 : ℝ)
    let T := (4*D)*X^3
    have X1 : 1 ≤ X := Real.one_le_rpow nr (by norm_num)
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) D1) (one_le_pow₀ X1)
    have cp : (4 : ℝ)^(1/262144 : ℝ) ≤ 4 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have divs (m : ℕ) (hm : m ≤ 4*n^3) : (m.divisors.card : ℝ) ≤ T := by
      calc
        _ ≤ D*((4*n^3 : ℕ) : ℝ)^(1/(262144 : ℕ) : ℝ) := db (4*n^3) m hm
        _ = D*((4 : ℝ)^(1/262144 : ℝ)*X^3) := by
          push_cast
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul np.le]
          unfold X
          rw [← Real.rpow_mul_natCast np.le]
          norm_num
        _ ≤ D*(4*X^3) := by gcongr
        _ = _ := by unfold T; ring
    have ex : (n : ℝ)^(4095/4096 : ℝ)*X^29 = (n : ℝ)^(-(35/262144) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast np.le, ← Real.rpow_add np, ← Real.rpow_add_one np.ne']
      congr 1
      norm_num
    calc
      _ ≤ 7330560*(n : ℝ)^(4095/4096 : ℝ)*T^8*logBudget n^5 := norm_large_high_product_slice_le nBig T1 divs
      _ ≤ 7330560*(n : ℝ)^(4095/4096 : ℝ)*T^8*X^5 := by gcongr
      _ = C*((n : ℝ)^(4095/4096 : ℝ)*X^29) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(35/262144) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right final.le np.le
  obtain ⟨N,h⟩ := eventually_atTop.mp bound
  exact ⟨N,fun n hn _ => h n hn⟩

end

end B13BoundedStepProductSavingProof

end

/- Large high product wave saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical Finset

noncomputable section

theorem large_high_product_wave_saving : saving largeHighProductWaveSum := by
  intro ε he
  obtain ⟨N,h⟩ := large_high_product_residue_saving ε he
  obtain ⟨M,hm⟩ := eventually_atTop.mp eventually_large_high_product_scale
  refine ⟨max N M,fun n hn even => ?_⟩
  rw [large_high_product_wave_sum_eq_grouped,← large_high_product_slice_eq_full n (hm n (by omega))]
  exact h n (by omega) even

private theorem norm_large_high_product_volume_correction_le {n : ℕ} (n0 : 0 < n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖largeHighProductVolumeCorrection n‖ ≤ 24*(n : ℝ)^(511/768 : ℝ)*T^7*logBudget n^3 := by
  let A := expandedWideStepCap n
  let N := (n : ℝ)
  let L := logBudget n
  let W := T^3*L
  have nr : 0 < N := by change (0 : ℝ) < (n : ℝ); exact_mod_cast n0
  have A0 := expanded_wide_step_pos n0
  have An := expanded_wide_step_le n0
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have W0 : 0 ≤ W := by unfold W; positivity
  have leftRange (i : ℕ × ℕ) (hi : i ∈ thinHighLeftItems n) : leftBilinearStep i ∈ Icc 1 A := by
    obtain ⟨base,cap⟩ := mem_filter.mp hi
    exact mem_Icc.mpr ⟨(mem_Icc.mp (bilateral_left_step_range base)).1,cap.trans (extended_step_cap_le_expanded n)⟩
  have rightRange (j : RightHighWaveIndex) (hj : j ∈ outerRightHighItems n) : rightHighWaveStep j ∈ Icc 1 A := by
    obtain ⟨base,cap⟩ := mem_filter.mp hj
    exact mem_Icc.mpr ⟨(mem_Icc.mp (bilateral_right_high_step_range base)).1,cap⟩
  have leftMass (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ i ∈ (thinHighLeftItems n).filter (fun i => leftBilinearStep i=m), ‖leftBilinearWeight n i‖) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _)) (fun _ _ _ => norm_nonneg _)).trans
      (norm_bilateral_left_step_mass n0 T0 divisors m (Icc_subset_Icc_right An hm))
  have rightMass (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ j ∈ (outerRightHighItems n).filter (fun j => rightHighWaveStep j=m), ‖rightHighWaveWeight n j‖) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _)) (fun _ _ _ => norm_nonneg _)).trans
      (norm_bilateral_right_high_step_mass T0 divisors m (Icc_subset_Icc_right An hm))
  have logA : 1+Real.log (A : ℝ) ≤ L := by
    have h : (A : ℝ) ≤ N := by
      change (expandedWideStepCap n : ℝ) ≤ (n : ℝ)
      exact_mod_cast An
    have p : (0 : ℝ) < A := by exact_mod_cast A0
    unfold L logBudget
    linarith only [Real.log_le_log p (show (A : ℝ) ≤ (n : ℝ)+2 from h.trans (by simp [N]))]
  have aCap : (A : ℝ) ≤ N^(511/768 : ℝ) := Nat.floor_le (by positivity)
  have h := norm_pair_residue_swap_family_le n A n0 A0 (thinHighLeftItems n) (outerRightHighItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) rightHighWaveStep (rightHighWaveLower n)
    (fun j => n/rightHighWaveStep j) (leftBilinearWeight n) (rightHighWaveWeight n)
    (fun i j => largeHighProductGate n i (rightHighWaveStep j)) W0 leftRange rightRange leftMass rightMass
  calc
    _ ≤ 24*W^2*(A : ℝ)*(1+Real.log (A : ℝ))*(n.divisors.card : ℝ) := h
    _ ≤ 24*W^2*N^(511/768 : ℝ)*L*T := by gcongr; exact divisors n le_rfl
    _ = _ := by unfold W L N; ring

theorem large_high_product_volume_correction_saving : saving largeHighProductVolumeCorrection := by
  intro ε he
  obtain ⟨D,D1,dBound⟩ := divisor_envelope_at_power 4096 (by decide)
  let C := 24*D^7
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-((257/768-10/4096)) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (257/768-10/4096))).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C*(n : ℝ)^(-((257/768-10/4096)) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have est : ∀ᶠ n : ℕ in atTop, ‖largeHighProductVolumeCorrection n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le_power (1/4096) (by norm_num),
      scaled.eventually_lt_const he] with n hn logb small
    have nr : (0 : ℝ) < n := by exact_mod_cast hn
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/4096 : ℝ)
    let T := D*X
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1
      (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))
    have ex : (n : ℝ)^(511/768 : ℝ)*X^10 = (n : ℝ)^(-((257/768-10/4096)) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast nr.le,← Real.rpow_add nr,← Real.rpow_add_one nr.ne']
      congr 1
      norm_num
    calc
      _ ≤ 24*(n : ℝ)^(511/768 : ℝ)*T^7*logBudget n^3 :=
        norm_large_high_product_volume_correction_le hn T1 (dBound n)
      _ ≤ 24*(n : ℝ)^(511/768 : ℝ)*T^7*X^3 := by gcongr
      _ = C*((n : ℝ)^(511/768 : ℝ)*X^10) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-((257/768-10/4096)) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
  obtain ⟨N,h⟩ := eventually_atTop.mp est
  exact ⟨N,fun n hn _ => h n hn⟩

theorem original_large_high_product_wave_saving : saving originalLargeHighProductWaveSum := by
  intro ε he
  obtain ⟨N,h⟩ := large_high_product_wave_saving (ε/2) (by positivity)
  obtain ⟨M,hm⟩ := large_high_product_volume_correction_saving (ε/2) (by positivity)
  refine ⟨max N M,fun n hn even => ?_⟩
  rw [original_large_high_product_eq_swapped_add_correction]
  exact (norm_add_le _ _).trans (by linarith only [h n (by omega) even,hm n (by omega) even])

end

end B13BoundedStepProductSavingProof

end

/- Large high product arithmetic -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def largeHighProductBaseGate (n : ℕ) (i : ℕ × ℕ) (j : RightHighWaveIndex) : Prop :=
  let u := leftBilinearStep i
  let v := rightHighWaveStep j
  expandedHighModulusCap n < v ∧ prefixStepGate n u v ∧ u*v ≤ highFarStripProductCap n

def largeHighProductBase (n : ℕ) : ℂ :=
  ∑ i ∈ thinHighLeftItems n, ∑ j ∈ outerRightHighItems n,
    if largeHighProductBaseGate n i j then highResidueTerm n i j else 0

private theorem large_high_product_original_under_caps (n : ℕ) :
    originalLargeHighProductWaveSum n =
      ∑ i ∈ thinHighLeftItems n, ∑ j ∈ outerRightHighItems n,
        if largeHighProductGate n i (rightHighWaveStep j) then highResidueTerm n i j else 0 := by
  unfold originalLargeHighProductWaveSum highResidueSum thinHighLeftItems outerRightHighItems extendedWaveItems expandedWaveItems
  simp_rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : leftBilinearStep i ≤ extendedWideStepCap n
  · rw [ite_eq_left hi]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : largeHighProductGate n i (rightHighWaveStep j)
    · simp [hj,hj.2.1]
    · simp [hj]
  · rw [ite_eq_right hi]
    refine sum_eq_zero fun j _ => ?_
    exact ite_eq_right (fun h : largeHighProductGate n i (rightHighWaveStep j) => hi h.1)

theorem large_high_product_base_eq_partition (n : ℕ) :
    largeHighProductBase n = originalLargeHighProductWaveSum n + boundedRightCuts largeHighProductBaseGate n := by
  rw [large_high_product_original_under_caps]
  unfold largeHighProductBase boundedRightCuts boundedRightProductCut boundedRightCommonCut boundedRightTargetCut
    smallProductResidueFamily gcdResidueFamily largeLeftDivisorResidueFamily
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  let u := leftBilinearStep i
  let v := rightHighWaveStep j
  have ui : u ≤ extendedWideStepCap n := (mem_filter.mp hi).2
  have vj : v ≤ expandedWideStepCap n := (mem_filter.mp hj).2
  have combine : largeHighProductGate n i v ↔ (largeHighProductBaseGate n i j ∧ thinHighProductCap n < u*v ∧
      u.gcd v ≤ thinHighGcdCap n ∧ u.gcd n ≤ thinHighLeftDivisorCap n) := by
    constructor
    · rintro ⟨_,_,lo,p,tl,up,g,t⟩
      exact ⟨⟨lo,p,up⟩,tl,g,t⟩
    · rintro ⟨⟨lo,p,up⟩,tl,g,t⟩
      exact ⟨ui,vj,lo,p,tl,up,g,t⟩
  by_cases base : largeHighProductBaseGate n i j
  · by_cases p : u*v ≤ thinHighProductCap n
    · simp [u,v,base,p,not_lt.mpr p,combine,boundedRightProductGate,highResidueTerm]
    · by_cases g : u.gcd v ≤ thinHighGcdCap n
      · by_cases t : u.gcd n ≤ thinHighLeftDivisorCap n <;>
          simp [u,v,base,p,lt_of_not_ge p,g,not_lt.mpr g,t,lt_of_not_ge,
            combine,boundedRightProductGate,highResidueTerm]
      · simp [u,v,base,p,lt_of_not_ge p,g,lt_of_not_ge g,combine,boundedRightProductGate,highResidueTerm]
  · have nope : ¬largeHighProductGate n i (rightHighWaveStep j) := fun h => base (combine.mp h).1
    simp [base,nope,boundedRightProductGate]

theorem large_high_product_base_saving : saving largeHighProductBase := by
  intro ε he
  obtain ⟨N,h⟩ := original_large_high_product_wave_saving (ε/2) (by positivity)
  obtain ⟨M,hm⟩ := bounded_right_cuts_saving largeHighProductBaseGate (ε/2) (by positivity)
  refine ⟨max N M,fun n hn even => ?_⟩
  rw [large_high_product_base_eq_partition]
  exact (norm_add_le _ _).trans (by linarith only [h n (by omega) even,hm n (by omega) even])

theorem large_high_product_left_step_le_old_cap {n u v : ℕ}
    (n0 : 0 < n) (scale : (2 : ℝ) ≤ (n : ℝ)^(1/1024 : ℝ))
    (vLo : expandedHighModulusCap n < v) (p : u*v ≤ highFarStripProductCap n) :
    u ≤ extendedWideStepCap n := by
  let N := (n : ℝ)
  have n1 : 1 ≤ N := by change (1 : ℝ) ≤ n; exact_mod_cast n0
  have np : 0 < N := zero_lt_one.trans_le n1
  have lo : N^(515/1024 : ℝ) ≤ (v : ℝ) := (Nat.lt_floor_add_one _).le.trans
    (by change (expandedHighModulusCap n : ℝ)+1 ≤ (v : ℝ); exact_mod_cast Nat.succ_le_of_lt vLo)
  have upper : (u : ℝ)*(v : ℝ) ≤ (highFarStripProductCap n : ℝ) := by exact_mod_cast p
  have geo : (u : ℝ) ≤ N^(1/2 : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (515/1024 : ℝ))).mp
    calc
      _ ≤ (u : ℝ)*(v : ℝ) := mul_le_mul_of_nonneg_left lo (by positivity)
      _ ≤ _ := upper
      _ ≤ 2*N^(4097/4096 : ℝ) := by
        unfold highFarStripProductCap
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
      _ ≤ N^(1/1024 : ℝ)*N^(4097/4096 : ℝ) := mul_le_mul_of_nonneg_right scale (by positivity)
      _ ≤ N^(1/2 : ℝ)*N^(515/1024 : ℝ) := by
        rw [← Real.rpow_add np,← Real.rpow_add np]
        exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
  exact Nat.le_floor (geo.trans (Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)))

end

end B13BoundedStepProductSavingProof

end

/- Large high product remainder -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter
open scoped Classical Finset

noncomputable section

def rawExpandedHighAboveProduct (n : ℕ) : ℂ :=
  rawWavePairSum n (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep)
    (outerRightHighItems n) rightHighWaveStep (rightHighWaveLower n)
    (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)
    (fun u v => prefixStepGate n u v ∧ highFarStripProductCap n < u*v)
    (fun u v l r p s => (pairResidueError n u v l r p s : ℂ))

end

end B13BoundedStepProductSavingProof

end

/- Middle low product geometry -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def middleLowProductGate (lowerCap upperCap : ℕ → ℕ) (farOnly : Bool) (n u v : ℕ) : Prop :=
  u ≤ extendedWideStepCap n ∧ lowerCap n < v ∧ v ≤ upperCap n ∧
    prefixStepGate n u v ∧ u*v ≤ highFarStripProductCap n ∧ (farOnly = true → 2*n < u*v)

def middleLowAnalyticGate (lowerCap upperCap : ℕ → ℕ) (farOnly : Bool) (n x y : ℕ) : Prop :=
  middleLowProductGate lowerCap upperCap farOnly n x y ∧ thinHighProductCap n < x*y ∧
    x.gcd y ≤ nearProductCommonDivisorCut n ∧ y.gcd n ≤ targetDivisorCap n

def middleLowProductRows (lowerCap upperCap : ℕ → ℕ) (J : ℕ → Finset RightLowWaveIndex) (n : ℕ) : Finset RightLowWaveIndex :=
  (J n).filter fun j =>
    let v := rightLowWaveStep j
    n ≤ v^2 ∧ lowerCap n < v ∧ v ≤ upperCap n ∧ v.gcd n ≤ targetDivisorCap n

def middleLowProductLower (farOnly : Bool) (n : ℕ) (j : RightLowWaveIndex) (_ : ℕ) : ℕ :=
  let v := rightLowWaveStep j
  max (primeHyperbolaShortLeftLo n v) (max (thinHighProductCap n/v) (if farOnly then 2*n/v else 0))

def middleLowProductUpper (n : ℕ) (j : RightLowWaveIndex) (_ : ℕ) : ℕ :=
  let v := rightLowWaveStep j
  min (extendedWideStepCap n) (highFarStripProductCap n/v)

theorem middle_low_product_square {n v : ℕ} (n0 : 0 < n) (lo : expandedHighModulusCap n < v) :
    n ≤ v^2 := by
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast n0
  have top : (n : ℝ)^(515/1024 : ℝ) ≤ (v : ℝ) := (Nat.lt_floor_add_one _).le.trans
    (by change (expandedHighModulusCap n : ℝ)+1 ≤ (v : ℝ); exact_mod_cast Nat.succ_le_of_lt lo)
  have rt : (n : ℝ)^(1/2 : ℝ) ≤ v :=
    (Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)).trans top
  rw [← Real.sqrt_eq_rpow] at rt
  exact_mod_cast (Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (v : ℝ))).mp rt

theorem middle_low_product_membership {n : ℕ} {J : ℕ → Finset RightLowWaveIndex}
    {i : ℕ × ℕ} {j : RightLowWaveIndex} (farOnly : Bool) (lowerCap upperCap : ℕ → ℕ)
    (rootFloor : expandedHighModulusCap n ≤ lowerCap n) (hi : i ∈ bilateralLeftWaveItems n)
    (hj : j ∈ J n) (hr : j ∈ rightLowWaveItems n) :
    (j ∈ middleLowProductRows lowerCap upperCap J n ∧ i ∈ moderateLowDividedHyperbolaRowItems n (rightLowWaveStep j)
        (middleLowProductLower farOnly n j) (middleLowProductUpper n j)) ↔
      (leftBilinearStep i ≤ expandedWideStepCap n ∧ rightLowWaveStep j ≤ expandedWideStepCap n) ∧
      middleLowAnalyticGate lowerCap upperCap farOnly n (leftBilinearStep i) (rightLowWaveStep j) ∧
      (leftBilinearStep i).gcd (rightLowWaveStep j) ∣ n := by
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  have range := mem_Icc.mp (bilateral_right_low_step_range hr)
  have v0 : 0 < v := range.1
  have n0 : 0 < n := v0.trans_le range.2
  have vCap := ((right_low_step_le_proved_medium_cap hr).trans (old_step_cap_le_extended n)).trans
    (extended_step_cap_le_expanded n)
  have u0 : 0 < u := (mem_Icc.mp (bilateral_left_step_range hi)).1
  constructor
  · rintro ⟨row,col⟩
    obtain ⟨_,_,mLo,mHi,char⟩ := mem_filter.mp row
    obtain ⟨_,gMem,lo,up⟩ := mem_filter.mp col
    obtain ⟨dv,gNear,gMax,_⟩ := mem_filter.mp gMem
    have marked : maximumStep n^2 < u*v := (Nat.div_lt_iff_lt_mul v0).mp
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt ((le_max_left _ _).trans_lt lo))
    have thin : thinHighProductCap n < u*v := (Nat.div_lt_iff_lt_mul v0).mp
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt lo)
    have product : u*v ≤ highFarStripProductCap n :=
      (Nat.le_div_iff_mul_le v0).mp (up.trans (min_le_right _ _))
    have gate : farOnly = true → 2*n < u*v := by
      intro on
      apply (Nat.div_lt_iff_lt_mul v0).mp
      have h : (if farOnly then 2*n/v else 0) < u := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt lo
      simpa only [on,if_true] using h
    have uc : u ≤ extendedWideStepCap n := up.trans (min_le_left _ _)
    exact ⟨⟨uc.trans (extended_step_cap_le_expanded n),vCap⟩,
      ⟨⟨uc,mLo,mHi,⟨marked,gMax⟩,product,gate⟩,thin,gNear,char⟩,(Nat.mem_divisors.mp dv).1⟩
  · rintro ⟨_,⟨⟨uHi,mLo,mHi,pref,product,gate⟩,thin,gNear,char⟩,dv⟩
    have row : j ∈ middleLowProductRows lowerCap upperCap J n :=
      mem_filter.mpr ⟨hj,middle_low_product_square n0 (rootFloor.trans_lt mLo),mLo,mHi,char⟩
    have gMem : u.gcd v ∈ expandedHighDividedHyperbolaDivisors n v :=
      mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dv,n0.ne'⟩,gNear,pref.2,Nat.gcd_dvd_right _ _⟩
    have markedLeft := (mem_filter.mp (mem_filter.mp hi).1).2
    have hThin : thinHighProductCap n/v < u := (Nat.div_lt_iff_lt_mul v0).mpr thin
    have hBase : primeHyperbolaShortLeftLo n v < u := max_lt markedLeft
      (max_lt ((Nat.div_lt_iff_lt_mul v0).mpr pref.1)
        ((Nat.div_lt_iff_lt_mul v0).mpr ((thin_high_product_cap_ge_old n).trans_lt thin)))
    have hFar : (if farOnly then 2*n/v else 0) < u := by
      cases farOnly
      · simpa only [Bool.false_eq_true,if_false] using u0
      · simpa only [if_true] using (Nat.div_lt_iff_lt_mul v0).mpr (gate rfl)
    have hl : middleLowProductLower farOnly n j (u.gcd v) < u :=
      max_lt hBase (max_lt hThin hFar)
    have ht : u ≤ middleLowProductUpper n j (u.gcd v) :=
      le_min uHi ((Nat.le_div_iff_mul_le v0).mpr product)
    exact ⟨row,mem_filter.mpr ⟨hi,gMem,hl,ht⟩⟩

end

end B13BoundedStepProductSavingProof

end

/- Middle low product actual -/
section

namespace B13BoundedStepProductSavingProof

open Finset
open scoped Classical Finset

noncomputable section

private theorem middle_low_sum_extend {α : Type*} {S T : Finset α} (h : S ⊆ T)
    (f : α → ℂ) : (∑ a ∈ S, f a) = ∑ a ∈ T, if a ∈ S then f a else 0 := by
  rw [← sum_filter]
  have eq : T.filter (fun a => a ∈ S) = S := by
    ext a
    exact ⟨fun ha => (mem_filter.mp ha).2, fun ha => mem_filter.mpr ⟨h ha,ha⟩⟩
  rw [eq]

theorem middle_low_actual_eq_analytic {n : ℕ} (J : ℕ → Finset RightLowWaveIndex)
    (subset : J n ⊆ rightLowWaveItems n) (lowerCap upperCap : ℕ → ℕ) (farOnly : Bool)
    (floor : expandedHighModulusCap n ≤ lowerCap n) :
    moderateLowActualSlice (middleLowProductRows lowerCap upperCap J)
      (middleLowProductLower farOnly) middleLowProductUpper n =
      boundedOuterLeftBaseFrom (middleLowAnalyticGate lowerCap upperCap farOnly) n (J n)
        rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight := by
  let I := bilateralLeftWaveItems n
  let R := middleLowProductRows lowerCap upperCap J n
  let Q (j : RightLowWaveIndex) := moderateLowDividedHyperbolaRowItems n (rightLowWaveStep j)
    (middleLowProductLower farOnly n j) (middleLowProductUpper n j)
  let V := rightLowResidueTerm n
  let good (i : ℕ × ℕ) (j : RightLowWaveIndex) :=
    (leftBilinearStep i ≤ expandedWideStepCap n ∧ rightLowWaveStep j ≤ expandedWideStepCap n) ∧
      middleLowAnalyticGate lowerCap upperCap farOnly n (leftBilinearStep i) (rightLowWaveStep j)
  have lhs :
      moderateLowActualSlice (middleLowProductRows lowerCap upperCap J)
        (middleLowProductLower farOnly) middleLowProductUpper n =
        ∑ j ∈ J n, ∑ i ∈ I, if j ∈ R ∧ i ∈ Q j then V i j else 0 := by
    unfold moderateLowActualSlice
    have outer : R ⊆ J n := filter_subset _ _
    have inner (j : RightLowWaveIndex) : Q j ⊆ I := filter_subset _ _
    have point (j : RightLowWaveIndex) :
        rightLowWaveWeight j * (∑ i ∈ Q j, leftBilinearWeight n i *
          (pairResidueError n (leftBilinearStep i) (rightLowWaveStep j) 0 (n/leftBilinearStep i) 0
            (rightLowWaveUpper n j) : ℂ)) = ∑ i ∈ Q j, V i j := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      unfold V rightLowResidueTerm
      ring
    calc
      _ = ∑ j ∈ R, ∑ i ∈ Q j, V i j := sum_congr rfl (fun j _ => point j)
      _ = _ := by
        rw [middle_low_sum_extend outer]
        refine sum_congr rfl fun j _ => ?_
        by_cases h : j ∈ R
        · rw [ite_eq_left h,middle_low_sum_extend (inner j)]
          refine sum_congr rfl fun i _ => ?_
          by_cases a : i ∈ Q j
          · rw [ite_eq_left a,ite_eq_left (And.intro h a)]
          · rw [ite_eq_right a,ite_eq_right (fun z : j ∈ R ∧ i ∈ Q j => a z.2)]
        · simp [h]
  have rhs :
      boundedOuterLeftBaseFrom (middleLowAnalyticGate lowerCap upperCap farOnly) n (J n)
        rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight =
      ∑ i ∈ I, ∑ j ∈ J n, if good i j then V i j else 0 := by
    unfold boundedOuterLeftBaseFrom expandedWaveItems
    simp_rw [sum_filter]
    refine sum_congr rfl fun i _ => ?_
    by_cases uCap : leftBilinearStep i ≤ expandedWideStepCap n
    · rw [ite_eq_left uCap]
      refine sum_congr rfl fun j _ => ?_
      by_cases vCap : rightLowWaveStep j ≤ expandedWideStepCap n <;>
        simp [uCap,vCap,good,V,rightLowResidueTerm]
    · simp [uCap,good,V]
  rw [lhs,rhs,sum_comm (s := J n) (t := I)]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have eq := middle_low_product_membership farOnly lowerCap upperCap floor hi hj (subset hj)
  by_cases b : good i j
  · by_cases compat : (leftBilinearStep i).gcd (rightLowWaveStep j) ∣ n
    · rw [ite_eq_left (eq.mpr ⟨b.1,b.2,compat⟩),ite_eq_left b]
    · have off : ¬(j ∈ R ∧ i ∈ Q j) := fun h => compat (eq.mp h).2.2
      rw [ite_eq_right off,ite_eq_left b]
      simp [V,rightLowResidueTerm,pairResidueError,compat]
  · have off : ¬(j ∈ R ∧ i ∈ Q j) := fun h => b ⟨(eq.mp h).1,(eq.mp h).2.1⟩
    rw [ite_eq_right off,ite_eq_right b]

end

end B13BoundedStepProductSavingProof

end

/- Middle low product saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4EnergyTail
open scoped Classical Finset

noncomputable section

private theorem middle_low_product_kept_unchanged (n : ℕ) (J : Finset RightLowWaveIndex)
    (lowerCap upperCap : ℕ → ℕ) (farOnly : Bool) :
    boundedOuterLeftKeptFrom (middleLowAnalyticGate lowerCap upperCap farOnly) n J
      rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight =
    boundedOuterLeftKeptFrom (middleLowProductGate lowerCap upperCap farOnly) n J
      rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight := by
  unfold boundedOuterLeftKeptFrom
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  have related :
      boundedOuterLeftKeptGate (middleLowAnalyticGate lowerCap upperCap farOnly) n u v ↔
      boundedOuterLeftKeptGate (middleLowProductGate lowerCap upperCap farOnly) n u v := by
    constructor
    · rintro ⟨⟨base,_,_,_⟩,prod,g,tar⟩
      exact ⟨base,prod,g,tar⟩
    · rintro ⟨base,prod,g,tar⟩
      exact ⟨⟨base,prod,g.trans (thin_high_gcd_cap_le_old n),tar⟩,prod,g,tar⟩
  rw [related]

theorem middle_low_product_base_saving_of_analytic (J : ℕ → Finset RightLowWaveIndex)
    (subset : ∀ n, J n ⊆ rightLowWaveItems n) (lowerCap upperCap : ℕ → ℕ) (farOnly : Bool)
    (floor : ∀ n, expandedHighModulusCap n ≤ lowerCap n)
    (actual : saving (moderateLowActualSlice (middleLowProductRows lowerCap upperCap J)
      (middleLowProductLower farOnly) middleLowProductUpper)) :
    saving (fun n => boundedOuterLeftBaseFrom (middleLowProductGate lowerCap upperCap farOnly) n (J n)
      rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight) := by
  let v := rightLowWaveStep
  let c := rightLowWaveUpper
  let a := rightLowWaveWeight
  let F := middleLowProductGate lowerCap upperCap farOnly
  let G := middleLowAnalyticGate lowerCap upperCap farOnly
  have step (n : ℕ) (j : RightLowWaveIndex) (hj : j ∈ J n) : v j ∈ Icc 1 n :=
    bilateral_right_low_step_range (subset n hj)
  have mass (n : ℕ) {T : ℝ} (T1 : 1 ≤ T) (d : ∀ u ≤ n, (u.divisors.card : ℝ) ≤ T)
      (m : ℕ) (hm : m ∈ Icc 1 n) :
      (∑ j ∈ (J n).filter (fun j => v j=m), ‖a j‖) ≤ T^3*logBudget n :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (subset n)) (fun _ _ _ => norm_nonneg _)).trans
      (norm_bilateral_right_low_step_mass T1 d m hm)
  have fSave := bounded_outer_left_cut_saving F J v (fun _ _ => 0) c (fun _ => a) step
    (fun n _ t d m hm => mass n t d m hm)
  have gSave := bounded_outer_left_cut_saving G J v (fun _ _ => 0) c (fun _ => a) step
    (fun n _ t d m hm => mass n t d m hm)
  intro ε he
  obtain ⟨N,h⟩ := actual (ε/3) (by positivity)
  obtain ⟨M,hm⟩ := fSave (ε/3) (by positivity)
  obtain ⟨K,hk⟩ := gSave (ε/3) (by positivity)
  refine ⟨max N (max M K),fun n hn even => ?_⟩
  let P := boundedOuterLeftBaseFrom F n (J n) v (fun _ => 0) (c n) a
  let A := boundedOuterLeftBaseFrom G n (J n) v (fun _ => 0) (c n) a
  let CF := boundedOuterLeftCut F n (J n) v (fun _ => 0) (c n) a
  let CG := boundedOuterLeftCut G n (J n) v (fun _ => 0) (c n) a
  have eq : P = A-CG+CF := by
    unfold P A
    rw [bounded_outer_left_base_eq_partition,bounded_outer_left_base_eq_partition]
    have e := middle_low_product_kept_unchanged n (J n) lowerCap upperCap farOnly
    change boundedOuterLeftKeptFrom G n (J n) v (fun _ => 0) (c n) a =
      boundedOuterLeftKeptFrom F n (J n) v (fun _ => 0) (c n) a at e
    rw [e]
    change _+CF = (_+CG)-CG+CF
    abel
  have hA : ‖A‖ ≤ ε/3*(n : ℝ) := by
    have e := middle_low_actual_eq_analytic J (subset n) lowerCap upperCap farOnly (floor n)
    simpa only [e] using h n (by omega) even
  have hF : ‖CF‖ ≤ ε/3*(n : ℝ) := hm n (by omega) even
  have hG : ‖CG‖ ≤ ε/3*(n : ℝ) := hk n (by omega) even
  change ‖P‖ ≤ _
  rw [eq]
  calc
    _ ≤ ‖A-CG‖+‖CF‖ := norm_add_le _ _
    _ ≤ (‖A‖+‖CG‖)+‖CF‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ _ := by linarith only [hA,hG,hF]

private theorem middle_low_product_upper_mul (n : ℕ) (j : RightLowWaveIndex) (g : ℕ) :
    middleLowProductUpper n j g*rightLowWaveStep j ≤ expandedHyperbolaProductCap n :=
  ((Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)).trans
    (high_far_strip_cap_le_expanded_product n)

theorem moderate_low_product_base_saving (J : ℕ → Finset RightLowWaveIndex)
    (subset : ∀ n, J n ⊆ rightLowWaveItems n) (farOnly : Bool) :
    saving (fun n =>
      boundedOuterLeftBaseFrom (middleLowProductGate expandedHighModulusCap shortLowModulusCap farOnly) n
        (J n) rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight) := by
  refine middle_low_product_base_saving_of_analytic J subset _ _ farOnly (fun _ => le_rfl) ?_
  refine moderate_low_actual_slice_saving _ _ _ ?_ ?_ ?_ ?_ ?_
  · intro n j hj
    obtain ⟨base,sq,_,hi,char⟩ := mem_filter.mp hj
    exact ⟨subset n base,sq,hi,char⟩
  · exact fun _ _ _ _ => (le_max_left _ _).trans (le_max_left _ _)
  · exact fun _ _ _ _ => ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  · exact fun _ _ _ _ => min_le_left _ _
  · exact fun n j _ g => middle_low_product_upper_mul n j g

theorem wider_far_low_product_base_saving (J : ℕ → Finset RightLowWaveIndex)
    (subset : ∀ n, J n ⊆ rightLowWaveItems n) :
    saving (fun n =>
      boundedOuterLeftBaseFrom (middleLowProductGate shortLowModulusCap widerLowFarModulusCap true) n
        (J n) rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight) := by
  have caps (n : ℕ) : expandedHighModulusCap n ≤ shortLowModulusCap n := by
    rcases eq_or_ne n 0 with rfl | h
    · norm_num [expandedHighModulusCap,shortLowModulusCap,Real.zero_rpow]
    · exact expanded_high_modulus_cap_le_short_low (Nat.pos_of_ne_zero h)
  refine middle_low_product_base_saving_of_analytic J subset _ _ true caps ?_
  let R := middleLowProductRows shortLowModulusCap widerLowFarModulusCap J
  let lo := middleLowProductLower true
  let hi := middleLowProductUpper
  have sup (n : ℕ) (j : RightLowWaveIndex) (hj : j ∈ R n) :
      j ∈ rightLowWaveItems n ∧ n ≤ (rightLowWaveStep j)^2 ∧ shortLowModulusCap n < rightLowWaveStep j ∧
        rightLowWaveStep j ≤ widerLowFarModulusCap n ∧
          (rightLowWaveStep j).gcd n ≤ targetDivisorCap n := by
    obtain ⟨base,sq,l,r,chr⟩ := mem_filter.mp hj
    exact ⟨subset n base,sq,l,r,chr⟩
  have a : ∀ n j, j ∈ R n → ∀ g, 2*n/rightLowWaveStep j ≤ lo n j g :=
    fun _ _ _ _ => (le_max_right _ _).trans (le_max_right _ _)
  have b : ∀ n j, j ∈ R n → ∀ g, hi n j g ≤ extendedWideStepCap n := fun _ _ _ _ => min_le_left _ _
  intro ε he
  obtain ⟨N,h⟩ := wider_low_far_residue_saving R lo hi sup a b
    (fun n j _ g => middle_low_product_upper_mul n j g) ε he
  refine ⟨N,fun n hn even => ?_⟩
  rw [← moderate_low_actual_slice_eq R lo hi
      (fun j hj => ⟨(sup n j hj).1,(sup n j hj).2.1⟩)
      (fun _ _ _ => (le_max_left _ _).trans (le_max_left _ _)) (b n)]
  exact h n hn even

end

end B13BoundedStepProductSavingProof

end

/- Large q low far window -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

set_option maxHeartbeats 2500000 in
def largeQLowFarShortCut (n : ℕ) : ℕ := ⌊(n : ℝ)^(7/1024 : ℝ)⌋₊

set_option maxHeartbeats 2500000 in
def largeQLowFarFactorLower (n k : ℕ) : ℕ :=
  max (largeQLowFarShortCut n) (swappedHighFactorFloor n k)

set_option maxHeartbeats 2500000 in
def largeQLowFarFactorBlock (n k : ℕ) : Finset ℕ :=
  Ioc (largeQLowFarFactorLower n k) (min (cutoffU n) (swappedHighFactorFloor n (k+1)))

set_option maxHeartbeats 2500000 in
def largeQLowFarStepLower (n m : ℕ) : ℕ :=
  max (widerLowFarModulusCap n) (max (2*n/m) (max (maximumStep n^2/m) (thinHighProductCap n/m)))

set_option maxHeartbeats 2500000 in
def largeQLowFarStepUpper (n m : ℕ) : ℕ :=
  min (extendedWideStepCap n) (highFarStripProductCap n/m)

set_option maxHeartbeats 2500000 in
def largeQLowFarFactors (n m g k : ℕ) : Finset ℕ :=
  (Ioc (largeQLowFarFactorLower n k/g) (min (cutoffU n) (swappedHighFactorFloor n (k+1))/g)).filter
    (fun a => a.Coprime (m/g))

set_option maxHeartbeats 2500000 in
def largeQLowFarCofactorCap (n m g k : ℕ) : ℕ :=
  (largeQLowFarStepUpper n m/g)/(largeQLowFarFactorLower n k/g+1)

set_option maxHeartbeats 2500000 in
def largeQLowFarWindow (n : ℕ) (row : ℕ × ℕ) (g k : ℕ) : ℂ :=
  let m := leftBilinearStep row
  let v := m/g
  let l := largeQLowFarStepLower n m/g
  let r := largeQLowFarStepUpper n m/g
  let I := largeQLowFarFactors n m g k
  let J := intIntervalModUnits v 0 (largeQLowFarCofactorCap n m g k)
  let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (cutoffU n : ℤ)
  let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (min n (rightLargeCofactorCut n) : ℕ)
  let num := n/g-m/g
  gatedBilinearSum I J (swappedLowShortWeight g) (swappedLowPrimeWeight n) lo hi
    (fun a j => centeredIntIntervalResidue v 0 ((num : ℤ)/((a*j.toNat : ℕ) : ℤ))
      ((n/g : ℕ)*((a : ZMod v)*(j : ZMod v))⁻¹))

set_option maxHeartbeats 2500000 in
theorem norm_large_q_low_far_window_le {n g k : ℕ} {row : ℕ × ℕ}
    (hrow : row ∈ outerRightRows n)
    (gpos : 0 < g) (gn : g ∣ n) (gm : g ∣ leftBilinearStep row) (gSmall : g ≤ thinHighGcdCap n)
    (hk : k ∈ Icc 224 2047) (ns : 1 < n)
    {T : ℝ} (T1 : 1 ≤ T) (TL : logBudget n ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖largeQLowFarWindow n row g k‖ ≤
      592*(n : ℝ)^(4095/4096 : ℝ)*T^3*logBudget n^3/(leftBilinearStep row : ℝ) := by
  let e := g
  have e0 : 0 < e := gpos
  have eg : e ∣ g := dvd_refl g
  let m := leftBilinearStep row
  let v := m/g
  let N := (n : ℝ)
  let M := (m : ℝ)
  let V := (v : ℝ)
  let G := (g : ℝ)
  let E := (e : ℝ)
  let y := (k : ℝ)/32768
  let x := y-1/4096
  let A := swappedHighFactorFloor n (k+1)/e
  let aLo := largeQLowFarFactorLower n k
  let S := largeQLowFarCofactorCap n m g k
  let I := largeQLowFarFactors n m g k
  let J := intIntervalModUnits v 0 S
  let mLo := largeQLowFarStepLower n m
  let mHi := largeQLowFarStepUpper n m
  let l := mLo/g
  let r := mHi/g
  let L := logBudget n
  let α := swappedLowShortWeight g
  let β := swappedLowPrimeWeight n
  let baseLo (_ : ℕ) : ℤ := cutoffU n
  let baseHi (_ : ℕ) : ℤ := (min n (rightLargeCofactorCut n) : ℕ)
  let num := n/g-m/g
  have numN : num ≤ n/g := Nat.sub_le _ _
  have right : row ∈ bilateralLeftWaveItems n := (mem_filter.mp hrow).1
  obtain ⟨sq,origLo,charTop⟩ := (mem_filter.mp hrow).2
  have step := mem_Icc.mp (bilateral_left_step_range right)
  have m0 : 0 < m := step.1
  have mN : m ≤ n := step.2
  have v0 : 0 < v := Nat.div_pos (Nat.le_of_dvd m0 gm) gpos
  let _ : NeZero v := ⟨v0.ne'⟩
  have vprod : v*g=m := Nat.div_mul_cancel gm
  have npNat : 0 < n := zero_lt_one.trans ns
  have nr : 1 < N := show (1 : ℝ) < (n : ℝ) from by exact_mod_cast ns
  have np : 0 < N := zero_lt_one.trans nr
  have gp : 0 < G := show (0 : ℝ) < (g : ℝ) from by exact_mod_cast gpos
  have G1 : 1 ≤ G := show (1 : ℝ) ≤ (g : ℝ) from by exact_mod_cast gpos
  have vN : v ≤ n := (by simpa only [mul_one] using Nat.mul_le_mul_left v (show 1 ≤ g from gpos) : v ≤ v*g).trans
    (by rw [vprod]; exact mN)
  have vEq : V*G=M := by
    change (v : ℝ)*(g : ℝ) = (m : ℝ)
    exact_mod_cast vprod
  have origHi : M ≤ N^(1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.le_sqrt (by positivity) np.le).mpr
    change (m : ℝ)^2 ≤ (n : ℝ)
    exact_mod_cast sq
  have castGcd : (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ N^(1/2048 : ℝ) := by
    have vd : v ∣ m := ⟨g,vprod.symm⟩
    have nd : n/g ∣ n := ⟨g,(Nat.div_mul_cancel gn).symm⟩
    have d : v.gcd (n/g) ∣ m.gcd n := Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans vd) ((Nat.gcd_dvd_right _ _).trans nd)
    have relation := (gcd_val_nat_cast_le_gcd (m := v) (n/g)).trans
      ((Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ npNat) d).trans charTop)
    exact (show (v.gcd ((n/g : ℕ) : ZMod v).val : ℝ) ≤ (thinHighLeftDivisorCap n : ℝ) by
      exact_mod_cast relation).trans (Nat.floor_le (by positivity))
  have vHi : V ≤ N^(1/2 : ℝ) := by
    have h : V ≤ M := by
      rw [← vEq]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left G1 (by positivity : 0 ≤ V)
    exact h.trans origHi
  have gReal : G ≤ (thinHighGcdCap n : ℝ) := by
    change (g : ℝ) ≤ (thinHighGcdCap n : ℝ)
    exact_mod_cast gSmall
  have gCap : G ≤ N^(1/4096 : ℝ) :=
    gReal.trans (Nat.floor_le (Real.rpow_nonneg np.le _))
  have egNat : e ≤ g := Nat.le_of_dvd gpos eg
  have egReal : E ≤ G := by
    change (e : ℝ) ≤ (g : ℝ)
    exact_mod_cast egNat
  have eCap : E ≤ N^(1/4096 : ℝ) := egReal.trans gCap
  have vLo : N^(1/3 : ℝ) < V := by
    apply (mul_lt_mul_iff_left₀ gp).mp
    calc
      _ ≤ N^(1/3 : ℝ)*N^(1/4096 : ℝ) := mul_le_mul_of_nonneg_left gCap (by positivity)
      _ < N^(171/512 : ℝ) := by rw [← Real.rpow_add np]; exact Real.rpow_lt_rpow_of_exponent_lt nr (by norm_num)
      _ ≤ M := origLo
      _ = _ := vEq.symm
  obtain ⟨kminNat, kmaxNat⟩ : 224 ≤ k ∧ k ≤ 2047 := mem_Icc.mp hk
  have kmin : (224 : ℝ) ≤ k := by exact_mod_cast kminNat
  have kmax : (k : ℝ) ≤ 2047 := by exact_mod_cast kmaxNat
  have xLo : 27/4096 ≤ x := by unfold x y; linarith only [kmin]
  have xHi : x ≤ 1/3 := by unfold x y; linarith only [kmax]
  have aFormula : swappedHighFactorFloor n (k+1) = ⌊N^(x+9/32768)⌋₊ := by
    unfold swappedHighFactorFloor N x y
    rw [Nat.cast_add,Nat.cast_one,add_div]
    congr 2
    ring
  have aCap : (A : ℝ) ≤ N^(x+9/32768) :=
    (by exact_mod_cast Nat.div_le_self (swappedHighFactorFloor n (k+1)) e :
      (A : ℝ) ≤ (swappedHighFactorFloor n (k+1) : ℝ)).trans (by rw [aFormula]; exact Nat.floor_le (by positivity))
  have A1 : 0 < A := by
    change 1 ≤ swappedHighFactorFloor n (k+1)/e
    apply (Nat.le_div_iff_mul_le e0).mpr
    rw [one_mul,aFormula]
    exact Nat.le_floor (eCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by linarith only [xLo])))
  have aQ : (A : ℝ) ≤ N^(1/3 : ℝ) :=
    aCap.trans (Real.rpow_le_rpow_of_exponent_le nr.le (by unfold x y; linarith only [kmax]))
  have Av : A < v := by
    have h := aQ.trans_lt vLo
    change (A : ℝ) < (v : ℝ) at h
    exact_mod_cast h
  have Icap : I ⊆ Icc 1 A := by
    intro a ha
    have h := mem_Ioc.mp (mem_filter.mp ha).1
    exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt h.1,h.2.trans (Nat.div_le_div_right (min_le_right (cutoffU n) _))⟩
  have copI (a : ℕ) (ha : a ∈ I) : a.Coprime v := (mem_filter.mp ha).2
  have rN : mHi ≤ n := (min_le_left _ _).trans (extended_wide_step_le npNat)
  have rG : r*g ≤ mHi := Nat.div_mul_le_self mHi g
  have sR : S ≤ r := Nat.div_le_self _ _
  have rp : r*v*g^2 ≤ highFarStripProductCap n := calc
    _ = (r*g)*(v*g) := by ring
    _ = (r*g)*m := by rw [vprod]
    _ ≤ mHi*m := Nat.mul_le_mul_right m rG
    _ ≤ (highFarStripProductCap n/m)*m := Nat.mul_le_mul_right m (min_le_right _ _)
    _ ≤ _ := Nat.div_mul_le_self _ _
  have rCap : (r : ℝ)*V*G^2 ≤ 2*N^(4097/4096 : ℝ) := by
    calc
      _ ≤ (highFarStripProductCap n : ℝ) := by
        change (r : ℝ)*(v : ℝ)*(g : ℝ)^2 ≤ (highFarStripProductCap n : ℝ)
        exact_mod_cast rp
      _ ≤ _ := by
        unfold highFarStripProductCap
        push_cast
        exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
  have cofactorFloor : N^x ≤ (aLo/e : ℕ)+1 := by
    have more : aLo < (aLo/e+1)*e := (Nat.div_lt_iff_lt_mul e0).mp (Nat.lt_succ_self _)
    have rank : (swappedHighFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*E := by
      have le : swappedHighFactorFloor n k+1 ≤ (aLo/e+1)*e :=
        Nat.succ_le_of_lt ((le_max_right _ _).trans_lt more)
      change (swappedHighFactorFloor n k : ℝ)+1 ≤ (((aLo/e : ℕ) : ℝ)+1)*(e : ℝ)
      exact_mod_cast le
    have ground : N^y ≤ (((aLo/e : ℕ) : ℝ)+1)*E := (Nat.lt_floor_add_one (N^y)).le.trans rank
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np (1/4096 : ℝ))).mp
    calc
      _ = N^y := by rw [← Real.rpow_add np]; unfold x; simp
      _ ≤ (((aLo/e : ℕ) : ℝ)+1)*E := ground
      _ ≤ _ := mul_le_mul_of_nonneg_left eCap (by positivity)
  have sCap : (S : ℝ)*V*G^2 ≤ 2*N^(4097/4096-x) := by
    have cut : S*(aLo/e+1) ≤ r := Nat.div_mul_le_self r (aLo/e+1)
    have scaled : (S : ℝ)*(((aLo/e : ℕ) : ℝ)+1) ≤ (r : ℝ) := by exact_mod_cast cut
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos np x)).mp
    calc
      _ ≤ ((S : ℝ)*V*G^2)*(((aLo/e : ℕ) : ℝ)+1) :=
        mul_le_mul_of_nonneg_left cofactorFloor (by positivity)
      _ = ((S : ℝ)*(((aLo/e : ℕ) : ℝ)+1))*V*G^2 := by ring
      _ ≤ (r : ℝ)*V*G^2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right scaled (by positivity)) (by positivity)
      _ ≤ 2*N^(4097/4096 : ℝ) := rCap
      _ = (2*N^(4097/4096-x))*N^x := by rw [mul_assoc,← Real.rpow_add np,sub_add_cancel]
  have endCap : num/(l+1) ≤ ⌊V*G*N^(1/8192 : ℝ)⌋₊ := by
    have mSub : thinHighProductCap n/m ≤ mLo :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    have endOrig := swapped_high_endpoint_cap_of_size npNat m0 mSub (le_rfl : n ≤ n)
    have s : mLo+1 ≤ (l+1)*g := Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul gpos).mp (Nat.lt_succ_self (mLo/g)))
    rw [vEq]
    calc
      _ ≤ (n/g)/(l+1) := Nat.div_le_div_right numN
      _ = n/((l+1)*g) := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm g (l+1)]
      _ ≤ n/(mLo+1) := Nat.div_le_div_left s (Nat.succ_pos _)
      _ ≤ _ := endOrig
  have divN (z : ℕ) (h : z ≤ n) : (z.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ ns.le (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors z (h.trans nn)
  have divV (z : ℕ) (h : z ≤ 4*v^3) : (z.divisors.card : ℝ) ≤ T :=
    divisors z (h.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left vN 3)))
  have divR (z : ℕ) (h : z ≤ r) : (z.divisors.card : ℝ) ≤ T :=
    divN z (h.trans ((Nat.div_le_self _ _).trans rN))
  have aw (a : ℕ) (_ : a ∈ I) : ‖α a‖ ≤ T*L :=
    (norm_swapped_low_short_weight_le_one g a).trans
      (one_le_mul_of_one_le_of_one_le T1 (one_le_logBudget n))
  have bw (j : ℤ) (_ : j ∈ J) : ‖β j‖ ≤ T :=
    (norm_swapped_low_prime_weight_le_log n j).trans TL
  have logBound : 1+Real.log V ≤ L := by
    have pv : 0 < V := show (0 : ℝ) < (v : ℝ) from by exact_mod_cast v0
    have up : V ≤ (n : ℝ)+2 := by
      change (v : ℝ) ≤ (n : ℝ)+2
      exact_mod_cast vN.trans (by omega : n≤n+2)
    unfold L logBudget
    linarith only [Real.log_le_log pv up]
  have first := norm_outer_far_ratio_hyperbola_le_wider_factor (m := v) (c := ((n/g : ℕ) : ZMod v)) (g := g)
    castGcd nr.le G1 T1 (one_le_logBudget n) vHi vLo.le gCap xLo xHi logBound aCap sCap rCap endCap
    A1 Av I Icap copI α β baseLo baseHi aw bw divV divR
  unfold largeQLowFarWindow
  dsimp only
  exact first.trans_eq (by rw [vEq])

end

end B13BoundedStepProductSavingProof

end

/- Large q low far saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def largeQLowFarRow (n : ℕ) (row : ℕ × ℕ) : ℂ :=
  ∑ g ∈ swappedHighDivisors n (leftBilinearStep row), ∑ k ∈ Icc 224 2047, largeQLowFarWindow n row g k

def largeQLowFarResidueSlice (n : ℕ) : ℂ :=
  ∑ row ∈ outerRightRows n, leftBilinearWeight n row*largeQLowFarRow n row

theorem norm_large_q_low_far_row_le {n : ℕ} {j : (ℕ × ℕ)}
    (hj : j ∈ outerRightRows n) (ns : 1 < n)
    {T : ℝ} (T1 : 1 ≤ T) (TL : logBudget n ≤ T)
    (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T)
    (divN : ∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) :
    ‖largeQLowFarRow n j‖ ≤
      (1824*(592*(n : ℝ)^(4095/4096 : ℝ)*T^3*logBudget n^3)*T)*(1/(leftBilinearStep j : ℝ)) := by
  let B := 592*(n : ℝ)^(4095/4096 : ℝ)*T^3*logBudget n^3
  let M := (leftBilinearStep j : ℝ)
  let V := 1824*B/M
  let G := swappedHighDivisors n (leftBilinearStep j)
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have V0 : 0 ≤ V := by unfold V M B; positivity
  have natCard : G.card ≤ n.divisors.card := card_le_card (filter_subset _ n.divisors)
  have nG : (G.card : ℝ) ≤ T := (show (G.card : ℝ) ≤ (n.divisors.card : ℝ) by exact_mod_cast natCard).trans (divN n le_rfl)
  have per (g : ℕ) (hg : g ∈ G) : ‖∑ k ∈ Icc 224 2047, largeQLowFarWindow n j g k‖ ≤ V := by
    obtain ⟨data,gS,_,gq⟩ := mem_filter.mp hg
    have gn := (Nat.mem_divisors.mp data).1
    have g0 := Nat.pos_of_dvd_of_pos gn (zero_lt_one.trans ns)
    calc
      _ ≤ ∑ k ∈ Icc 224 2047, ‖largeQLowFarWindow n j g k‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Icc 224 2047, B/M := sum_le_sum fun k hk =>
        norm_large_q_low_far_window_le hj g0 gn gq gS hk ns T1 TL divisors
      _ = V := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,V]; norm_num; ring
  change ‖∑ g ∈ G, ∑ k ∈ Icc 224 2047, largeQLowFarWindow n j g k‖ ≤ (1824*B*T)*(1/M)
  calc
    _ ≤ ∑ g ∈ G, ‖∑ k ∈ Icc 224 2047, largeQLowFarWindow n j g k‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ G, V := sum_le_sum per
    _ = (G.card : ℝ)*V := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ T*V := mul_le_mul_of_nonneg_right nG V0
    _ = _ := by unfold V M; ring

private theorem norm_large_q_low_far_slice_le {n : ℕ} (nBig : 2 ≤ n)
    {T : ℝ} (T1 : 1 ≤ T) (TL : logBudget n ≤ T) (divisors : ∀ u ≤ 4*n^3, (u.divisors.card : ℝ) ≤ T) :
    ‖largeQLowFarResidueSlice n‖ ≤ 1079808*(n : ℝ)^(4095/4096 : ℝ)*T^7*logBudget n^5 := by
  let L := logBudget n
  let C := n
  let B := 592*(n : ℝ)^(4095/4096 : ℝ)*T^3*L^3
  let W := T^3*L
  let J := outerRightRows n
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have T0 := zero_le_one.trans T1
  have B0 : 0 ≤ B := by unfold B; positivity
  have W0 : 0 ≤ W := by unfold W; positivity
  have n1 : 1 ≤ n := (show 1 ≤ 2 by decide).trans nBig
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have nPos : (0 : ℝ) < n := zero_lt_one.trans_le nR
  have C1 : 1 ≤ C := n1
  have Cn : (C : ℝ) ≤ (n : ℝ) := le_rfl
  have Cnat : C ≤ n := by exact_mod_cast Cn
  have divN (u : ℕ) (h : u ≤ n) : (u.divisors.card : ℝ) ≤ T := by
    have nn : n ≤ 4*n^3 := calc
      n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
      _ ≤ _ := by omega
    exact divisors u (h.trans nn)
  have ns : 1 < n := nBig
  have massH : (∑ m ∈ Icc 1 C, 1/(m : ℝ)) ≤ L := calc
    _ = (harmonic C : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    _ ≤ 1+Real.log C := by exact_mod_cast harmonic_le_one_add_log C
    _ ≤ L := by
      unfold L logBudget
      exact add_le_add_right (Real.log_le_log (by exact_mod_cast C1)
        (Cn.trans (by linarith : (n : ℝ) ≤ (n : ℝ)+2))) _
  have step (j : (ℕ × ℕ)) (hj : j ∈ J) : leftBilinearStep j ∈ Icc 1 C :=
    bilateral_left_step_range (mem_filter.mp hj).1
  have weighted : (∑ j ∈ J, ‖leftBilinearWeight n j‖*(1/(leftBilinearStep j : ℝ))) ≤ W*L := by
    refine (sum_norm_mul_le_of_step_mass J leftBilinearStep (leftBilinearWeight n) (fun m => 1/(m : ℝ))
      step (fun _ _ => by positivity) ?_).trans (mul_le_mul_of_nonneg_left massH W0)
    intro m hm
    have h : m ∈ Icc 1 n := mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans Cnat⟩
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_left_step_mass (zero_lt_one.trans_le n1) T0 divN m h)
  have each (j : (ℕ × ℕ)) (hj : j ∈ J) :
      ‖largeQLowFarRow n j‖ ≤ (1824*B*T)*(1/(leftBilinearStep j : ℝ)) := by
    exact norm_large_q_low_far_row_le hj ns T1 TL divisors divN
  unfold largeQLowFarResidueSlice
  change ‖∑ j ∈ J, leftBilinearWeight n j*largeQLowFarRow n j‖ ≤ _
  calc
    _ ≤ ∑ j ∈ J, ‖leftBilinearWeight n j*largeQLowFarRow n j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ‖leftBilinearWeight n j‖*((1824*B*T)*(1/(leftBilinearStep j : ℝ))) := by
      refine sum_le_sum fun j hj => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (each j hj) (norm_nonneg _)
    _ = (1824*B*T)*(∑ j ∈ J, ‖leftBilinearWeight n j‖*(1/(leftBilinearStep j : ℝ))) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (1824*B*T)*(W*L) := mul_le_mul_of_nonneg_left weighted (by positivity)
    _ = _ := by unfold B W L; ring

theorem large_q_low_far_residue_saving : saving largeQLowFarResidueSlice := by
  intro ε he
  obtain ⟨D,D1,db⟩ := divisor_envelope_at_power 262144 (by decide)
  let C := 1079808*(4*D)^7
  have hlimit : Tendsto (fun n : ℕ => (n : ℝ)^(-(38/262144) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 38/262144)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(38/262144) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlimit
  have bound : ∀ᶠ n : ℕ in atTop, ‖largeQLowFarResidueSlice n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_log_budget_le_power (1/262144) (by norm_num),
      hl.eventually_lt_const he] with n nBig logb final
    have hn : 1 ≤ n := (show 1 ≤ (2 : ℕ) by decide).trans nBig
    have nr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have np : (0 : ℝ) < n := zero_lt_one.trans_le nr
    have D0 := zero_le_one.trans D1
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/262144 : ℝ)
    let T := (4*D)*X^3
    have X1 : 1 ≤ X := Real.one_le_rpow nr (by norm_num)
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) D1) (one_le_pow₀ X1)
    have TL : logBudget n ≤ T := logb.trans (by
      have xx : X ≤ X^3 := by simpa only [pow_one] using pow_le_pow_right₀ X1 (show 1 ≤ 3 by decide)
      exact xx.trans (le_mul_of_one_le_left (by positivity) (by nlinarith only [D1])))
    have cp : (4 : ℝ)^(1/262144 : ℝ) ≤ 4 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have divs (m : ℕ) (hm : m ≤ 4*n^3) : (m.divisors.card : ℝ) ≤ T := by
      calc
        _ ≤ D*((4*n^3 : ℕ) : ℝ)^(1/(262144 : ℕ) : ℝ) := db (4*n^3) m hm
        _ = D*((4 : ℝ)^(1/262144 : ℝ)*X^3) := by
          push_cast
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul np.le]
          unfold X
          rw [← Real.rpow_mul_natCast np.le]
          norm_num
        _ ≤ D*(4*X^3) := by gcongr
        _ = _ := by unfold T; ring
    have ex : (n : ℝ)^(4095/4096 : ℝ)*X^26 = (n : ℝ)^(-(38/262144) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast np.le, ← Real.rpow_add np, ← Real.rpow_add_one np.ne']
      congr 1
      norm_num
    calc
      _ ≤ 1079808*(n : ℝ)^(4095/4096 : ℝ)*T^7*logBudget n^5 := norm_large_q_low_far_slice_le nBig T1 TL divs
      _ ≤ 1079808*(n : ℝ)^(4095/4096 : ℝ)*T^7*X^5 := by gcongr
      _ = C*((n : ℝ)^(4095/4096 : ℝ)*X^26) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(38/262144) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right final.le np.le
  obtain ⟨N,h⟩ := eventually_atTop.mp bound
  exact ⟨N,fun n hn _ => h n hn⟩

end

end B13BoundedStepProductSavingProof

end

/- Large q low far window selection -/
section

namespace B13BoundedStepProductSavingProof

open Finset ArithmeticFunction DyadicMixedB4Scale
open scoped Classical

noncomputable section

set_option maxHeartbeats 2200000 in
def largeQLowFarSelection (n : ℕ) (row : ℕ × ℕ) (g k : ℕ) : Finset RightLowWaveIndex :=
  let m := leftBilinearStep row
  (rightLowWaveItems n).filter fun j =>
    let w := rightLowWaveStep j
    j.1.Prime ∧ ¬j.1 ∣ n ∧ j.2 ∈ largeQLowFarFactorBlock n k ∧
      w.gcd m=g ∧ largeQLowFarStepLower n m < w ∧ w ≤ largeQLowFarStepUpper n m

set_option maxHeartbeats 2200000 in
theorem expanded_high_modulus_cap_le_wider_low_far {n : ℕ} (n0 : 0 < n) :
    expandedHighModulusCap n ≤ widerLowFarModulusCap n :=
  (expanded_high_modulus_cap_le_short_low n0).trans
    (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n0)
      (by norm_num : (133/256 : ℝ) ≤ 535/1024)))

set_option maxHeartbeats 2200000 in
theorem large_q_low_far_step_above_left {n m w : ℕ} (m0 : 0 < m) (mN : m ≤ n) (msq : m^2 ≤ n)
    (step : largeQLowFarStepLower n m < w) : m < w :=
  (((square_le_implies_step_le_expanded_high_cap m0 msq).trans
    (expanded_high_modulus_cap_le_wider_low_far (m0.trans_le mN))).trans (le_max_left _ _)).trans_lt step

set_option maxHeartbeats 2200000 in
private theorem large_q_low_far_root_size {n w : ℕ} (n0 : 0 < n) (hw : widerLowFarModulusCap n < w) :
    n ≤ w^2 := by
  have nr : (1 : ℝ) ≤ n := by exact_mod_cast n0
  have p : (n : ℝ)^(1/2 : ℝ) ≤ (w : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le nr (by norm_num : (1/2 : ℝ) ≤ 535/1024)).trans
      ((Nat.lt_floor_add_one ((n : ℝ)^(535/1024 : ℝ))).le.trans (by
        change (widerLowFarModulusCap n : ℝ)+1 ≤ (w : ℝ)
        exact_mod_cast Nat.succ_le_of_lt hw))
  rw [← Real.sqrt_eq_rpow] at p
  exact_mod_cast (Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (w : ℝ))).mp p

set_option maxHeartbeats 2200000 in
theorem large_q_low_far_window_eq_selected {n g k : ℕ} {row : ℕ × ℕ}
    (hrow : row ∈ outerRightRows n)
    (g0 : 0 < g) (gn : g ∣ n) (gm : g ∣ leftBilinearStep row) :
    largeQLowFarWindow n row g k = ∑ j ∈ largeQLowFarSelection n row g k,
      swappedLowResidueTerm n (leftBilinearStep row) j := by
  let m := leftBilinearStep row
  let v := m/g
  let l₀ := largeQLowFarStepLower n m
  let r₀ := largeQLowFarStepUpper n m
  let l := l₀/g
  let r := r₀/g
  let aLo := largeQLowFarFactorLower n k
  let aHi := min (cutoffU n) (swappedHighFactorFloor n (k+1))
  let S := largeQLowFarCofactorCap n m g k
  let I := largeQLowFarFactors n m g k
  let J := intIntervalModUnits v 0 S
  let lo (a : ℕ) : ℤ := max ((l/a : ℕ) : ℤ) (cutoffU n : ℤ)
  let hi (a : ℕ) : ℤ := min ((r/a : ℕ) : ℤ) (min n (rightLargeCofactorCut n) : ℕ)
  let gate (a : ℕ) (j : ℤ) : Prop := lo a < j ∧ j ≤ hi a
  let admissible (j : ℤ) : Prop := j.toNat.Prime ∧ ¬j.toNat ∣ n
  let P := (J ×ˢ I).filter fun t => gate t.2 t.1 ∧ admissible t.1
  let f (t : ℤ × ℕ) : RightLowWaveIndex := ⟨t.1.toNat,g*t.2⟩
  let F (a : ℕ) (j : ℤ) := centeredIntIntervalResidue v 0
    (((n/g-m/g : ℕ) : ℤ)/((a*j.toNat : ℕ) : ℤ)) (((n/g : ℕ) : ZMod v)*((a : ZMod v)*(j : ZMod v))⁻¹)
  let W (t : ℤ × ℕ) := swappedLowShortWeight g t.2*(vonMangoldt t.1.toNat : ℂ)*F t.2 t.1
  have data := mem_filter.mp hrow
  have steps := mem_Icc.mp (bilateral_left_step_range data.1)
  have m0 : 0 < m := steps.1
  have mN : m ≤ n := steps.2
  have n0 := m0.trans_le mN
  have mSquare : m^2 ≤ n := data.2.1
  have gV : g*v=m := Nat.mul_div_cancel' gm
  have rN : r₀ ≤ n := (min_le_left _ _).trans (extended_wide_step_le n0)
  have aBounds (a : ℕ) : (aLo/g < a ∧ a ≤ aHi/g) ↔ aLo < g*a ∧ g*a ≤ aHi := by
    rw [Nat.div_lt_iff_lt_mul g0,Nat.le_div_iff_mul_le g0,Nat.mul_comm a g]
  have pBounds (u : ℕ) : (l < u ∧ u ≤ r) ↔ l₀ < g*u ∧ g*u ≤ r₀ := by
    change l₀/g < u ∧ u ≤ r₀/g ↔ _
    rw [Nat.div_lt_iff_lt_mul g0,Nat.le_div_iff_mul_le g0,Nat.mul_comm u g]
  have factsI {a : ℕ} (ha : a ∈ I) : aLo/g < a ∧ a ≤ aHi/g ∧ a.Coprime v :=
    ⟨(mem_Ioc.mp (mem_filter.mp ha).1).1,(mem_Ioc.mp (mem_filter.mp ha).1).2,(mem_filter.mp ha).2⟩
  have factsJ {b : ℤ} (hb : b ∈ J) : b ∈ Ioc (0 : ℤ) (S : ℤ) ∧ IsUnit (b : ZMod v) := by
    simpa only [J,intIntervalModUnits,mem_filter] using hb
  have zCast {b : ℤ} (b0 : 0 ≤ b) : (b.toNat : ZMod v) = (b : ZMod v) := by
    simpa only [Int.cast_natCast] using congrArg (fun x : ℤ => (x : ZMod v)) (Int.toNat_of_nonneg b0)
  have gateBounds {a : ℕ} (a0 : 0 < a) {b : ℤ} (b0 : 0 ≤ b) :
      gate a b ↔ (l < a*b.toNat ∧ a*b.toNat ≤ r) ∧
        cutoffU n < b.toNat ∧ b.toNat ≤ min n (rightLargeCofactorCut n) := by
    unfold gate lo hi
    rw [← Int.toNat_of_nonneg b0]
    simp only [max_lt_iff, le_min_iff, Int.ofNat_lt, Int.ofNat_le, Int.toNat_natCast,
      Nat.div_lt_iff_lt_mul a0, Nat.le_div_iff_mul_le a0, Nat.mul_comm b.toNat a]
    tauto
  have lift_mem (t : ℤ × ℕ) (ht : t ∈ P) : f t ∈ largeQLowFarSelection n row g k := by
    obtain ⟨hb,ha⟩ := mem_product.mp (mem_filter.mp ht).1
    obtain ⟨aLow,aTop,ac⟩ := factsI ha
    have a0 := (Nat.zero_le _).trans_lt aLow
    obtain ⟨bR,bUnit⟩ := factsJ hb
    have b0 := (mem_Ioc.mp bR).1
    have ab := (aBounds t.2).mp ⟨aLow,aTop⟩
    have ⟨pb,pl,pr⟩ := (gateBounds a0 b0.le).mp (mem_filter.mp ht).2.1
    have range := (pBounds _).mp pb
    have hp := (mem_filter.mp ht).2.2
    have qU : g*t.2 ≤ cutoffU n := ab.2.trans (min_le_left _ _)
    have prod : (g*t.2)*t.1.toNat=g*(t.2*t.1.toNat) := by ring
    have normStep : rightLowWaveStep (f t)=g*(t.2*t.1.toNat) := prod
    have items : f t ∈ rightLowWaveItems n := by
      refine mem_sigma.mpr ⟨mem_Ioc.mpr ⟨pl,pr⟩,mem_Icc.mpr ⟨mul_pos g0 a0,le_min qU ?_⟩⟩
      exact (Nat.le_div_iff_mul_le ((Nat.zero_le _).trans_lt pl)).mpr (prod ▸ range.2.trans rN)
    have cop : (t.2*t.1.toNat).Coprime v := by
      have bp : t.1.toNat.Coprime v :=
        (ZMod.isUnit_iff_coprime _ _).mp (zCast b0.le ▸ bUnit)
      exact ac.mul_left bp
    have gcd : (rightLowWaveStep (f t)).gcd m=g := by
      rw [normStep,← gV,Nat.gcd_mul_left,cop.gcd_eq_one,mul_one]
    exact mem_filter.mpr ⟨items,hp.1,hp.2,mem_Ioc.mpr ab,gcd,normStep ▸ range.1,normStep ▸ range.2⟩
  have lift_surj (j : RightLowWaveIndex) (hj : j ∈ largeQLowFarSelection n row g k) :
      ∃ t ∈ P, f t = j := by
    obtain ⟨items,hp,hpn,fac,gcd,sl,sr⟩ := mem_filter.mp hj
    have qs : g ∣ j.2 := gcd ▸ right_low_common_gcd_dvd_short_factor hp hpn (gcd.symm ▸ gn)
    let a := j.2/g
    let b := j.1
    have aEq : g*a=j.2 := Nat.mul_div_cancel' qs
    have aB : aLo/g < a ∧ a ≤ aHi/g := (aBounds a).mpr (by rw [aEq]; exact mem_Ioc.mp fac)
    have a0 := (Nat.zero_le _).trans_lt aB.1
    have pR := mem_Ioc.mp (mem_sigma.mp items).1
    have b0 : 0 < b := (Nat.zero_le _).trans_lt pR.1
    have wEq : rightLowWaveStep j = g*(a*b) := by
      rw [← mul_assoc,aEq]
      rfl
    have wG : rightLowWaveStep j/g = a*b := by rw [wEq,Nat.mul_div_cancel_left _ g0]
    have pb := (pBounds (a*b)).mpr (by rw [← wEq]; exact ⟨sl,sr⟩)
    have bS : b ≤ S := (Nat.le_div_iff_mul_le (Nat.succ_pos (aLo/g))).mpr (by
      rw [Nat.mul_comm]; exact (Nat.mul_le_mul_right b aB.1).trans pb.2)
    have cop : (a*b).Coprime v := by
      have h := Nat.coprime_div_gcd_div_gcd (m := rightLowWaveStep j) (n := m) (gcd.symm ▸ g0)
      rwa [gcd,wG] at h
    have jI : a ∈ I := mem_filter.mpr ⟨mem_Ioc.mpr aB,cop.coprime_dvd_left (dvd_mul_right _ _)⟩
    have jJ : (b : ℤ) ∈ J := by
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨by exact_mod_cast b0,by exact_mod_cast bS⟩,?_⟩
      rw [Int.cast_natCast]
      exact (ZMod.isUnit_iff_coprime _ _).mpr (cop.coprime_dvd_left (dvd_mul_left _ _))
    have ga : gate a (b : ℤ) := (gateBounds a0 (by positivity)).mpr (by
      simp only [Int.toNat_natCast]; exact ⟨pb,pR⟩)
    refine ⟨((b : ℤ),a),mem_filter.mpr ⟨mem_product.mpr ⟨jJ,jI⟩,ga,?_⟩,?_⟩
    · simpa only [admissible,Int.toNat_natCast] using And.intro hp hpn
    · change (⟨(b : ℤ).toNat,g*a⟩ : RightLowWaveIndex) = j
      rw [Int.toNat_natCast,aEq]
  have val (t : ℤ × ℕ) (ht : t ∈ P) : W t=swappedLowResidueTerm n m (f t) := by
    obtain ⟨items,_,_,_,gcd,loStep,_⟩ := mem_filter.mp (lift_mem t ht)
    let w := rightLowWaveStep (f t)
    have large : widerLowFarModulusCap n < w := (le_max_left _ _).trans_lt loStep
    have high := large_q_low_far_root_size n0 large
    have order := large_q_low_far_step_above_left m0 mN mSquare loStep
    have e := right_low_residue_above_root_eq_single_prefix items high order m0 mN (gcd.symm ▸ gn)
    dsimp only at e
    change w.gcd m=g at gcd
    rw [gcd] at e
    have wG : w/g = t.2*t.1.toNat := by
      change (g*t.2*t.1.toNat)/g = _
      rw [mul_assoc,Nat.mul_div_cancel_left _ g0]
    have cast : (t.1.toNat : ZMod v) = (t.1 : ZMod v) :=
      zCast (mem_Ioc.mp (factsJ (mem_product.mp (mem_filter.mp ht).1).1).1).1.le
    have phase : ((t.2*t.1.toNat : ℕ) : ZMod v) = (t.2 : ZMod v)*(t.1 : ZMod v) := by
      rw [Nat.cast_mul,cast]
    rw [wG,Int.natCast_ediv,phase] at e
    unfold W swappedLowResidueTerm swappedLowShortWeight rightLowWaveWeight F
    rw [e]
  have flat : largeQLowFarWindow n row g k = ∑ t ∈ P, W t := by
    change gatedBilinearSum I J (swappedLowShortWeight g) (swappedLowPrimeWeight n) lo hi F = _
    rw [gated_bilinear_sum_eq_pair_sum]
    unfold P
    rw [sum_filter,sum_product]
    refine sum_congr rfl fun b hb => sum_congr rfl fun a ha => ?_
    change (if gate a b then _ else 0) = (if gate a b ∧ admissible b then W (b,a) else 0)
    by_cases h : gate a b
    · have a0 := (Nat.zero_le _).trans_lt (factsI ha).1
      have b0 := (mem_Ioc.mp (factsJ hb).1).1.le
      have bn := ((gateBounds a0 b0).mp h).2.2.trans (min_le_left _ _)
      by_cases p : admissible b
      · have on : b.toNat.Prime ∧ ¬b.toNat ∣ n ∧ b.toNat ≤ n := ⟨p.1,p.2,bn⟩
        rw [ite_eq_left h,ite_eq_left (And.intro h p)]
        simp only [W,swappedLowPrimeWeight,ite_eq_left on]
      · have off : ¬(b.toNat.Prime ∧ ¬b.toNat ∣ n ∧ b.toNat ≤ n) := fun hx => p ⟨hx.1,hx.2.1⟩
        rw [ite_eq_left h,ite_eq_right (fun hx : gate a b ∧ admissible b => p hx.2)]
        simp only [swappedLowPrimeWeight,ite_eq_right off,mul_zero,zero_mul]
    · simp [h]
  rw [flat]
  refine sum_bij (fun t _ => f t) lift_mem ?_ ?_ val
  swap
  · intro i hi
    obtain ⟨t,ht,eqt⟩ := lift_surj i hi
    exact ⟨t,ht,eqt⟩
  intro t ht u hu heq
  have positive {x : ℤ × ℕ} (hx : x ∈ P) : 0 ≤ x.1 :=
    (mem_Ioc.mp (factsJ (mem_product.mp (mem_filter.mp hx).1).1).1).1.le
  have fst : t.1.toNat=u.1.toNat := congrArg Sigma.fst heq
  have snd : g*t.2=g*u.2 := congrArg (fun j : RightLowWaveIndex => j.2) heq
  exact Prod.ext (by rw [← Int.toNat_of_nonneg (positive ht),← Int.toNat_of_nonneg (positive hu),fst])
    (Nat.eq_of_mul_eq_mul_left g0 snd)

end

end B13BoundedStepProductSavingProof

end

/- Large q low far row selection -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical

noncomputable section

theorem large_q_low_far_factor_blocks_cover {n q : ℕ} (n1 : 1 ≤ n)
    (qL : largeQLowFarShortCut n < q) (qH : q ≤ cutoffU n) :
    ∃! k, k ∈ Icc 224 2047 ∧ q ∈ largeQLowFarFactorBlock n k := by
  have nr : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have cut : rightVaughanCut n ≤ largeQLowFarShortCut n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nr (by norm_num : (1/256 : ℝ) ≤ 7/1024))
  have cap : cutoffU n ≤ swappedHighFactorCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nr (by norm_num : (1/16 : ℝ) ≤ 31/96))
  obtain ⟨k,⟨km,kq⟩,uniq⟩ := swapped_low_factor_blocks_cover n1 (cut.trans_lt qL) qH
  have kLo : 224 ≤ k := by
    by_contra! small
    have ke : ((k+1 : ℕ) : ℝ) ≤ 224 := by exact_mod_cast (show k+1 ≤ 224 by omega)
    have lim : swappedHighFactorFloor n (k+1) ≤ largeQLowFarShortCut n :=
      Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nr (by linarith only [ke]))
    exact (not_le_of_gt qL) (((mem_Ioc.mp kq).2.trans (min_le_right _ _)).trans lim)
  have oldLo := (le_max_right (rightVaughanCut n) (swappedHighFactorFloor n k)).trans_lt (mem_Ioc.mp kq).1
  have oldHi := (mem_Ioc.mp kq).2.trans (min_le_right _ _)
  refine ⟨k,⟨mem_Icc.mpr ⟨kLo,(mem_Icc.mp km).2⟩,mem_Ioc.mpr ⟨max_lt qL oldLo,le_min qH oldHi⟩⟩,?_⟩
  intro k' h
  obtain ⟨range,mem⟩ := h
  have m := mem_Ioc.mp mem
  exact uniq k' ⟨mem_Icc.mpr ⟨(by decide : 128 ≤ 224).trans (mem_Icc.mp range).1,(mem_Icc.mp range).2⟩,
    mem_Ioc.mpr ⟨max_lt (cut.trans_lt qL) ((le_max_right _ _).trans_lt m.1),
      le_min (qH.trans cap) (m.2.trans (min_le_right _ _))⟩⟩

def largeQLowFarRowItems (n : ℕ) (row : ℕ × ℕ) : Finset RightLowWaveIndex :=
  let m := leftBilinearStep row
  (rightLowWaveItems n).filter fun j =>
    let w := rightLowWaveStep j
    w.gcd m ∈ swappedHighDivisors n m ∧
      largeQLowFarStepLower n m < w ∧ w ≤ largeQLowFarStepUpper n m ∧
      largeQLowFarShortCut n < j.2 ∧ j.1.Prime ∧ ¬j.1 ∣ n

theorem large_q_low_far_row_eq_selected {n : ℕ} {row : ℕ × ℕ} (hr : row ∈ outerRightRows n) :
    largeQLowFarRow n row = ∑ j ∈ largeQLowFarRowItems n row,
      swappedLowResidueTerm n (leftBilinearStep row) j := by
  let m := leftBilinearStep row
  let I := largeQLowFarRowItems n row
  let G := swappedHighDivisors n m
  let K := Icc 224 2047
  let d (j : RightLowWaveIndex) := (rightLowWaveStep j).gcd m
  let w := swappedLowResidueTerm n m
  have step := mem_Icc.mp (bilateral_left_step_range (mem_filter.mp hr).1)
  have n1 : 1 ≤ n := step.1.trans step.2
  have mapsG : ∀ j ∈ I, d j ∈ G := fun _ hj => (mem_filter.mp hj).2.1
  change largeQLowFarRow n row = ∑ j ∈ I, w j
  rw [← sum_fiberwise_of_maps_to mapsG w]
  unfold largeQLowFarRow
  refine sum_congr rfl fun g hg => ?_
  let I₁ := I.filter fun j => d j=g
  have data := mem_filter.mp hg
  have gn := (Nat.mem_divisors.mp data.1).1
  have g0 := Nat.pos_of_dvd_of_pos gn n1
  have gm := data.2.2.2
  have eqFilter (k : ℕ) : largeQLowFarSelection n row g k =
      I₁.filter (fun j => j.2 ∈ largeQLowFarFactorBlock n k) := by
    ext j
    constructor
    · intro hj
      obtain ⟨items,prime,nd,fac,gg,lo,up⟩ := mem_filter.mp hj
      have dg : d j ∈ G := by change (rightLowWaveStep j).gcd m ∈ G; rw [gg]; exact hg
      have qL : largeQLowFarShortCut n < j.2 := (le_max_left _ _).trans_lt (mem_Ioc.mp fac).1
      have jI : j ∈ I := mem_filter.mpr ⟨items,dg,lo,up,qL,prime,nd⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨jI,gg⟩,fac⟩
    · intro hj
      obtain ⟨j₁,fac⟩ := mem_filter.mp hj
      obtain ⟨j₀,gg⟩ := mem_filter.mp j₁
      obtain ⟨items,_,lo,up,_,prime,nd⟩ := mem_filter.mp j₀
      exact mem_filter.mpr ⟨items,prime,nd,fac,gg,lo,up⟩
  calc
    (∑ k ∈ K, largeQLowFarWindow n row g k) =
        ∑ k ∈ K, ∑ j ∈ I₁.filter (fun j => j.2 ∈ largeQLowFarFactorBlock n k), w j := by
      refine sum_congr rfl fun k hk => ?_
      rw [← eqFilter k]
      exact large_q_low_far_window_eq_selected hr g0 gn gm
    _ = ∑ j ∈ I₁, ∑ k ∈ K, if j.2 ∈ largeQLowFarFactorBlock n k then w j else 0 := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = ∑ j ∈ I₁, w j := by
      refine sum_congr rfl fun j hj => ?_
      have j₀ : j ∈ I := (mem_filter.mp hj).1
      have info := mem_filter.mp j₀
      have qL : largeQLowFarShortCut n < j.2 := info.2.2.2.2.1
      have qH : j.2 ≤ cutoffU n := (mem_Icc.mp (mem_sigma.mp info.1).2).2.trans (min_le_left _ _)
      obtain ⟨k,⟨kMem,kq⟩,uniq⟩ := large_q_low_far_factor_blocks_cover n1 qL qH
      rw [sum_eq_single_of_mem k kMem]
      · exact ite_eq_left kq
      · intro k' hk' neq
        exact ite_eq_right (fun h => neq (uniq k' ⟨hk',h⟩))

end

end B13BoundedStepProductSavingProof

end

/- Large q low far original saving -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def largeQLowFarOriginalSlice (n : ℕ) : ℂ :=
  ∑ row ∈ outerRightRows n, leftBilinearWeight n row *
    ∑ j ∈ largeQLowFarRowItems n row, rightLowWaveWeight j *
      (pairResidueError n (leftBilinearStep row) (rightLowWaveStep j) 0 (n/leftBilinearStep row)
        0 (rightLowWaveUpper n j) : ℂ)

def largeQLowFarVolumeCorrection (n : ℕ) : ℂ :=
  pairResidueSwapFamily n (outerRightRows n) (rightLowWaveItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n)
    (leftBilinearWeight n) rightLowWaveWeight
    (fun i j => j ∈ largeQLowFarRowItems n i)

theorem large_q_low_far_original_eq_slice_add_correction (n : ℕ) :
    largeQLowFarOriginalSlice n = largeQLowFarResidueSlice n + largeQLowFarVolumeCorrection n := by
  unfold largeQLowFarOriginalSlice largeQLowFarResidueSlice largeQLowFarVolumeCorrection pairResidueSwapFamily
  rw [← sum_add_distrib]
  refine sum_congr rfl fun row hr => ?_
  rw [large_q_low_far_row_eq_selected hr]
  rw [mul_sum,mul_sum]
  let gate (j : RightLowWaveIndex) := j ∈ largeQLowFarRowItems n row
  have expand (f : RightLowWaveIndex → ℂ) :
      (∑ j ∈ largeQLowFarRowItems n row, f j) =
        ∑ j ∈ rightLowWaveItems n, if gate j then f j else 0 := by
    unfold largeQLowFarRowItems
    rw [sum_filter]
    refine sum_congr rfl fun j hj => ?_
    simp [gate,largeQLowFarRowItems,hj]
  rw [expand,expand,← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : j ∈ largeQLowFarRowItems n row
  · simp only [gate,ite_eq_left h]
    unfold swappedLowResidueTerm
    ring
  · simp only [gate,ite_eq_right h,zero_add]

private theorem norm_large_q_low_far_volume_correction_le {n : ℕ} (n0 : 0 < n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖largeQLowFarVolumeCorrection n‖ ≤ 24*(n : ℝ)^(21/32 : ℝ)*T^7*logBudget n^3 := by
  let A := extendedWideStepCap n
  let N := (n : ℝ)
  let L := logBudget n
  let W := T^3*L
  have nr : 0 < N := by change (0 : ℝ) < (n : ℝ); exact_mod_cast n0
  have A0 := extended_wide_step_pos n0
  have An := extended_wide_step_le n0
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have W0 : 0 ≤ W := by unfold W; positivity
  have leftRange (i : ℕ × ℕ) (hi : i ∈ outerRightRows n) : leftBilinearStep i ∈ Icc 1 A := by
    have h := mem_filter.mp hi
    have step := mem_Icc.mp (bilateral_left_step_range h.1)
    exact mem_Icc.mpr ⟨step.1,
      (high_step_le_medium_of_square_le step.1 h.2.1).trans (old_step_cap_le_extended n)⟩
  have rightRange (j : RightLowWaveIndex) (hj : j ∈ rightLowWaveItems n) : rightLowWaveStep j ∈ Icc 1 A :=
    mem_Icc.mpr ⟨(mem_Icc.mp (bilateral_right_low_step_range hj)).1,
      (right_low_step_le_proved_medium_cap hj).trans (old_step_cap_le_extended n)⟩
  have leftMass (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ i ∈ (outerRightRows n).filter (fun i => leftBilinearStep i=m), ‖leftBilinearWeight n i‖) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _)) (fun _ _ _ => norm_nonneg _)).trans
      (norm_bilateral_left_step_mass n0 T0 divisors m (Icc_subset_Icc_right An hm))
  have rightMass (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ j ∈ (rightLowWaveItems n).filter (fun j => rightLowWaveStep j=m), ‖rightLowWaveWeight j‖) ≤ W :=
    norm_bilateral_right_low_step_mass T1 divisors m (Icc_subset_Icc_right An hm)
  have logA : 1+Real.log (A : ℝ) ≤ L := by
    have h : (A : ℝ) ≤ N := by
      change (extendedWideStepCap n : ℝ) ≤ (n : ℝ)
      exact_mod_cast An
    have p : (0 : ℝ) < A := by exact_mod_cast A0
    unfold L logBudget
    linarith only [Real.log_le_log p (show (A : ℝ) ≤ (n : ℝ)+2 from h.trans (by simp [N]))]
  have aCap : (A : ℝ) ≤ N^(21/32 : ℝ) := Nat.floor_le (by positivity)
  have h := norm_pair_residue_swap_family_le n A n0 A0 (outerRightRows n) (rightLowWaveItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) rightLowWaveStep (fun _ => 0)
    (rightLowWaveUpper n) (leftBilinearWeight n) rightLowWaveWeight
    (fun i j => j ∈ largeQLowFarRowItems n i) W0 leftRange rightRange leftMass rightMass
  calc
    _ ≤ 24*W^2*(A : ℝ)*(1+Real.log (A : ℝ))*(n.divisors.card : ℝ) := h
    _ ≤ 24*W^2*N^(21/32 : ℝ)*L*T := by gcongr; exact divisors n le_rfl
    _ = _ := by unfold W L N; ring

theorem large_q_low_far_volume_correction_saving : saving largeQLowFarVolumeCorrection := by
  intro ε he
  obtain ⟨D,D1,dBound⟩ := divisor_envelope_at_power 4096 (by decide)
  let C := 24*D^7
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-(1398/4096) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1398/4096)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(1398/4096) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have est : ∀ᶠ n : ℕ in atTop, ‖largeQLowFarVolumeCorrection n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le_power (1/4096) (by norm_num),
      scaled.eventually_lt_const he] with n hn logb small
    have nr : (0 : ℝ) < n := by exact_mod_cast hn
    have L0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/4096 : ℝ)
    let T := D*X
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1
      (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))
    have ex : (n : ℝ)^(21/32 : ℝ)*X^10 = (n : ℝ)^(-(1398/4096) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast nr.le,← Real.rpow_add nr,← Real.rpow_add_one nr.ne']
      congr 1
      norm_num
    calc
      _ ≤ 24*(n : ℝ)^(21/32 : ℝ)*T^7*logBudget n^3 :=
        norm_large_q_low_far_volume_correction_le hn T1 (dBound n)
      _ ≤ 24*(n : ℝ)^(21/32 : ℝ)*T^7*X^3 := by gcongr
      _ = C*((n : ℝ)^(21/32 : ℝ)*X^10) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(1398/4096) : ℝ))*(n : ℝ) := by rw [ex]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
  obtain ⟨N,h⟩ := eventually_atTop.mp est
  exact ⟨N,fun n hn _ => h n hn⟩

theorem large_q_low_far_original_slice_saving : saving largeQLowFarOriginalSlice := by
  intro ε he
  obtain ⟨N,h⟩ := large_q_low_far_residue_saving (ε/2) (by positivity)
  obtain ⟨M,hm⟩ := large_q_low_far_volume_correction_saving (ε/2) (by positivity)
  refine ⟨max N M,fun n hn even => ?_⟩
  rw [large_q_low_far_original_eq_slice_add_correction]
  exact (norm_add_le _ _).trans (by linarith only [h n (by omega) even,hm n (by omega) even])

end

end B13BoundedStepProductSavingProof

end

/- Large q low far geometry -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical

noncomputable section

def lowLargeQFarGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  j.1.Prime ∧ ¬j.1 ∣ n ∧ widerLowFarModulusCap n < v ∧ prefixStepGate n u v ∧
    2*n < u*v ∧ u*v ≤ highFarStripProductCap n

def lowLargeQFarKept (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  lowLargeQFarGate n i j ∧ thinHighProductCap n < u*v ∧
    u.gcd v ≤ thinHighGcdCap n ∧ u.gcd n ≤ thinHighLeftDivisorCap n ∧ u.gcd v ∣ n

theorem large_q_low_far_short_factor {n : ℕ} {j : RightLowWaveIndex}
    (hj : j ∈ rightLowWaveItems n) (h : widerLowFarModulusCap n < rightLowWaveStep j) :
    largeQLowFarShortCut n < j.2 := by
  have n0 := (mem_Icc.mp (bilateral_right_low_step_range hj)).1.trans
    (mem_Icc.mp (bilateral_right_low_step_range hj)).2
  have nr : (0 : ℝ) < n := by exact_mod_cast n0
  by_contra! hb
  have b : (j.2 : ℝ) ≤ (n : ℝ)^(7/1024 : ℝ) :=
    (show (j.2 : ℝ) ≤ (largeQLowFarShortCut n : ℝ) by exact_mod_cast hb).trans
      (Nat.floor_le (by positivity))
  have base : j.1 ≤ rightLargeCofactorCut n := (mem_Ioc.mp (mem_sigma.mp hj).1).2.trans (min_le_right _ _)
  have bound : (j.1 : ℝ) ≤ (n : ℝ)^(33/64 : ℝ) :=
    (show (j.1 : ℝ) ≤ (rightLargeCofactorCut n : ℝ) by exact_mod_cast base).trans (Nat.floor_le (by positivity))
  apply (not_le_of_gt h)
  apply Nat.le_floor
  unfold rightLowWaveStep
  push_cast
  calc
    _ ≤ (n : ℝ)^(7/1024 : ℝ)*(n : ℝ)^(33/64 : ℝ) := mul_le_mul b bound (by positivity) (by positivity)
    _ = (n : ℝ)^(535/1024 : ℝ) := by rw [← Real.rpow_add nr]; norm_num

theorem low_large_q_far_mem_iff {n : ℕ} {i : ℕ × ℕ} {j : RightLowWaveIndex}
    (large : (2 : ℝ) ≤ (n : ℝ)^(1/64 : ℝ))
    (hi : i ∈ bilateralLeftWaveItems n) (hj : j ∈ rightLowWaveItems n) :
    (i ∈ outerRightRows n ∧ j ∈ largeQLowFarRowItems n i) ↔
      leftBilinearStep i ≤ extendedWideStepCap n ∧ lowLargeQFarKept n i j := by
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  let g := u.gcd v
  have uRange := mem_Icc.mp (bilateral_left_step_range hi)
  have u0 : 0 < u := uRange.1
  have n0 : 0 < n := u0.trans_le uRange.2
  have vTop := (right_low_step_le_proved_medium_cap hj).trans (old_step_cap_le_extended n)
  have stepLower {Q : ℕ} (h : Q/u < v) : Q < u*v := by
    simpa only [Nat.mul_comm v u] using (Nat.div_lt_iff_lt_mul u0).mp h
  have divLower {Q : ℕ} (h : Q < u*v) : Q/u < v := by
    apply (Nat.div_lt_iff_lt_mul u0).mpr
    simpa only [Nat.mul_comm v u] using h
  constructor
  · rintro ⟨row,col⟩
    obtain ⟨_,sq,_,char⟩ := mem_filter.mp row
    obtain ⟨_,hdiv,low,up,_,prime,notDiv⟩ := mem_filter.mp col
    obtain ⟨data,gcdSmall,gcdMax,_⟩ := mem_filter.mp hdiv
    have gSmall : g ≤ thinHighGcdCap n := by simpa only [g,Nat.gcd_comm] using gcdSmall
    have gMax : g ≤ maximumStep n := by simpa only [g,Nat.gcd_comm] using gcdMax
    have gn : g ∣ n := by simpa only [g,Nat.gcd_comm] using (Nat.mem_divisors.mp data).1
    have uTop := (high_step_le_medium_of_square_le u0 sq).trans (old_step_cap_le_extended n)
    have inner : max (2*n/u) (max (maximumStep n^2/u) (thinHighProductCap n/u)) < v :=
      (le_max_right _ _).trans_lt low
    have prodMax : maximumStep n^2 < u*v := stepLower
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt inner)
    have prodThin : thinHighProductCap n < u*v := stepLower
      (((le_max_right _ _).trans (le_max_right _ _)).trans_lt inner)
    have far : 2*n < u*v := stepLower ((le_max_left _ _).trans_lt inner)
    have prodUp : u*v ≤ highFarStripProductCap n := by
      simpa only [Nat.mul_comm u v] using (Nat.le_div_iff_mul_le u0).mp (up.trans (min_le_right _ _))
    have vL : widerLowFarModulusCap n < v := (le_max_left _ _).trans_lt low
    exact ⟨uTop,⟨prime,notDiv,vL,⟨prodMax,gMax⟩,far,prodUp⟩,prodThin,gSmall,char,gn⟩
  · rintro ⟨uTop,⟨prime,notDiv,vL,pref,far,prodUp⟩,prodThin,gSmall,char,gn⟩
    have nr : (1 : ℝ) ≤ n := by exact_mod_cast n0
    have short : shortLowModulusCap n ≤ widerLowFarModulusCap n :=
      Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nr (by norm_num : (133/256 : ℝ) ≤ 535/1024))
    have hm := high_far_strip_row_mem large hi (v := v)
      ⟨uTop,vTop.trans (extended_step_cap_le_expanded n),short.trans_lt vL,
        pref,far,prodThin,prodUp,gSmall,char⟩
    have d : v.gcd u ∈ swappedHighDivisors n u := by
      refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_,n0.ne'⟩,?_,?_,Nat.gcd_dvd_right v u⟩
      · simpa only [g,Nat.gcd_comm] using gn
      · simpa only [g,Nat.gcd_comm] using gSmall
      · simpa only [g,Nat.gcd_comm] using pref.2
    have l : largeQLowFarStepLower n u < v :=
      max_lt vL (max_lt (divLower far) (max_lt (divLower pref.1) (divLower prodThin)))
    have r : v ≤ largeQLowFarStepUpper n u := le_min vTop
      ((Nat.le_div_iff_mul_le u0).mpr (by rw [Nat.mul_comm v u]; exact prodUp))
    exact ⟨hm,mem_filter.mpr ⟨hj,d,l,r,large_q_low_far_short_factor hj vL,prime,notDiv⟩⟩

end

end B13BoundedStepProductSavingProof

end

/- Large q low far arithmetic -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter
open scoped Classical Finset

noncomputable section

theorem low_large_q_far_partition (n : ℕ) :
    rightLowResidueFamily lowLargeQFarGate n =
      rightLowResidueFamily lowLargeQFarKept n + thinLowCut lowLargeQFarGate n := by
  unfold rightLowResidueFamily thinLowCut thinLowProductCut thinLowCommonCut thinLowTargetCut
    smallProductResidueFamily gcdResidueFamily largeLeftDivisorResidueFamily
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  by_cases d : u.gcd v ∣ n
  · by_cases h : lowLargeQFarGate n i j
    · by_cases p : u*v ≤ thinHighProductCap n
      · simp [u,v,h,p,not_lt.mpr p,lowLargeQFarKept,thinLowProductGate,rightLowResidueTerm]
      · by_cases g : u.gcd v ≤ thinHighGcdCap n
        · by_cases l : u.gcd n ≤ thinHighLeftDivisorCap n <;>
            simp [u,v,h,p,lt_of_not_ge p,g,not_lt.mpr g,l,lt_of_not_ge,lowLargeQFarKept,
              thinLowProductGate,rightLowResidueTerm,d]
        · simp [u,v,h,p,lt_of_not_ge p,g,lt_of_not_ge g,lowLargeQFarKept,thinLowProductGate,rightLowResidueTerm]
    · simp [h,lowLargeQFarKept,thinLowProductGate]
  · simp [u,v,d,rightLowResidueTerm,pairResidueError]

private theorem sum_subset_with_membership_large_q_low_far_arithmetic {α : Type*} {S T : Finset α} (h : S ⊆ T)
    (f : α → ℂ) : (∑ a ∈ S, f a) = ∑ a ∈ T, if a ∈ S then f a else 0 := by
  rw [← sum_filter]
  have eq : T.filter (fun a => a ∈ S) = S := by
    ext a
    exact ⟨fun ha => (mem_filter.mp ha).2,fun ha => mem_filter.mpr ⟨h ha,ha⟩⟩
  rw [eq]

theorem low_large_q_far_kept_eq_swapped {n : ℕ} (large : (2 : ℝ) ≤ (n : ℝ)^(1/64 : ℝ)) :
    rightLowResidueFamily lowLargeQFarKept n = largeQLowFarOriginalSlice n := by
  let I := bilateralLeftWaveItems n
  let J := rightLowWaveItems n
  let S := outerRightRows n
  let R := fun i : ℕ × ℕ => largeQLowFarRowItems n i
  let V := rightLowResidueTerm n
  have out (i : ℕ × ℕ) (h : i ∈ S) : i ∈ I := (mem_filter.mp h).1
  have inside (i : ℕ × ℕ) : R i ⊆ J := filter_subset _ _
  have a : largeQLowFarOriginalSlice n =
      ∑ i ∈ I, ∑ j ∈ J, if i ∈ S ∧ j ∈ R i then V i j else 0 := by
    unfold largeQLowFarOriginalSlice
    have move (i : ℕ × ℕ) : leftBilinearWeight n i *
        (∑ j ∈ R i, rightLowWaveWeight j *
          (pairResidueError n (leftBilinearStep i) (rightLowWaveStep j) 0
            (n/leftBilinearStep i) 0 (rightLowWaveUpper n j) : ℂ)) = ∑ j ∈ R i, V i j := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      unfold V rightLowResidueTerm
      ring
    calc
      _ = ∑ i ∈ S, ∑ j ∈ R i, V i j := sum_congr rfl (fun i _ => move i)
      _ = _ := by
        rw [sum_subset_with_membership_large_q_low_far_arithmetic (show S ⊆ I from fun i hi => out i hi)]
        refine sum_congr rfl fun i _ => ?_
        by_cases hi : i ∈ S
        · rw [ite_eq_left hi,sum_subset_with_membership_large_q_low_far_arithmetic (inside i)]
          refine sum_congr rfl fun j _ => ?_
          by_cases hj : j ∈ R i
          · rw [ite_eq_left hj,ite_eq_left (And.intro hi hj)]
          · rw [ite_eq_right hj,ite_eq_right (fun h : i ∈ S ∧ j ∈ R i => hj h.2)]
        · simp [hi]
  have b : rightLowResidueFamily lowLargeQFarKept n =
      ∑ i ∈ I, ∑ j ∈ J, if leftBilinearStep i ≤ extendedWideStepCap n ∧ lowLargeQFarKept n i j then V i j else 0 := by
    unfold rightLowResidueFamily thinHighLeftItems extendedWaveItems
    rw [thin_low_right_items_eq, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : leftBilinearStep i ≤ extendedWideStepCap n
    · simp [h,V,J]
    · simp [h,V,J]
  rw [a,b]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have equivalence := low_large_q_far_mem_iff large hi hj
  by_cases h : i ∈ S ∧ j ∈ R i
  · rw [ite_eq_left h,ite_eq_left (equivalence.mp h)]
  · have k : ¬(leftBilinearStep i ≤ extendedWideStepCap n ∧ lowLargeQFarKept n i j) :=
      fun z => h (equivalence.mpr z)
    rw [ite_eq_right h,ite_eq_right k]

theorem low_large_q_far_saving : saving (rightLowResidueFamily lowLargeQFarGate) := by
  intro ε he
  obtain ⟨N,h⟩ := large_q_low_far_original_slice_saving (ε/2) (by positivity)
  obtain ⟨M,hm⟩ := thin_low_cut_saving lowLargeQFarGate (ε/2) (by positivity)
  obtain ⟨P,hp⟩ := eventually_atTop.mp eventually_high_far_strip_scale
  refine ⟨max P (max N M), fun n hn even => ?_⟩
  rw [low_large_q_far_partition,low_large_q_far_kept_eq_swapped (hp n (by omega))]
  exact (norm_add_le _ _).trans (by linarith only [h n (by omega) even,hm n (by omega) even])

end

end B13BoundedStepProductSavingProof

end

/- Low product families -/
section

namespace B13BoundedStepProductSavingProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def lowProductsWaveGate (n u v : ℕ) : Prop :=
  expandedHighModulusCap n < v ∧ prefixStepGate n u v ∧ u*v ≤ highFarStripProductCap n

def lowProductsGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  ¬j.1 ∣ n ∧ lowProductsWaveGate n (leftBilinearStep i) (rightLowWaveStep j)

def lowPrimeProductsGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  j.1.Prime ∧ lowProductsGate n i j

def lowSmallProductCutGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  lowPrimeProductsGate n i j ∧ rightVaughanCut n < j.2 ∧
    leftBilinearStep i*rightLowWaveStep j ≤ subcriticalMediumProductCap n

theorem low_small_product_slice_saving : saving (rightLowResidueFamily lowSmallProductCutGate) := by
  have eq : rightLowResidueFamily lowSmallProductCutGate = thinLowCut lowSmallProductCutGate := by
    funext n
    unfold rightLowResidueFamily thinLowCut thinLowProductCut thinLowCommonCut thinLowTargetCut
      smallProductResidueFamily gcdResidueFamily largeLeftDivisorResidueFamily
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases h : lowSmallProductCutGate n i j
    · have product := h.2.2.trans (thin_high_product_cap_ge_old n)
      simp [h,product,not_lt.mpr product,thinLowProductGate,rightLowResidueTerm]
    · simp [h,thinLowProductGate]
  rw [eq]
  exact thin_low_cut_saving _

def lowPrimeItems (n : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter (fun j => j.1.Prime ∧ ¬j.1 ∣ n)

def lowShortQPrimeItems (n : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter (fun j => j.1.Prime ∧ ¬j.1 ∣ n ∧ j.2 ≤ rightVaughanCut n)

def lowLargeQPrimeItems (n : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter (fun j => j.1.Prime ∧ ¬j.1 ∣ n ∧ rightVaughanCut n < j.2)

def lowShortQProductGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  (j.1.Prime ∧ ¬j.1 ∣ n ∧ j.2 ≤ rightVaughanCut n) ∧
    middleLowProductGate expandedHighModulusCap shortLowModulusCap false n (leftBilinearStep i) (rightLowWaveStep j)

def lowLargeQMiddleFarGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  (j.1.Prime ∧ ¬j.1 ∣ n ∧ rightVaughanCut n < j.2) ∧
    middleLowProductGate expandedHighModulusCap shortLowModulusCap true n (leftBilinearStep i) (rightLowWaveStep j)

def lowWiderFarGate (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  (j.1.Prime ∧ ¬j.1 ∣ n) ∧
    middleLowProductGate shortLowModulusCap widerLowFarModulusCap true n (leftBilinearStep i) (rightLowWaveStep j)

theorem bounded_left_low_eq_family (n : ℕ) (J : Finset RightLowWaveIndex)
    (selection : ℕ → RightLowWaveIndex → Prop) (gate : ℕ → ℕ → ℕ → Prop)
    (selected : ∀ j, j ∈ J ↔ j ∈ rightLowWaveItems n ∧ selection n j)
    (cap : ∀ u v, gate n u v → u ≤ extendedWideStepCap n) :
    boundedOuterLeftBaseFrom gate n J
      rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight =
    rightLowResidueFamily (fun n i j => selection n j ∧ gate n (leftBilinearStep i) (rightLowWaveStep j)) n := by
  have selectedSet : J = (rightLowWaveItems n).filter (selection n) := by
    ext j
    simpa only [mem_filter] using selected j
  rw [selectedSet]
  let X := expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep
  have Ieq : thinHighLeftItems n = X.filter (fun i => leftBilinearStep i ≤ extendedWideStepCap n) := by
    ext i
    unfold thinHighLeftItems extendedWaveItems X expandedWaveItems
    simp only [mem_filter]
    exact ⟨fun h => ⟨⟨h.1,h.2.trans (extended_step_cap_le_expanded n)⟩,h.2⟩,fun h => ⟨h.1.1,h.2⟩⟩
  have Jeq : expandedWaveItems n ((rightLowWaveItems n).filter (selection n)) rightLowWaveStep =
      (rightLowWaveItems n).filter (selection n) := by
    apply filter_eq_self.mpr
    intro j hj
    exact ((right_low_step_le_proved_medium_cap (mem_filter.mp hj).1).trans
      (old_step_cap_le_extended n)).trans (extended_step_cap_le_expanded n)
  unfold boundedOuterLeftBaseFrom rightLowResidueFamily
  rw [Ieq,Jeq,thin_low_right_items_eq]
  simp_rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  by_cases u : leftBilinearStep i ≤ extendedWideStepCap n
  · rw [ite_eq_left u]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : selection n j <;> simp [h,rightLowResidueTerm]
  · rw [ite_eq_right u]
    refine sum_eq_zero fun j _ => ?_
    simp [show ¬gate n (leftBilinearStep i) (rightLowWaveStep j) from fun h => u (cap _ _ h)]

theorem low_short_q_product_saving : saving (rightLowResidueFamily lowShortQProductGate) := by
  have h := moderate_low_product_base_saving lowShortQPrimeItems (fun _ => filter_subset _ _) false
  intro ε he
  obtain ⟨N,hn⟩ := h ε he
  refine ⟨N,fun n nn even => ?_⟩
  have e := bounded_left_low_eq_family n (lowShortQPrimeItems n)
    (fun n j => j.1.Prime ∧ ¬j.1 ∣ n ∧ j.2 ≤ rightVaughanCut n)
    (middleLowProductGate expandedHighModulusCap shortLowModulusCap false) (fun _ => mem_filter) (fun _ _ h => h.1)
  exact (show ‖rightLowResidueFamily lowShortQProductGate n‖ ≤ _ from by
    rw [← show _ = rightLowResidueFamily lowShortQProductGate n from e]
    exact hn n nn even)

theorem low_large_q_middle_far_saving : saving (rightLowResidueFamily lowLargeQMiddleFarGate) := by
  have h := moderate_low_product_base_saving lowLargeQPrimeItems (fun _ => filter_subset _ _) true
  intro ε he
  obtain ⟨N,hn⟩ := h ε he
  refine ⟨N,fun n nn even => ?_⟩
  have e := bounded_left_low_eq_family n (lowLargeQPrimeItems n)
    (fun n j => j.1.Prime ∧ ¬j.1 ∣ n ∧ rightVaughanCut n < j.2)
    (middleLowProductGate expandedHighModulusCap shortLowModulusCap true) (fun _ => mem_filter) (fun _ _ h => h.1)
  exact (show ‖rightLowResidueFamily lowLargeQMiddleFarGate n‖ ≤ _ from by
    rw [← show _ = rightLowResidueFamily lowLargeQMiddleFarGate n from e]
    exact hn n nn even)

theorem low_wider_far_saving : saving (rightLowResidueFamily lowWiderFarGate) := by
  have h := wider_far_low_product_base_saving lowPrimeItems (fun _ => filter_subset _ _)
  intro ε he
  obtain ⟨N,hn⟩ := h ε he
  refine ⟨N,fun n nn even => ?_⟩
  have e := bounded_left_low_eq_family n (lowPrimeItems n) (fun n j => j.1.Prime ∧ ¬j.1 ∣ n)
    (middleLowProductGate shortLowModulusCap widerLowFarModulusCap true) (fun _ => mem_filter) (fun _ _ h => h.1)
  exact (show ‖rightLowResidueFamily lowWiderFarGate n‖ ≤ _ from by
    rw [← show _ = rightLowResidueFamily lowWiderFarGate n from e]
    exact hn n nn even)

theorem right_low_step_le_short_cap_of_short_factor {n : ℕ} {j : RightLowWaveIndex}
    (hj : j ∈ rightLowWaveItems n) (h : j.2 ≤ rightVaughanCut n) :
    rightLowWaveStep j ≤ shortLowModulusCap n := by
  have n0 := (mem_Icc.mp (bilateral_right_low_step_range hj)).1.trans
    (mem_Icc.mp (bilateral_right_low_step_range hj)).2
  have nr : (0 : ℝ) < n := by exact_mod_cast n0
  have q : (j.2 : ℝ) ≤ (n : ℝ)^(1/256 : ℝ) :=
    (show (j.2 : ℝ) ≤ (rightVaughanCut n : ℝ) from by exact_mod_cast h).trans (Nat.floor_le (by positivity))
  have p : j.1 ≤ rightLargeCofactorCut n :=
    (mem_Ioc.mp (mem_sigma.mp hj).1).2.trans (min_le_right _ _)
  have b : (j.1 : ℝ) ≤ (n : ℝ)^(33/64 : ℝ) :=
    (show (j.1 : ℝ) ≤ (rightLargeCofactorCut n : ℝ) from by exact_mod_cast p).trans (Nat.floor_le (by positivity))
  apply Nat.le_floor
  unfold rightLowWaveStep
  push_cast
  calc
    _ ≤ (n : ℝ)^(1/256 : ℝ)*(n : ℝ)^(33/64 : ℝ) := mul_le_mul q b (by positivity) (by positivity)
    _ = (n : ℝ)^(133/256 : ℝ) := by rw [← Real.rpow_add nr]; norm_num

end

end B13BoundedStepProductSavingProof

end

/- Low product partition -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter ArithmeticFunction DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

private theorem saving_pair_add {a b : ℕ → ℂ} (ha : saving a) (hb : saving b) :
    saving (fun n => a n + b n) := by
  intro ε he
  obtain ⟨N,hN⟩ := ha (ε/2) (by positivity)
  obtain ⟨M,hM⟩ := hb (ε/2) (by positivity)
  refine ⟨max N M,fun n hn even => ?_⟩
  exact (norm_add_le _ _).trans
    (by linarith only [hN n (by omega) even,hM n (by omega) even])

def lowPrimeProductPieces (n : ℕ) : ℂ :=
  rightLowResidueFamily lowShortQProductGate n +
    (rightLowResidueFamily lowSmallProductCutGate n +
      (rightLowResidueFamily lowLargeQNearGate n +
        (rightLowResidueFamily lowLargeQMiddleFarGate n +
          (rightLowResidueFamily lowWiderFarGate n + rightLowResidueFamily lowLargeQFarGate n))))

theorem low_prime_products_eq_pieces (n : ℕ) :
    rightLowResidueFamily lowPrimeProductsGate n = lowPrimeProductPieces n := by
  unfold lowPrimeProductPieces rightLowResidueFamily
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  let p := u*v
  have uc : u ≤ extendedWideStepCap n := (mem_filter.mp hi).2
  have hr := (mem_filter.mp hj).1
  have r := mem_Icc.mp (bilateral_right_low_step_range hr)
  have n0 : 0 < n := r.1.trans r.2
  have nr : (1 : ℝ) ≤ n := by exact_mod_cast n0
  have Mle : expandedHighModulusCap n ≤ shortLowModulusCap n := expanded_high_modulus_cap_le_short_low n0
  have Sle : shortLowModulusCap n ≤ widerLowFarModulusCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nr (by norm_num : (133/256 : ℝ) ≤ 535/1024))
  have smallLe : subcriticalMediumProductCap n ≤ 2*n :=
    (subcritical_product_cap_le_n n0).trans (by omega)
  have smallC := twice_le_high_far_strip_cap n
  by_cases base : lowPrimeProductsGate n i j
  · have baseData := base
    obtain ⟨pPrime,ndvd,modLo,pref,top⟩ := baseData
    by_cases short : j.2 ≤ rightVaughanCut n
    · have low := right_low_step_le_short_cap_of_short_factor hr short
      have wider := low.trans Sle
      simp [base,lowShortQProductGate,lowSmallProductCutGate,lowLargeQNearGate,lowLargeQMiddleFarGate,
        lowWiderFarGate,lowLargeQFarGate,middleLowProductGate,u,v,uc,pPrime,ndvd,modLo,pref,top,
        short,not_lt.mpr short,low,not_lt.mpr low,wider,not_lt.mpr wider]
    · have large : rightVaughanCut n < j.2 := lt_of_not_ge short
      by_cases small : p ≤ subcriticalMediumProductCap n
      · have near : p ≤ 2*n := small.trans smallLe
        simp [base,lowShortQProductGate,lowSmallProductCutGate,lowLargeQNearGate,lowLargeQMiddleFarGate,
          lowWiderFarGate,lowLargeQFarGate,middleLowProductGate,u,v,p,uc,pPrime,ndvd,modLo,pref,top,
          short,large,small,not_lt.mpr small,near,not_lt.mpr near]
      · have big : subcriticalMediumProductCap n < p := lt_of_not_ge small
        by_cases near : p ≤ 2*n
        · simp [base,lowShortQProductGate,lowSmallProductCutGate,lowLargeQNearGate,lowLargeQMiddleFarGate,
            lowWiderFarGate,lowLargeQFarGate,middleLowProductGate,u,v,p,uc,pPrime,ndvd,modLo,pref,top,
            short,large,small,big,near,not_lt.mpr near]
        · have far : 2*n < p := lt_of_not_ge near
          by_cases cap : v ≤ shortLowModulusCap n
          · have wider := cap.trans Sle
            simp [base,lowShortQProductGate,lowSmallProductCutGate,lowLargeQNearGate,lowLargeQMiddleFarGate,
              lowWiderFarGate,lowLargeQFarGate,middleLowProductGate,u,v,p,uc,pPrime,ndvd,modLo,pref,top,
              short,large,small,big,near,far,cap,not_lt.mpr cap,wider,not_lt.mpr wider]
          · have lo : shortLowModulusCap n < v := lt_of_not_ge cap
            by_cases wider : v ≤ widerLowFarModulusCap n
            · simp [base,lowShortQProductGate,lowSmallProductCutGate,lowLargeQNearGate,lowLargeQMiddleFarGate,
                lowWiderFarGate,lowLargeQFarGate,middleLowProductGate,u,v,p,uc,pPrime,ndvd,modLo,pref,top,
                short,large,small,big,near,far,cap,lo,wider,not_lt.mpr wider]
            · have hi : widerLowFarModulusCap n < v := lt_of_not_ge wider
              simp [base,lowShortQProductGate,lowSmallProductCutGate,lowLargeQNearGate,lowLargeQMiddleFarGate,
                lowWiderFarGate,lowLargeQFarGate,middleLowProductGate,u,v,p,uc,pPrime,ndvd,modLo,pref,top,
                short,large,small,big,near,far,cap,lo,wider,hi]
  · have off1 : ¬lowShortQProductGate n i j := by
      rintro ⟨⟨prime,ndvd,_⟩,⟨_,lo,_,pref,up,_⟩⟩
      exact base ⟨prime,ndvd,lo,pref,up⟩
    have off2 : ¬lowSmallProductCutGate n i j := fun h => base h.1
    have off3 : ¬lowLargeQNearGate n i j := by
      rintro ⟨prime,ndvd,_,lo,pref,_,up⟩
      exact base ⟨prime,ndvd,lo,pref,up.trans smallC⟩
    have off4 : ¬lowLargeQMiddleFarGate n i j := by
      rintro ⟨⟨prime,ndvd,_⟩,⟨_,lo,_,pref,up,_⟩⟩
      exact base ⟨prime,ndvd,lo,pref,up⟩
    have off5 : ¬lowWiderFarGate n i j := by
      rintro ⟨⟨prime,ndvd⟩,⟨_,lo,_,pref,up,_⟩⟩
      exact base ⟨prime,ndvd,Mle.trans_lt lo,pref,up⟩
    have off6 : ¬lowLargeQFarGate n i j := by
      rintro ⟨prime,ndvd,lo,pref,_,up⟩
      exact base ⟨prime,ndvd,(Mle.trans Sle).trans_lt lo,pref,up⟩
    simp [base,off1,off2,off3,off4,off5,off6]

theorem low_prime_products_saving : saving (rightLowResidueFamily lowPrimeProductsGate) := by
  have e : rightLowResidueFamily lowPrimeProductsGate = lowPrimeProductPieces :=
    funext low_prime_products_eq_pieces
  rw [e]
  exact saving_pair_add low_short_q_product_saving
    (saving_pair_add low_small_product_slice_saving
      (saving_pair_add low_large_q_near_saving
        (saving_pair_add low_large_q_middle_far_saving (saving_pair_add low_wider_far_saving low_large_q_far_saving))))

private theorem low_nonprime_products_eq_proper_power (n : ℕ) :
    rightLowResidueFamily (fun n i j => lowProductsGate n i j ∧ ¬j.1.Prime) n =
      extendedProperPowerResidueSliceWith lowProductsWaveGate n := by
  have rightSets : extendedProperPowerRightItems n =
      (rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n ∧ ¬j.1.Prime ∧ IsPrimePow j.1) := by
    ext j
    unfold extendedProperPowerRightItems extendedWaveItems
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨⟨base,ndvd⟩,_⟩,prime,power⟩
      exact ⟨base,ndvd,prime,power⟩
    · rintro ⟨base,ndvd,prime,power⟩
      exact ⟨⟨⟨base,ndvd⟩,(right_low_step_le_proved_medium_cap base).trans (old_step_cap_le_extended n)⟩,
        prime,power⟩
  unfold rightLowResidueFamily extendedProperPowerResidueSliceWith thinHighLeftItems
  rw [thin_low_right_items_eq,rightSets]
  simp_rw [sum_filter]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases p : j.1.Prime <;> by_cases nd : j.1 ∣ n
  all_goals try solve | simp [lowProductsGate,p,nd]
  by_cases q : IsPrimePow j.1
  · simp [lowProductsGate,p,nd,q,rightLowResidueTerm]
  · have z : vonMangoldt j.1 = 0 := vonMangoldt_eq_zero_iff.mpr q
    simp [lowProductsGate,p,nd,q,rightLowResidueTerm,rightLowWaveWeight,z]

theorem low_products_saving : saving (rightLowResidueFamily lowProductsGate) := by
  have e : rightLowResidueFamily lowProductsGate =
      fun n => rightLowResidueFamily lowPrimeProductsGate n + extendedProperPowerResidueSliceWith lowProductsWaveGate n := by
    funext n
    rw [← low_nonprime_products_eq_proper_power]
    unfold rightLowResidueFamily
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases p : j.1.Prime <;> by_cases gate : lowProductsGate n i j <;>
      simp [lowPrimeProductsGate,p,gate]
  rw [e]
  exact saving_pair_add low_prime_products_saving (extended_proper_power_residue_with_saving lowProductsWaveGate)

end

end B13BoundedStepProductSavingProof

end

/- Low product remainder -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter
open scoped Classical Finset

noncomputable section

def rawExpandedLowAboveProduct (n : ℕ) : ℂ :=
  rawWavePairSum n (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep)
    (expandedWaveItems n (outerLeftLowItems n) rightLowWaveStep) rightLowWaveStep
    (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight
    (fun u v => prefixStepGate n u v ∧ highFarStripProductCap n < u*v)
    (fun u v l r a b => (pairResidueError n u v l r a b : ℂ))

def rawExpandedAfterBoundedProducts (n : ℕ) : ℂ :=
  rawExpandedLowAboveProduct n + rawExpandedHighAboveProduct n

end

end B13BoundedStepProductSavingProof

end

/- Route bounded -/
section

namespace B13BoundedStepProductSavingProof

open Finset Filter
open scoped Classical Finset

noncomputable section

def rawExpandedBoundedProducts (n : ℕ) : ℂ :=
  rawWavePairSum n (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep)
    (expandedWaveItems n (outerLeftLowItems n) rightLowWaveStep) rightLowWaveStep
    (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight
    (fun u v => prefixStepGate n u v ∧ u*v ≤ highFarStripProductCap n)
    (fun u v l r p s => (pairResidueError n u v l r p s : ℂ)) +
  rawWavePairSum n (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep)
    (outerRightHighItems n) rightHighWaveStep (rightHighWaveLower n)
    (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)
    (fun u v => prefixStepGate n u v ∧ u*v ≤ highFarStripProductCap n)
    (fun u v l r p s => (pairResidueError n u v l r p s : ℂ))

private theorem raw_prefix_split_at_product (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) :
    rawExpandedWavePairSum n J v p s w (fun u v l r a b => (pairResidueError n u v l r a b : ℂ)) =
    rawWavePairSum n (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep)
      (expandedWaveItems n J v) v p s w
      (fun u v => prefixStepGate n u v ∧ highFarStripProductCap n < u*v)
      (fun u v l r a b => (pairResidueError n u v l r a b : ℂ)) +
    rawWavePairSum n (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep)
      (expandedWaveItems n J v) v p s w
      (fun u v => prefixStepGate n u v ∧ u*v ≤ highFarStripProductCap n)
      (fun u v l r a b => (pairResidueError n u v l r a b : ℂ)) := by
  unfold rawExpandedWavePairSum rawWavePairSum
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases pre : prefixStepGate n (leftBilinearStep i) (v j)
  · by_cases prod : leftBilinearStep i * v j ≤ highFarStripProductCap n
    · simp [pre,prod,not_lt.mpr prod]
    · simp [pre,prod,lt_of_not_ge prod]
  · simp [pre]

private theorem raw_expanded_le_product_partition (n : ℕ) :
    rawExpandedResidue n = rawExpandedAfterBoundedProducts n + rawExpandedBoundedProducts n := by
  unfold rawExpandedResidue rawExpandedAfterBoundedProducts rawExpandedBoundedProducts
    rawExpandedLowAboveProduct rawExpandedHighAboveProduct
  rw [raw_prefix_split_at_product,raw_prefix_split_at_product]
  unfold outerLeftLowItems outerRightHighItems
  abel

private theorem route_raw_expanded_high_product_split {n : ℕ} (scale : (2 : ℝ) ≤ (n : ℝ)^(1/1024 : ℝ)) :
    rawExpandedAboveSmallModulusFrom n (rightHighWaveItems n) rightHighWaveStep (rightHighWaveLower n)
      (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n) =
      rawExpandedHighAboveProduct n + largeHighProductBase n := by
  let X := expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep
  have leftSets : thinHighLeftItems n = X.filter (fun i => leftBilinearStep i ≤ extendedWideStepCap n) := by
    ext i
    unfold thinHighLeftItems extendedWaveItems X expandedWaveItems
    simp only [mem_filter]
    exact ⟨fun h => ⟨⟨h.1,h.2.trans (extended_step_cap_le_expanded n)⟩,h.2⟩,fun h => ⟨h.1.1,h.2⟩⟩
  unfold rawExpandedAboveSmallModulusFrom rawExpandedHighAboveProduct rawWavePairSum largeHighProductBase outerRightHighItems
  rw [leftSets,sum_filter,← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  dsimp only
  let u := leftBilinearStep i
  have step := mem_Icc.mp (bilateral_left_step_range (mem_filter.mp hi).1)
  have n0 : 0 < n := step.1.trans step.2
  by_cases uc : u ≤ extendedWideStepCap n
  · have H : leftBilinearStep i ≤ extendedWideStepCap n := uc
    rw [ite_eq_left H,← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    let v := rightHighWaveStep j
    by_cases pref : prefixStepGate n u v
    · by_cases product : u*v ≤ highFarStripProductCap n
      · by_cases modCap : v ≤ expandedHighModulusCap n
        · simp [u,v,pref,product,modCap,not_lt.mpr product,not_lt.mpr modCap,smallModulusProductBand,largeHighProductBaseGate]
        · simp [u,v,pref,product,modCap,not_lt.mpr product,lt_of_not_ge modCap,smallModulusProductBand,
            largeHighProductBaseGate,highResidueTerm]
      · simp [u,v,pref,product,lt_of_not_ge product,smallModulusProductBand,largeHighProductBaseGate]
    · simp [u,v,pref,largeHighProductBaseGate]
  · have H : ¬leftBilinearStep i ≤ extendedWideStepCap n := uc
    rw [ite_eq_right H,add_zero]
    refine sum_congr rfl fun j _ => ?_
    let v := rightHighWaveStep j
    by_cases product : u*v ≤ highFarStripProductCap n
    · have mv : v ≤ expandedHighModulusCap n := by
        by_contra! lo
        exact uc (large_high_product_left_step_le_old_cap n0 scale lo product)
      simp [u,v,product,not_lt.mpr product,mv,smallModulusProductBand]
    · simp [u,v,product,lt_of_not_ge product,smallModulusProductBand]

private theorem route_raw_expanded_low_product_split {n : ℕ} (scale : (2 : ℝ) ≤ (n : ℝ)^(1/1024 : ℝ)) :
    rawExpandedAboveSmallModulusFrom n (outerLeftLowItems n) rightLowWaveStep
      (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight =
      rawExpandedLowAboveProduct n + rightLowResidueFamily lowProductsGate n := by
  have n0 : 0 < n := by
    rcases eq_or_ne n 0 with rfl | h
    · norm_num [Real.zero_rpow] at scale
    · exact Nat.pos_of_ne_zero h
  have range (u v : ℕ) (h : lowProductsWaveGate n u v) : u ≤ extendedWideStepCap n :=
    large_high_product_left_step_le_old_cap n0 scale h.1 h.2.2
  have low : boundedOuterLeftBaseFrom lowProductsWaveGate n (outerLeftLowItems n)
      rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight =
        rightLowResidueFamily lowProductsGate n :=
    bounded_left_low_eq_family n (outerLeftLowItems n) (fun n j => ¬j.1 ∣ n) lowProductsWaveGate
      (fun _ => mem_filter) range
  rw [← low]
  unfold rawExpandedAboveSmallModulusFrom rawExpandedLowAboveProduct rawWavePairSum boundedOuterLeftBaseFrom
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  let u := leftBilinearStep i
  let v := rightLowWaveStep j
  by_cases product : u*v ≤ highFarStripProductCap n
  · by_cases modCap : v ≤ expandedHighModulusCap n
    · simp [u,v,product,modCap,not_lt.mpr product,not_lt.mpr modCap,smallModulusProductBand,lowProductsWaveGate]
    · simp [u,v,product,modCap,not_lt.mpr product,lt_of_not_ge modCap,smallModulusProductBand,lowProductsWaveGate]
  · simp [u,v,product,lt_of_not_ge product,smallModulusProductBand,lowProductsWaveGate]

private theorem raw_expanded_existing_bounded_slices {n : ℕ} (scale : (2 : ℝ) ≤ (n : ℝ)^(1/1024 : ℝ)) :
    rawExpandedResidue n = rawExpandedAfterBoundedProducts n +
      (smallModulusProductSlice n + (largeHighProductBase n + rightLowResidueFamily lowProductsGate n)) := by
  rw [raw_expanded_eq_small_modulus_split]
  unfold rawExpandedAfterSmallModulus rawExpandedAfterBoundedProducts
  rw [route_raw_expanded_high_product_split scale,route_raw_expanded_low_product_split scale]
  abel

theorem raw_expanded_bounded_products_saving : saving rawExpandedBoundedProducts := by
  intro ε he
  obtain ⟨K,hK⟩ := eventually_atTop.mp eventually_large_high_product_scale
  obtain ⟨N₁,h₁⟩ := small_modulus_product_slice_saving (ε/3) (by positivity)
  obtain ⟨N₂,h₂⟩ := large_high_product_base_saving (ε/3) (by positivity)
  obtain ⟨N₃,h₃⟩ := low_products_saving (ε/3) (by positivity)
  refine ⟨max K (max N₁ (max N₂ N₃)),fun n hn even => ?_⟩
  have eq := raw_expanded_existing_bounded_slices (hK n (by omega))
  rw [raw_expanded_le_product_partition] at eq
  change ‖rawExpandedBoundedProducts n‖ ≤ ε*(n : ℝ)
  rw [add_left_cancel eq]
  calc
    _ ≤ ‖smallModulusProductSlice n‖ +
        ‖largeHighProductBase n + rightLowResidueFamily lowProductsGate n‖ := norm_add_le _ _
    _ ≤ ‖smallModulusProductSlice n‖ +
        (‖largeHighProductBase n‖ + ‖rightLowResidueFamily lowProductsGate n‖) :=
      (add_le_add) le_rfl (norm_add_le _ _)
    _ ≤ (ε/3)*(n : ℝ) + ((ε/3)*(n : ℝ) + (ε/3)*(n : ℝ)) :=
      (add_le_add) (h₁ n (by omega) even) (add_le_add (h₂ n (by omega) even) (h₃ n (by omega) even))
    _ = _ := by ring

end

end B13BoundedStepProductSavingProof

theorem Conjectures.Goldbach.B13BoundedStepProductSaving :
let Λ := ArithmeticFunction.vonMangoldt
    let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
    let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊
    let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊
    let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
    let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊
    let M := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
    let truncate : ArithmeticFunction ℝ → ℕ → ArithmeticFunction ℝ := fun f H => ⟨fun m => if m ≤ H then f m else 0, by simp⟩
    let PL := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 96 : ℝ)⌋₊
    let PR := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 256 : ℝ)⌋₊
    let K := fun n : ℕ => ⌊(n : ℝ) ^ (33 / 64 : ℝ)⌋₊
    let Lcap := fun n : ℕ => ⌊(n : ℝ) ^ (3 / 10 : ℝ)⌋₊
    let split := fun n : ℕ => ⌊(n : ℝ) ^ (7 / 12 : ℝ)⌋₊
    let stepCap := fun n : ℕ => U n * ⌊(n : ℝ) ^ (111 / 256 : ℝ)⌋₊
    let F := fun (P : ℕ) => ((M - truncate M P) * (Λ - truncate Λ P) : ArithmeticFunction ℝ)
    let u := fun i : ℕ × ℕ => i.1 * i.2
    let vl := fun j : (Σ _ : ℕ, ℕ) => j.2 * j.1
    let vh := fun j : (Σ _ : ℕ, ℕ × ℕ) => j.1 * j.2.1 * j.2.2
    let X := fun n : ℕ => (((Finset.Ioc (U n) (B₁ n) ×ˢ Finset.Icc 1 n).filter (fun i => Lcap n < u i)).filter (fun i => u i ≤ n))
    let Y := fun n : ℕ => (Finset.Ioc (U n) (min n (K n))).sigma (fun b => Finset.Icc 1 (min (U n) (n / b)))
    let Z := fun n : ℕ => ((Finset.Icc 1 (U n)).sigma (fun d => Finset.Ioc (B₂ n / d) (min (split n / d) (n / (K n + 1) / d)) ×ˢ Finset.Icc 1 n)).filter (fun j => vh j ≤ n)
    let w := fun (n : ℕ) (i : ℕ × ℕ) => ((∑ d ∈ (Nat.divisors i.1).filter (fun d => U n < d), μ d : ℝ) : ℂ) * (F (PL n) i.2 : ℂ)
    let errorPart := fun (n g h a b c d : ℕ) => (let e := g.gcd h; let A := max (a : ℤ) (((n : ℤ) - (h : ℤ)*d - 1)/(g : ℤ)); let B := min (b : ℤ) (((n : ℤ) - (h : ℤ)*((c : ℤ)+1))/(g : ℤ)); let m : ℤ := (h/e : ℕ); let z := ((n/e : ℕ) : ℤ) * Nat.gcdA (g/e) (h/e) % m; if e ∣ n then (if A ≤ B then ((((A-z)%m : ℤ) : ℝ) - (((B-z)%m : ℤ) : ℝ))/(m : ℝ) else 0) else 0)
    let expandedCap := fun n : ℕ => ⌊(n : ℝ)^(511/768 : ℝ)⌋₊
    let productCap := fun n : ℕ => 2*⌊(n : ℝ)^(4097/4096 : ℝ)⌋₊
    let inside := fun (n u v : ℕ) =>
      (stepCap n^2 < u*v ∧ u.gcd v ≤ stepCap n) ∧ u*v ≤ productCap n
    let insideLow := fun n : ℕ =>
      ∑ i ∈ (X n).filter (fun i => u i ≤ expandedCap n),
      ∑ j ∈ ((Y n).filter (fun j => ¬j.1 ∣ n)).filter (fun j => vl j ≤ expandedCap n),
        @ite ℂ (inside n (u i) (vl j)) (Classical.propDecidable _) (w n i*((-(μ j.2 : ℂ))*(Λ j.1 : ℂ))*
          (errorPart n (u i) (vl j) 0 (n/u i) 0 (min (B₃ n/j.2) (n/vl j)) : ℂ)) 0
    let insideHigh := fun n : ℕ =>
      ∑ i ∈ (X n).filter (fun i => u i ≤ expandedCap n),
      ∑ j ∈ (Z n).filter (fun j => vh j ≤ expandedCap n),
        @ite ℂ (inside n (u i) (vh j)) (Classical.propDecidable _) (w n i*((-(μ j.1 : ℂ))*(F (PR n) j.2.2 : ℂ))*
          (errorPart n (u i) (vh j) 0 (n/u i) (K n/j.2.2) (n/vh j) : ℂ)) 0
    let residual := fun n => insideLow n + insideHigh n
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖residual n‖ ≤ e * (n : ℝ) := by
  exact B13BoundedStepProductSavingProof.raw_expanded_bounded_products_saving

end
