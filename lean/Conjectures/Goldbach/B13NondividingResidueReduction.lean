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

/- L goldbach frontier type2 b1 b3 -/
section

namespace B13NondividingResidueReductionProof

section

namespace DyadicMixedB4Geometric
open Finset MeasureTheory
noncomputable section
def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
def wave (u l r : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Ioc l r, phase ((u*h:ℕ)*t)
/-- Geometric cancellation on the complex unit circle. -/
theorem norm_geometric_sum_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (N : ℕ) : ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

/-- The chord distance for a phase of period one. -/
theorem norm_exp_phase_sub_one (x : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * x / 2 = Real.pi * x := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num

/-- Geometric cancellation expressed directly in terms of the phase sine. -/
theorem norm_geometric_phase_sum_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0)
    (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / |Real.sin (Real.pi * x)| := by
  have habs : 0 < |Real.sin (Real.pi * x)| := abs_pos.2 hx
  have hne : Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) ≠ 1 := by
    intro h
    have hn := norm_exp_phase_sub_one x
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hbound := norm_geometric_sum_le_two_div
    (Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x)) hne N
  rw [norm_exp_phase_sub_one] at hbound
  convert hbound using 1
  field_simp
@[simp] theorem norm_phase' (x : ℝ) : ‖phase x‖=1 := by simp [phase, Complex.norm_exp]

theorem wave_cap (u l r : ℕ) (x : ℝ) : ‖wave u l r x‖ ≤ r := by
  unfold wave
  calc
    _ ≤ ∑ h∈Ioc l r,‖phase ((u*h:ℕ)*x)‖ := norm_sum_le _ _
    _ ≤ (r:ℝ) := by simp

theorem wave_sin (u l r : ℕ) (x : ℝ) (hs : Real.sin (Real.pi*(u*x))≠0) :
    ‖wave u l r x‖ ≤ 1/|Real.sin (Real.pi*(u*x))| := by
  let z := Complex.exp (Complex.I*((2*Real.pi*((u:ℝ)*x):ℝ):ℂ))
  have hz : ‖z‖=1 := Complex.norm_exp_I_mul_ofReal _
  have heq : wave u l r x = z^(l+1)*∑ j∈range (r-l),z^j := by
    have hs' : Ioc l r = Ico (l+1) (r+1) := by ext h; simp only [mem_Ioc,mem_Ico]; omega
    rw [wave,hs',sum_Ico_eq_sum_range,Nat.add_sub_add_right,mul_sum]
    apply sum_congr rfl
    intro j _
    rw [← pow_add]
    dsimp [z,phase]
    rw [← Complex.exp_nat_mul]
    push_cast; congr 1; ring
  rw [heq,norm_mul,norm_pow,hz,one_pow,one_mul]
  exact norm_geometric_phase_sum_le hs _
def centers (u v : ℕ) := range (u+1) ×ˢ range (v+1)
def delta (U V : ℕ) (z : ℕ×ℕ) : ℤ := (z.1:ℤ)*V-(z.2:ℤ)*U

private theorem sameMod {U V i j a b : ℕ} (hc : U.Coprime V)
    (h : delta U V (i,j)=delta U V (a,b)) : i ≡ a [MOD U] := by
  apply Nat.ModEq.cancel_right_of_coprime hc
  apply Nat.modEq_iff_dvd.mpr
  refine ⟨(b:ℤ)-j,?_⟩
  unfold delta at h;push_cast;dsimp at h;linarith

private theorem codeInj {U V : ℕ} (hU : 0<U) (hc : U.Coprime V) :
    Function.Injective (fun z : ℕ×ℕ => ((decide (0≤delta U V z), (delta U V z).natAbs),z.1/U)) := by
  rintro ⟨i,j⟩ ⟨a,b⟩ he
  have hs := congrArg (fun z: (Bool×ℕ)×ℕ => z.1.1) he
  have hm := congrArg (fun z: (Bool×ℕ)×ℕ => z.1.2) he
  have hd := congrArg (fun z: (Bool×ℕ)×ℕ => z.2) he
  change decide (0≤delta U V (i,j))=decide (0≤delta U V (a,b)) at hs
  change (delta U V (i,j)).natAbs=(delta U V (a,b)).natAbs at hm
  change i/U=a/U at hd
  have hD : delta U V (i,j)=delta U V (a,b) := by
    have hsign : 0≤delta U V (i,j) ↔ 0≤delta U V (a,b) := by simpa using hs
    omega
  have hmod := sameMod hc hD
  change i % U = a % U at hmod
  have hie : i=a := by
    have h1 := Nat.mod_add_div i U
    have h2 := Nat.mod_add_div a U
    rw [hd,hmod] at h1;omega
  subst a
  simp only [delta,sub_right_inj] at hD
  have he' : (j:ℤ)=(b:ℤ) := mul_right_cancel₀ (by exact_mod_cast hU.ne') hD
  simp [show j=b by exact_mod_cast he']

theorem latticeSum (g U V : ℕ) (hg : 0<g) (hU : 0<U) (hV : 0<V) (hc : U.Coprime V)
    (f : ℕ→ℝ) (hf : ∀a,0≤f a) :
    (∑ z ∈ centers (g*U) (g*V), f (delta U V z).natAbs) ≤
      2*((g:ℝ)+1)*∑ a ∈ range (g*U*V+1), f a := by
  let code := fun z : ℕ×ℕ => ((decide (0≤delta U V z),(delta U V z).natAbs),z.1/U)
  let T := (univ (α:=Bool) ×ˢ range (g*U*V+1)) ×ˢ range (g+1)
  calc
    _ ≤ ∑ a ∈ T,f a.1.2 := by
      apply Finset.sum_le_sum_of_injOn code (codeInj hU hc).injOn
      · intro a ha
        obtain ⟨⟨i,j⟩,hz,rfl⟩ := mem_image.mp ha
        obtain ⟨hi,hj⟩ := mem_product.mp hz
        have hi' : i≤g*U := Nat.le_of_lt_succ (mem_range.mp hi)
        have hj' : j≤g*V := Nat.le_of_lt_succ (mem_range.mp hj)
        have h1 : (i:ℤ)*V≤(g:ℤ)*U*V := by exact_mod_cast Nat.mul_le_mul_right V hi'
        have h2 : (j:ℤ)*U≤(g:ℤ)*U*V := by
          simpa [mul_comm,mul_assoc,mul_left_comm] using (show (j:ℤ)*U≤(g:ℤ)*V*U by exact_mod_cast Nat.mul_le_mul_right U hj')
        have hf1 : 0≤(i:ℤ)*V := by positivity
        have hf2 : 0≤(j:ℤ)*U := by positivity
        have hL : (delta U V (i,j)).natAbs≤g*U*V := by
          unfold delta;dsimp;zify;push_cast;apply abs_le.mpr;constructor <;> omega
        have hG : i/U≤g := (Nat.div_le_div_right hi').trans_eq (Nat.mul_div_cancel _ hU)
        exact mem_product.mpr ⟨mem_product.mpr ⟨mem_univ _,mem_range.mpr (Nat.lt_succ_of_le hL)⟩,mem_range.mpr (Nat.lt_succ_of_le hG)⟩
      · intro _ _;exact le_rfl
      · intro a _ _;exact hf _
    _ = _ := by
      simp [T,sum_product,sum_mul,mul_sum,mul_comm,mul_left_comm,mul_assoc]

theorem commonCenter (u v i j : ℕ) (hu : 0<u) (hv : 0<v) (hi : i≤u)
    (h : (i:ℝ)/u=(j:ℝ)/v) : ∃ k≤u.gcd v, (i:ℝ)/u=(k:ℝ)/(u.gcd v) := by
  let g := u.gcd v
  let U := u/g
  let V := v/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left v hu
  have hgu : g*U=u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hgv : g*V=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have hU : 0<U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) hg
  have hc : U.Coprime V := Nat.coprime_div_gcd_div_gcd hg
  have h' := (div_eq_div_iff (by exact_mod_cast hu.ne') (by exact_mod_cast hv.ne')).mp h
  have hnat : i*v=j*u := by exact_mod_cast h'
  rw [←hgu,←hgv] at hnat
  have hev : i*V=j*U := Nat.eq_of_mul_eq_mul_left hg (by simpa [mul_comm,mul_assoc,mul_left_comm] using hnat)
  have hdiv : U ∣ i := hc.dvd_of_dvd_mul_right (hev ▸ dvd_mul_left _ _)
  obtain ⟨k,hk⟩ := hdiv
  have hle : U*k ≤ U*g := by rw [←hk,Nat.mul_comm U g,hgu]; exact hi
  have hkg : k≤g := Nat.le_of_mul_le_mul_left hle hU
  refine ⟨k,hkg,?_⟩
  change (i:ℝ)/u=(k:ℝ)/g
  rw [←hgu,hk];push_cast;field_simp
def sep (u v : ℕ) (z : ℕ×ℕ) : ℝ := |(z.1:ℝ)/u-(z.2:ℝ)/v|

private theorem sep_reduced (g U V : ℕ) (hg : 0<g) (hU : 0<U) (hV : 0<V) (z : ℕ×ℕ) :
    sep (g*U) (g*V) z=((delta U V z).natAbs:ℝ)/(g*U*V) := by
  have hdelta : ((delta U V z).natAbs:ℝ) = |(z.1:ℝ)*V-z.2*U| := by
    calc
      _ = |((delta U V z:ℤ):ℝ)| := by simp only [Nat.cast_natAbs,Int.cast_abs]
      _ = _ := by simp [delta]
  rw [hdelta,←abs_of_pos (show (0:ℝ)<g*U*V by positivity),←abs_div]
  unfold sep
  congr 1;push_cast;field_simp

private theorem inverse_sum (m : ℕ) : (∑ j ∈ range (m+1),(j:ℝ)⁻¹) ≤ 1+Real.log m := by
  have h := harmonic_le_one_add_log m
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have he : range (m+1)=insert 0 (Icc 1 m) := by ext j;simp;omega
  simpa [he] using h

theorem spacingSum (n u v : ℕ) (hu : 0<u) (hv : 0<v) (hun : u≤n) (hvn : v≤n) :
    (∑ z ∈ centers u v, (sep u v z)⁻¹) ≤ 8*((u:ℝ)*v)*(1+Real.log ((n:ℝ)+2)) := by
  let g := u.gcd v
  let U := u/g
  let V := v/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left v hu
  have hgu : g*U=u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hgv : g*V=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have hU : 0<U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) hg
  have hV : 0<V := Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right u v)) hg
  have hc : U.Coprime V := Nat.coprime_div_gcd_div_gcd hg
  have hL := latticeSum g U V hg hU hV hc (fun m => (m:ℝ)⁻¹) (fun m => by positivity)
  let N := g*U*V
  have hN : 0<N := by dsimp [N];positivity
  have hNn : N≤n*n := by
    dsimp [N];rw [hgu];exact Nat.mul_le_mul hun ((Nat.div_le_self ..).trans hvn)
  have hlog : 1+Real.log (N:ℝ) ≤ 2*(1+Real.log ((n:ℝ)+2)) := by
    have he : (N:ℝ) ≤ ((n:ℝ)+2)^2 := by
      calc _ ≤ (n:ℝ)*n := by exact_mod_cast hNn
           _ ≤ _ := by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    have h := Real.log_le_log (by exact_mod_cast hN) he
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hgr : (1:ℝ)≤g := by exact_mod_cast hg
  have hlogpos : 0≤1+Real.log ((n:ℝ)+2) := by linarith [Real.log_nonneg (show 1≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have hmul := (inverse_sum N).trans hlog
  rw [←hgu,←hgv]
  simp_rw [sep_reduced g U V hg hU hV, inv_div,div_eq_mul_inv,←Finset.mul_sum]
  push_cast
  have hcore := (hL.trans (mul_le_mul_of_nonneg_left hmul (by positivity)))
  calc
    _ ≤ ((g:ℝ)*U*V)*(2*((g:ℝ)+1)*(2*(1+Real.log ((n:ℝ)+2)))) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ ≤ _ := by
      have hx := mul_le_mul_of_nonneg_right hgr (show 0≤(g:ℝ)*U*V*(1+Real.log ((n:ℝ)+2)) by positivity)
      nlinarith only [hx]

theorem coincidentCount (u v : ℕ) (hu : 0<u) (hv : 0<v) :
    (∑ z ∈ centers u v, if sep u v z=0 then (1:ℝ) else 0) ≤ 4*(u.gcd v:ℝ) := by
  let g := u.gcd v
  let U := u/g
  let V := v/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left v hu
  have hgu : g*U=u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)
  have hgv : g*V=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)
  have hU : 0<U := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) hg
  have hV : 0<V := Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right u v)) hg
  have hc : U.Coprime V := Nat.coprime_div_gcd_div_gcd hg
  have h := latticeSum g U V hg hU hV hc (fun m => if m=0 then (1:ℝ) else 0) (fun m => by split_ifs <;> norm_num)
  change _≤4*(g:ℝ)
  conv_lhs => rw [←hgu,←hgv]
  simp_rw [sep_reduced g U V hg hU hV]
  have hgr : (1:ℝ)≤g := by exact_mod_cast hg
  simp [show (g:ℝ)*U*V≠0 by positivity] at h ⊢
  linarith

def smoothKernel (a c t : ℝ) := 1/(a+|t-c|)
theorem cont_smoothKernel {a c : ℝ} (ha : 0<a) : Continuous (smoothKernel a c) := by
  unfold smoothKernel; fun_prop (disch := intro t; positivity)
theorem nonneg_smoothKernel {a c t : ℝ} (ha : 0≤a) : 0 ≤ smoothKernel a c t := by
  unfold smoothKernel;positivity

private theorem shift_center (f : ℝ→ℝ) (hc : Continuous f) (hf : ∀t,0≤f t)
    (hev : ∀t,f (-t)=f t) (c : ℝ) (hc0 : 0≤c) (hc1 : c≤1) :
    (∫ t in (0:ℝ)..1, f (t-c)) ≤ 2 * ∫ t in (0:ℝ)..1, f t := by
  have hh := intervalIntegral.integral_comp_neg f (a:=0) (b:=1)
  simp only [hev,neg_zero] at hh
  rw [intervalIntegral.integral_comp_sub_right]
  calc
    _ ≤ ∫ t in (-1:ℝ)..1, f t := by
      apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall hf) (hc.intervalIntegrable _ _)
    _ = _ := by
      rw [←intervalIntegral.integral_add_adjacent_intervals (b:=0) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),←hh]
      ring

theorem integral_smoothKernel {a c : ℝ} (ha : 0<a) (hc0 : 0≤c) (hc1 : c≤1) :
    (∫ t in (0:ℝ)..1,smoothKernel a c t) ≤ 2*Real.log ((1+a)/a) := by
  let f := fun x:ℝ => 1/(a+|x|)
  have hcont : Continuous f := by dsimp [f];fun_prop (disch := intro t; positivity)
  have h := shift_center f hcont (fun t => by dsimp [f];positivity) (fun t => by simp [f]) c hc0 hc1
  have hid : (∫ t in (0:ℝ)..1,f t) = Real.log ((1+a)/a) := by
    calc
      _ = ∫ t in (0:ℝ)..1, 1/(t+a) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num)] at ht
        simp [f,abs_of_nonneg ht.1,add_comm]
      _ = ∫ t in a..1+a, 1/t := by simpa using intervalIntegral.integral_comp_add_right (fun x:ℝ=>1/x) a (a:=0) (b:=1)
      _ = _ := integral_one_div_of_pos ha (by positivity)
  rwa [hid] at h

theorem integral_smoothKernel_sq {a c : ℝ} (ha : 0<a) (hc0 : 0≤c) (hc1 : c≤1) :
    (∫ t in (0:ℝ)..1,(smoothKernel a c t)^2) ≤ 2/a := by
  let f := fun x:ℝ => (1/(a+|x|))^2
  have hcont : Continuous f := by dsimp [f];fun_prop (disch := intro t; positivity)
  have h := shift_center f hcont (fun t => sq_nonneg _) (fun t => by simp [f]) c hc0 hc1
  have he : (∫ t in (0:ℝ)..1,f t) ≤ 1/a := by
    calc
      _ = ∫ t in (0:ℝ)..1, (t+a)^(-2:ℤ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num)] at ht
        simp [f,abs_of_nonneg ht.1,add_comm,one_div,zpow_neg,pow_two]
      _ = ∫ t in a..1+a,t^(-2:ℤ) := by simpa using intervalIntegral.integral_comp_add_right (fun x:ℝ=>x^(-2:ℤ)) a (a:=0) (b:=1)
      _ ≤ _ := by
        rw [integral_zpow (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt ha (by positivity)⟩)]
        norm_num
        have hh : 0≤(1+a)⁻¹ := by positivity
        linarith
  change _≤2*(∫ t in (0:ℝ)..1, f t) at h
  exact h.trans (by rw [div_eq_mul_one_div 2 a]; linarith)

theorem distinct_kernel {a x y t : ℝ} (ha : 0<a) (hxy : x≠y) :
    smoothKernel a x t*smoothKernel a y t ≤
      (smoothKernel a x t+smoothKernel a y t)/|x-y| := by
  have hx : 0<a+|t-x| := by positivity
  have hy : 0<a+|t-y| := by positivity
  have h := abs_sub_le x t y
  rw [abs_sub_comm x t] at h
  unfold smoothKernel
  apply (le_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hxy))).mpr
  field_simp
  linarith

theorem nearestCenter (u : ℕ) (t : ℝ) (h0 : 0≤t) (h1 : t≤1) :
    ∃ i ∈ range (u+1), |(u:ℝ)*t-i|≤1/2 := by
  let i := ⌊(u:ℝ)*t+1/2⌋₊
  have hlow : (i:ℝ) ≤ (u:ℝ)*t+1/2 := Nat.floor_le (by positivity)
  have hhigh : (u:ℝ)*t+1/2 < (i:ℝ)+1 := Nat.lt_floor_add_one _
  have hle : (u:ℝ)*t≤u := by simpa using mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg u)
  have hi : (i:ℝ)<(u:ℝ)+1 := by linarith
  refine ⟨i,mem_range.mpr (by exact_mod_cast hi),abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem waveBound {n u l r i : ℕ} {t : ℝ} (hu : 0<u) (hr : r≤n/u)
    (hi : |(u:ℝ)*t-i|≤1/2) :
    ‖wave u l r t‖ ≤ (2/(u:ℝ))*smoothKernel (1/((n:ℝ)+1)) ((i:ℝ)/u) t := by
  have hur : (0:ℝ)<u := by exact_mod_cast hu
  let a : ℝ := 1/((n:ℝ)+1)
  let c : ℝ := (i:ℝ)/u
  let y : ℝ := (u:ℝ)*t-i
  have hnorm : ‖wave u l r t‖≤(n:ℝ)/u := by
    calc
      _ ≤ ∑ h ∈ Ioc l r, ‖phase ((u*h:ℕ)*t)‖ := norm_sum_le ..
      _ = ((r-l:ℕ):ℝ) := by simp [phase,Complex.norm_exp]
      _ ≤ ((n/u:ℕ):ℝ) := by exact_mod_cast (Nat.sub_le r l).trans hr
      _ ≤ _ := Nat.cast_div_le
  have h1 : ‖wave u l r t‖*a ≤ 1/(u:ℝ) := by
    dsimp [a]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    exact hnorm.trans (by rw [one_div_mul_eq_div];gcongr;linarith)
  have h2 : ‖wave u l r t‖*|t-c| ≤ 1/(u:ℝ) := by
    have hcy : |y|=(u:ℝ)*|t-c| := by
      rw [←abs_of_pos hur,←abs_mul]
      congr 1;dsimp [y,c];field_simp
    rcases eq_or_ne y 0 with hy|hy
    · have hzero : |t-c|=0 := by rw [hy,abs_zero] at hcy;exact (mul_eq_zero.mp hcy.symm).resolve_left hur.ne'
      rw [hzero,mul_zero];positivity
    have hper : |Real.sin (Real.pi*((u:ℝ)*t))|=|Real.sin (Real.pi*y)| := by
      rw [show Real.pi*((u:ℝ)*t)=Real.pi*y+(i:ℝ)*Real.pi by dsimp [y];ring,
        Real.sin_add_nat_mul_pi,abs_mul,abs_pow];simp
    have hpi : |Real.pi*y|≤Real.pi/2 := by rw [abs_mul,abs_of_pos Real.pi_pos];nlinarith [mul_le_mul_of_nonneg_left hi Real.pi_pos.le]
    have hj := Real.mul_abs_le_abs_sin hpi
    rw [abs_mul,abs_of_pos Real.pi_pos,←mul_assoc,div_mul_cancel₀ _ Real.pi_ne_zero,←hper] at hj
    have hs := (mul_pos (by norm_num : (0:ℝ)<2) (abs_pos.mpr hy)).trans_le hj
    have hw := (le_div_iff₀ hs).mp (wave_sin u l r t (abs_pos.mp hs))
    have hbound := mul_le_mul_of_nonneg_left hj (norm_nonneg (wave u l r t))
    rw [hcy] at hbound
    apply (le_div_iff₀ hur).mpr
    linarith
  have hden : 0<a+|t-c| := by dsimp [a];positivity
  change _ ≤ (2/(u:ℝ))*(1/(a+|t-c|))
  rw [mul_one_div]
  apply (le_div_iff₀ hden).mpr
  rw [mul_add,show (2:ℝ)/u=1/(u:ℝ)+1/(u:ℝ) by ring]
  exact add_le_add h1 h2
def pairEnv (a b : ℝ) (u v : ℕ) (z : ℕ×ℕ) (t : ℝ) : ℝ :=
  let x := (z.1:ℝ)/u
  let y := (z.2:ℝ)/v
  if sep u v z=0 then (16/((u:ℝ)*v))*(smoothKernel b x t)^2 else
    (4/((u:ℝ)*v))*(sep u v z)⁻¹*(smoothKernel a x t+smoothKernel a y t)

theorem pair_nonneg (a b : ℝ) (ha : 0≤a) (u v : ℕ) (z : ℕ×ℕ) (t : ℝ) :
    0≤pairEnv a b u v z t := by
  unfold pairEnv;split_ifs
  · positivity
  · exact mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr (abs_nonneg _))) (add_nonneg (nonneg_smoothKernel ha) (nonneg_smoothKernel ha))

theorem pair_cont (a b : ℝ) (ha : 0<a) (hb : 0<b) (u v : ℕ) (z : ℕ×ℕ) :
    Continuous (pairEnv a b u v z) := by
  unfold pairEnv
  split_ifs
  · exact continuous_const.mul ((cont_smoothKernel hb).pow 2)
  · exact continuous_const.mul ((cont_smoothKernel ha).add (cont_smoothKernel ha))

def gridNear (b : ℝ) (g : ℕ) : Set ℝ :=
  {t | ∃ j : ℕ, j ≤ g ∧ |t - (j : ℝ) / g| ≤ b}

theorem awayPoint (n u v l r k s : ℕ) (b : ℝ) (hb : 0 < b) (hu : 0 < u) (hv : 0 < v)
    (hr : r ≤ n / u) (hs : s ≤ n / v) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (gridNear b (u.gcd v))ᶜ.indicator (fun x => ‖wave u l r x * wave v k s x‖) t ≤
      ∑ z ∈ centers u v, pairEnv (1 / ((n : ℝ) + 1)) b u v z t := by
  classical
  let a : ℝ := 1/((n:ℝ)+1)
  have ha : 0<a := by dsimp [a]; positivity
  by_cases hm : t∈(gridNear b (u.gcd v))ᶜ
  · rw [Set.indicator_of_mem hm,norm_mul]
    obtain ⟨i,hi,hi'⟩ := nearestCenter u t ht.1 ht.2
    obtain ⟨j,hj,hj'⟩ := nearestCenter v t ht.1 ht.2
    let x := (i:ℝ)/u
    let y := (j:ℝ)/v
    have hby := mul_le_mul (waveBound (l:=l) hu hr hi') (waveBound (l:=k) hv hs hj') (norm_nonneg _) (mul_nonneg (by positivity) (nonneg_smoothKernel ha.le))
    change _≤(2/(u:ℝ)*smoothKernel a x t)*(2/(v:ℝ)*smoothKernel a y t) at hby
    have hpre : ‖wave u l r t‖*‖wave v k s t‖≤4/((u:ℝ)*v)*(smoothKernel a x t*smoothKernel a y t) := by
      refine hby.trans_eq ?_;ring
    refine le_trans ?_ (single_le_sum (f:=fun z=>pairEnv a b u v z t) (fun z _=>pair_nonneg a b ha.le u v z t) (show (i,j)∈centers u v from mem_product.mpr ⟨hi,hj⟩))
    change _≤pairEnv a b u v (i,j) t
    unfold pairEnv
    by_cases he : x=y
    · have hsep : sep u v (i,j)=0 := by change |x-y|=0;rw [he];simp
      rw [if_pos hsep]
      obtain ⟨h,hh,heh⟩ := commonCenter u v i j hu hv (Nat.le_of_lt_succ (mem_range.mp hi)) he
      have hdist : b < |t-x| := by
        by_contra! hsmall
        apply hm;exact ⟨h,hh,by change |t-(h:ℝ)/(u.gcd v:ℝ)|≤b;rw [←heh];exact hsmall⟩
      have hk : smoothKernel a x t≤2*smoothKernel b x t := by
        unfold smoothKernel
        have hp : 0<a+|t-x| := by positivity
        have hp' : 0<b+|t-x| := by positivity
        rw [mul_one_div]
        apply (div_le_div_iff₀ hp hp').mpr
        linarith
      rw [←he] at hpre
      calc
        _ ≤ _ := hpre
        _ ≤ 4/((u:ℝ)*v)*((2*smoothKernel b x t)*(2*smoothKernel b x t)) :=
          mul_le_mul_of_nonneg_left (mul_self_le_mul_self (nonneg_smoothKernel ha.le) hk) (by positivity)
        _ = _ := by dsimp [x];ring
    · have hsep : sep u v (i,j)≠0 := abs_ne_zero.mpr (sub_ne_zero.mpr he)
      rw [if_neg hsep]
      exact hpre.trans ((mul_le_mul_of_nonneg_left (distinct_kernel ha he) (by positivity : 0≤4/((u:ℝ)*v))).trans_eq (by change _=4/((u:ℝ)*v)*|x-y|⁻¹*_;ring))
  · rw [Set.indicator_of_notMem hm]
    exact sum_nonneg (fun z _=>pair_nonneg a b ha.le u v z t)

theorem gridNear_measurable (b : ℝ) (g : ℕ) : MeasurableSet (gridNear b g) := by
  unfold gridNear
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  by_cases h : j≤g
  · simp only [h,true_and]
    exact measurableSet_le (f:= fun t:ℝ => |t-(j:ℝ)/g|) (g:=fun _=>b) (by fun_prop) measurable_const
  · simp [h]

private theorem pair_integral (n : ℕ) (b : ℝ) (hb : 0<b) (u v : ℕ) (hu : 0<u) (hv : 0<v)
    (z : ℕ×ℕ) (hz : z∈centers u v) :
    (∫ t in (0:ℝ)..1,pairEnv (1/((n:ℝ)+1)) b u v z t) ≤
    (32/((u:ℝ)*v*b))*(if sep u v z=0 then 1 else 0)+
      (16*Real.log ((n:ℝ)+2)/((u:ℝ)*v))*(sep u v z)⁻¹ := by
  let a : ℝ := 1/((n:ℝ)+1)
  have ha : 0<a := by dsimp [a]; positivity
  let x := (z.1:ℝ)/u
  let y := (z.2:ℝ)/v
  obtain ⟨hi,hj⟩ := mem_product.mp hz
  have hcX : x≤1 := (div_le_one (by exact_mod_cast hu)).mpr (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hi))
  have hcY : y≤1 := (div_le_one (by exact_mod_cast hv)).mpr (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hj))
  have hlog : (1+a)/a=(n:ℝ)+2 := by dsimp [a];field_simp;ring
  by_cases h : sep u v z=0
  · simp only [pairEnv,h,ite_true,inv_zero,mul_zero,add_zero,mul_one]
    rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ (16/((u:ℝ)*v))*(2/b) := mul_le_mul_of_nonneg_left (integral_smoothKernel_sq hb (by dsimp [x];positivity) hcX) (by positivity)
      _ = _ := by ring
  · simp only [pairEnv,h,ite_false,mul_zero,zero_add]
    have hi := integral_smoothKernel ha (by dsimp [x];positivity) hcX
    have hj := integral_smoothKernel ha (by dsimp [y];positivity) hcY
    rw [hlog] at hi hj
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add ((cont_smoothKernel ha).intervalIntegrable _ _)
      ((cont_smoothKernel ha).intervalIntegrable _ _)]
    calc
      _ ≤ (4/((u:ℝ)*v))*(sep u v z)⁻¹*(4*Real.log ((n:ℝ)+2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by positivity) (inv_nonneg.mpr (abs_nonneg _)))
      _ = _ := by ring

theorem awayBound (n u v l r k s : ℕ) (b : ℝ) (hb : 0 < b)
    (hu : 0 < u) (hv : 0 < v) (hun : u ≤ n) (hvn : v ≤ n)
    (hr : r ≤ n / u) (hs : s ≤ n / v) :
    (∫ t in (0 : ℝ)..1, (gridNear b (u.gcd v))ᶜ.indicator
      (fun x => ‖wave u l r x * wave v k s x‖) t) ≤
      128 * ((1 + Real.log ((n : ℝ) + 2)) ^ 2 + (u.gcd v : ℝ) / ((u : ℝ) * v * b)) := by
  let a : ℝ := 1 / ((n : ℝ) + 1)
  let W : ℝ := Real.log ((n : ℝ) + 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hw : 0 ≤ W := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have integrable : IntervalIntegrable ((gridNear b (u.gcd v))ᶜ.indicator
      (fun x => ‖wave u l r x * wave v k s x‖)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have continuous : Continuous (fun x => ‖wave u l r x * wave v k s x‖) := by
      unfold wave phase
      fun_prop
    exact (continuous.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
      (gridNear_measurable b (u.gcd v)).compl
  have pairIntegrable (z : ℕ × ℕ) :=
    (pair_cont a b ha hb u v z).intervalIntegrable (μ := volume) 0 1
  have bound := intervalIntegral.integral_mono_on zero_le_one integrable
    (IntervalIntegrable.sum (centers u v) (fun z _ => pairIntegrable z))
    (fun t ht => by simpa only [Finset.sum_apply] using awayPoint n u v l r k s b hb hu hv hr hs t ht)
  simp only [Finset.sum_apply] at bound
  rw [intervalIntegral.integral_finsetSum (fun z _ => pairIntegrable z)] at bound
  have pairBound := bound.trans (sum_le_sum (s := centers u v)
    (fun z hz => pair_integral n b hb u v hu hv z hz))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at pairBound
  have equalBound := mul_le_mul_of_nonneg_left (coincidentCount u v hu hv)
    (show 0 ≤ 32 / ((u : ℝ) * v * b) by positivity)
  have distinctBound := mul_le_mul_of_nonneg_left (spacingSum n u v hu hv hun hvn)
    (show 0 ≤ 16 * W / ((u : ℝ) * v) by positivity)
  rw [show (32 / ((u : ℝ) * v * b)) * (4 * (u.gcd v : ℝ)) =
      128 * ((u.gcd v : ℝ) / ((u : ℝ) * v * b)) by ring] at equalBound
  change _ ≤ (16 * W / ((u : ℝ) * v)) * (8 * ((u : ℝ) * v) * (1 + W)) at distinctBound
  rw [show (16 * W / ((u : ℝ) * v)) * (8 * ((u : ℝ) * v) * (1 + W)) =
      128 * W * (1 + W) by field_simp; ring] at distinctBound
  change _ ≤ 128 * ((1 + W) ^ 2 + (u.gcd v : ℝ) / ((u : ℝ) * v * b))
  have logBound : 128 * W * (1 + W) ≤ 128 * (1 + W) ^ 2 := by nlinarith only [hw]
  exact pairBound.trans (by linarith only [equalBound, distinctBound, logBound])

theorem gridNear_subset_of_dvd {g u : ℕ} (b : ℝ) (hg : 0 < g) (hu : 0 < u) (dvd : g ∣ u) :
    gridNear b g ⊆ gridNear b u := by
  intro t member
  obtain ⟨j, jBound, distance⟩ := member
  obtain ⟨k, rfl⟩ := dvd
  have hk : 0 < k := Nat.pos_of_mul_pos_left hu
  refine ⟨j * k, Nat.mul_le_mul_right k jBound, ?_⟩
  have same : ((j * k : ℕ) : ℝ) / ((g * k : ℕ) : ℝ) = (j : ℝ) / g := by
    push_cast
    field_simp
  simpa only [same] using distance

def offWave (b : ℝ) (u l r : ℕ) : ℝ → ℂ := (gridNear b u)ᶜ.indicator (wave u l r)

theorem norm_offWave_mul_le (b : ℝ) {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (l r k s : ℕ) (t : ℝ) :
    ‖offWave b u l r t * offWave b v k s t‖ ≤
      (gridNear b (u.gcd v))ᶜ.indicator (fun x => ‖wave u l r x * wave v k s x‖) t := by
  have rhsNonnegative := Set.indicator_nonneg (s := (gridNear b (u.gcd v))ᶜ)
    (f := fun x => ‖wave u l r x * wave v k s x‖) (fun _ _ => norm_nonneg _) t
  by_cases nearU : t ∈ gridNear b u
  · simpa [offWave, nearU] using rhsNonnegative
  by_cases nearV : t ∈ gridNear b v
  · simpa [offWave, nearV] using rhsNonnegative
  have nearNotGcd : t ∉ gridNear b (u.gcd v) := fun member =>
    nearU (gridNear_subset_of_dvd b (Nat.gcd_pos_of_pos_left v hu) hu (Nat.gcd_dvd_left u v) member)
  simp [offWave, nearU, nearV, nearNotGcd]

end
end DyadicMixedB4Geometric

end

section

namespace DyadicMixedB4ArcGeometry
open Finset MeasureTheory DyadicMixedB4Geometric
noncomputable section

def numSet (q : ℕ) := (range (q+1)).filter (fun a => a.Coprime q)

private theorem centerSep {a b q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (h : a*r ≠ b*q) : 1/((q:ℝ)*r) ≤ |(a:ℝ)/q-b/r| := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  rw [show (a:ℝ)/q-b/r = (a*r-b*q)/(q*r) by field_simp, abs_div,
    abs_of_pos (mul_pos hq' hr')]
  apply (div_le_div_iff_of_pos_right (mul_pos hq' hr')).mpr
  rcases lt_or_gt_of_ne h with hab | hba
  · have hgap : (a:ℝ)*r+1 ≤ b*q := by exact_mod_cast Nat.succ_le_of_lt hab
    linarith [neg_le_abs ((a:ℝ)*r-b*q)]
  · have hgap : (b:ℝ)*q+1 ≤ a*r := by exact_mod_cast Nat.succ_le_of_lt hba
    linarith [le_abs_self ((a:ℝ)*r-b*q)]

private theorem centerEq {a b q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (ha : a.Coprime q) (hb : b.Coprime r) (he : a*r=b*q) : q=r ∧ a=b := by
  have h₁ : q ∣ a*r := he ▸ Nat.dvd_mul_left q b
  have h₂ : r ∣ b*q := he.symm ▸ Nat.dvd_mul_left r a
  have eq := Nat.dvd_antisymm (ha.symm.dvd_of_dvd_mul_left h₁) (hb.symm.dvd_of_dvd_mul_left h₂)
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq he⟩

private theorem centerOfGrid (j g : ℕ) (hg : 0<g) (hj : j≤g) :
    ∃ q ∈ g.divisors, ∃ a ∈ numSet q, (j:ℝ)/g=(a:ℝ)/q := by
  let z := j.gcd g
  have hz : 0 < z := Nat.gcd_pos_of_pos_right j hg
  have hd : z ∣ g := Nat.gcd_dvd_right j g
  have hjd : z ∣ j := Nat.gcd_dvd_left j g
  have hq : 0 < g/z := Nat.div_pos (Nat.le_of_dvd hg hd) hz
  refine ⟨g/z,Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd,hg.ne'⟩,j/z,?_,?_⟩
  · exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hj)),
      Nat.coprime_div_gcd_div_gcd hz⟩
  · apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    exact_mod_cast (show j*(g/z)=(j/z)*g from calc
      j*(g/z) = ((j/z)*z)*(g/z) := by rw [Nat.div_mul_cancel hjd]
      _ = (j/z)*((g/z)*z) := by ring
      _ = (j/z)*g := by rw [Nat.div_mul_cancel hd])

private theorem gridOfCenter {g q a : ℕ} (hq : q ∈ g.divisors) (ha : a ∈ numSet q) :
    ∃ j ≤ g, (j:ℝ)/g=(a:ℝ)/q := by
  obtain ⟨hd,hg⟩ := Nat.mem_divisors.mp hq
  have hqp := Nat.pos_of_mem_divisors hq
  have hap : a ≤ q := by have := mem_range.mp (mem_filter.mp ha).1; omega
  refine ⟨a*(g/q), ?_, ?_⟩
  · calc _ ≤ q*(g/q) := Nat.mul_le_mul_right _ hap
         _ = g := Nat.mul_div_cancel' hd
  · apply (div_eq_div_iff (by exact_mod_cast hg) (by exact_mod_cast hqp.ne')).mpr
    exact_mod_cast (show a*(g/q)*q=a*g by rw [mul_assoc,Nat.div_mul_cancel hd])

def radius (M : ℕ) : ℝ := 1 / (8 * (M : ℝ) ^ 2)

def wide (n B H : ℕ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q ∧
    |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)}

def window (n M B H q : ℕ) : Set ℝ :=
  {x | |x| ≤ radius M ∧ (B < q ∨ (H : ℝ) / ((q : ℝ) * n) < |x|)}

def cell (n M B H q a : ℕ) : Set ℝ :=
  {t | t - (a : ℝ) / q ∈ window n M B H q}

theorem radius_le_product {M q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (qBound : q ≤ M) (rBound : r ≤ M) : radius M ≤ 1 / (4 * (q : ℝ) * r) := by
  have productBound : (q : ℝ) * r ≤ (M : ℝ) ^ 2 := by
    norm_cast
    rw [pow_two]
    exact Nat.mul_le_mul qBound rBound
  unfold radius
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith only [productBound, show 0 ≤ (M : ℝ) ^ 2 by positivity]

private theorem centers_eq_of_close {a b q r : ℕ} {t : ℝ} (hq : 0 < q) (hr : 0 < r)
    (nearA : |t - (a : ℝ) / q| ≤ 1 / (4 * (q : ℝ) * r))
    (nearB : |t - (b : ℝ) / r| ≤ 1 / (4 * (q : ℝ) * r)) : a * r = b * q := by
  by_contra different
  have separated := centerSep hq hr different
  have triangle := abs_sub_le ((a : ℝ) / q) t ((b : ℝ) / r)
  rw [abs_sub_comm ((a : ℝ) / q) t] at triangle
  have quotient : 1 / ((q : ℝ) * r) = 4 * (1 / (4 * (q : ℝ) * r)) := by ring
  rw [quotient] at separated
  linarith only [nearA, nearB, triangle, separated,
    show 0 < 1 / (4 * (q : ℝ) * r) by positivity]

theorem wide_at_cell_center {a q n M g B H : ℕ} {t : ℝ} (hn : 0 < n) (hg : 0 < g)
    (gBound : g ≤ M) (Bbound : B ≤ M) (smallWidth : 4 * H * M ≤ n)
    (qMember : q ∈ g.divisors) (aMember : a ∈ numSet q)
    (nearCenter : |t - (a : ℝ) / q| ≤ radius M) :
    t ∈ wide n B H ↔ q ≤ B ∧ |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n) := by
  have hq := Nat.pos_of_mem_divisors qMember
  have qBound : q ≤ M := (Nat.le_of_dvd hg (Nat.mem_divisors.mp qMember).1).trans gBound
  obtain ⟨aRange, aCoprime⟩ := mem_filter.mp aMember
  constructor
  · rintro ⟨r, b, hr, rBound, _, bCoprime, nearB⟩
    have hWidth : (H : ℝ) / ((r : ℝ) * n) ≤ 1 / (4 * (q : ℝ) * r) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have qWidth : (4 : ℝ) * H * q ≤ n := by
        exact_mod_cast (Nat.mul_le_mul_left (4 * H) qBound).trans smallWidth
      nlinarith only [mul_le_mul_of_nonneg_right qWidth (Nat.cast_nonneg (α := ℝ) r)]
    obtain ⟨rfl, rfl⟩ := centerEq hq hr aCoprime bCoprime
      (centers_eq_of_close hq hr (nearCenter.trans (radius_le_product hq hr qBound (rBound.trans Bbound)))
        (nearB.trans hWidth))
    exact ⟨rBound, nearB⟩
  · rintro ⟨qLe, near⟩
    exact ⟨q, a, hq, qLe, Nat.le_of_lt_succ (mem_range.mp aRange), aCoprime, near⟩

theorem mem_deep_cell (n M g B H : ℕ) (hn : 0 < n) (hg : 0 < g) (gBound : g ≤ M)
    (Bbound : B ≤ M) (smallWidth : 4 * H * M ≤ n) (t : ℝ) :
    t ∈ gridNear (radius M) g ∩ (wide n B H)ᶜ ↔
      ∃ q ∈ g.divisors, ∃ a ∈ numSet q, t ∈ cell n M B H q a := by
  constructor
  · rintro ⟨⟨j, jBound, near⟩, deep⟩
    obtain ⟨q, qMember, a, aMember, center⟩ := centerOfGrid j g hg jBound
    rw [center] at near
    refine ⟨q, qMember, a, aMember, near, ?_⟩
    have outside := (wide_at_cell_center hn hg gBound Bbound smallWidth qMember aMember near).not.mp deep
    simpa only [not_and_or, not_le] using outside
  · rintro ⟨q, qMember, a, aMember, near, deep⟩
    obtain ⟨j, jBound, center⟩ := gridOfCenter qMember aMember
    refine ⟨⟨j, jBound, center.symm ▸ near⟩, ?_⟩
    apply (wide_at_cell_center hn hg gBound Bbound smallWidth qMember aMember near).not.mpr
    simpa only [not_and_or, not_le] using deep

private theorem unique_deep_cell {n M g B H q r a b : ℕ} {t : ℝ} (hg : 0 < g) (gBound : g ≤ M)
    (qMember : q ∈ g.divisors) (rMember : r ∈ g.divisors)
    (aMember : a ∈ numSet q) (bMember : b ∈ numSet r)
    (htq : t ∈ cell n M B H q a) (htr : t ∈ cell n M B H r b) : q = r ∧ a = b := by
  have hq := Nat.pos_of_mem_divisors qMember
  have hr := Nat.pos_of_mem_divisors rMember
  have cap := radius_le_product hq hr
    ((Nat.le_of_dvd hg (Nat.mem_divisors.mp qMember).1).trans gBound)
    ((Nat.le_of_dvd hg (Nat.mem_divisors.mp rMember).1).trans gBound)
  exact centerEq hq hr (mem_filter.mp aMember).2 (mem_filter.mp bMember).2
    (centers_eq_of_close hq hr (htq.1.trans cap) (htr.1.trans cap))

theorem deep_cell_indicator (f : ℝ → ℂ) (n M g B H : ℕ) (hn : 0 < n) (hg : 0 < g)
    (gBound : g ≤ M) (Bbound : B ≤ M) (smallWidth : 4 * H * M ≤ n) (t : ℝ) :
    (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator f t =
    ∑ q ∈ g.divisors, ∑ a ∈ numSet q, (cell n M B H q a).indicator f t := by
  classical
  have description := mem_deep_cell n M g B H hn hg gBound Bbound smallWidth t
  by_cases membership : t ∈ gridNear (radius M) g ∩ (wide n B H)ᶜ
  · obtain ⟨q, qMember, a, aMember, cellMember⟩ := description.mp membership
    rw [Set.indicator_of_mem membership, sum_eq_single_of_mem q qMember]
    · rw [sum_eq_single_of_mem a aMember, Set.indicator_of_mem cellMember]
      intro b bMember different
      exact Set.indicator_of_notMem (fun h => different
        (unique_deep_cell hg gBound qMember qMember bMember aMember h cellMember).2) _
    · intro r rMember different
      apply sum_eq_zero
      intro b bMember
      exact Set.indicator_of_notMem (fun h => different
        (unique_deep_cell hg gBound rMember qMember bMember aMember h cellMember).1) _
  · rw [Set.indicator_of_notMem membership]
    symm
    apply sum_eq_zero
    intro q qMember
    apply sum_eq_zero
    intro a aMember
    exact Set.indicator_of_notMem (fun h => membership (description.mpr ⟨q, qMember, a, aMember, h⟩)) _

theorem window_empty_of_small_modulus {n M B H q R : ℕ} (hn : 0 < n) (hq : 0 < q)
    (qBound : q ≤ R) (RBound : R ≤ B) (cover : (R : ℝ) * n * radius M ≤ H) :
    window n M B H q = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have qCover : (q : ℝ) * n * radius M ≤ H := by
    refine le_trans ?_ cover
    gcongr
    unfold radius
    positivity
  have radiusBound : radius M ≤ (H : ℝ) / ((q : ℝ) * n) := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm (radius M)] using qCover
  exact ht.2.elim (fun h => (not_lt_of_ge (qBound.trans RBound)) h)
    (fun h => (not_lt_of_ge (ht.1.trans radiusBound)) h)

end
end DyadicMixedB4ArcGeometry

end

section

open Finset MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcGeometry

namespace DyadicMixedB4ArcCenters

noncomputable section

theorem window_measurable (n M B H q : ℕ) : MeasurableSet (window n M B H q) := by
  have radiusMeasurable : MeasurableSet {x : ℝ | |x| ≤ radius M} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have widthMeasurable : MeasurableSet {x : ℝ | (H : ℝ) / ((q : ℝ) * n) < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  by_cases h : B < q
  · simpa [window, h] using radiusMeasurable
  · have eq : window n M B H q =
        {x : ℝ | |x| ≤ radius M} ∩ {x : ℝ | (H : ℝ) / ((q : ℝ) * n) < |x|} := by
        ext t
        simp [window, h]
    rw [eq]
    exact radiusMeasurable.inter widthMeasurable

theorem cell_measurable (n M B H q a : ℕ) : MeasurableSet (cell n M B H q a) :=
  (window_measurable n M B H q).preimage (measurable_id.sub measurable_const)

theorem cell_within_unit_interval {n M B H q a : ℕ} (qLower : 1 < q) (qBound : q ≤ M)
    (aMember : a ∈ numSet q) : cell n M B H q a ⊆ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨aRange, aCoprime⟩ := mem_filter.mp aMember
  have qPositive : 0 < q := by omega
  have qRealPositive : (0 : ℝ) < q := by exact_mod_cast qPositive
  have aPositive : 0 < a := by
    by_contra! zero
    have aZero : a = 0 := by omega
    subst a
    exact (by omega : q ≠ 1) (q.coprime_zero_left.mp aCoprime)
  have aLt : a < q := by
    have aLe := Nat.le_of_lt_succ (mem_range.mp aRange)
    apply lt_of_le_of_ne aLe
    intro equal
    subst a
    have impossible : q.gcd q = 1 := aCoprime
    rw [Nat.gcd_self] at impossible
    omega
  have left : 1 / (q : ℝ) ≤ (a : ℝ) / q := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast aPositive) qRealPositive.le
  have right : (a : ℝ) / q ≤ 1 - 1 / (q : ℝ) := by
    rw [show (1 : ℝ) - 1 / (q : ℝ) = ((q : ℝ) - 1) / q by field_simp]
    have space : (a : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt aLt
    exact div_le_div_of_nonneg_right (by linarith only [space]) qRealPositive.le
  have cap : radius M ≤ 1 / (q : ℝ) := (radius_le_product qPositive (r := 1) (by decide) qBound (by omega)).trans
    (one_div_le_one_div_of_le qRealPositive (by push_cast; nlinarith only [qRealPositive]))
  intro t member
  have distance := abs_le.mp member.1
  exact ⟨by linarith only [distance.1, cap, left], by linarith only [distance.2, cap, right]⟩

private theorem integral_indicator_closed {f : ℝ → ℂ} {s : Set ℝ} {a b : ℝ}
    (ordered : a ≤ b) (measurable : MeasurableSet s) (contained : s ⊆ Set.Icc a b) :
    (∫ t in a..b, s.indicator f t) = ∫ t in s, f t := by
  rw [intervalIntegral.integral_of_le ordered, ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator measurable, Set.inter_eq_right.mpr contained]

theorem integral_cell_translate {f : ℝ → ℂ} {n M B H q a : ℕ}
    (qLower : 1 < q) (qBound : q ≤ M) (aMember : a ∈ numSet q) :
    (∫ t in (0 : ℝ)..1, (cell n M B H q a).indicator f t) =
      ∫ t in window n M B H q, f (t + (a : ℝ) / q) := by
  let s := cell n M B H q a
  let w := window n M B H q
  let centre := (a : ℝ) / q
  let d := radius M
  have dNonnegative : 0 ≤ d := by dsimp [d, radius]; positivity
  have measurableS : MeasurableSet s := cell_measurable n M B H q a
  have measurableW : MeasurableSet w := window_measurable n M B H q
  have containedS : s ⊆ Set.Icc (-d + centre) (d + centre) := by
    intro t ht
    have distance := abs_le.mp ht.1
    change -d ≤ t - centre ∧ t - centre ≤ d at distance
    exact ⟨by linarith only [distance.1], by linarith only [distance.2]⟩
  have containedW : w ⊆ Set.Icc (-d) d := fun t ht => abs_le.mp ht.1
  have translateIndicator (t : ℝ) : s.indicator f (t + centre) =
      w.indicator (fun x => f (x + centre)) t := by
    have memIff : t + centre ∈ s ↔ t ∈ w := by
      change t + centre - centre ∈ w ↔ _
      rw [add_sub_cancel_right]
    by_cases membership : t ∈ w
    · rw [Set.indicator_of_mem (memIff.mpr membership), Set.indicator_of_mem membership]
    · rw [Set.indicator_of_notMem (fun other => membership (memIff.mp other)), Set.indicator_of_notMem membership]
  calc
    _ = ∫ t in s, f t := integral_indicator_closed zero_le_one measurableS
      (cell_within_unit_interval qLower qBound aMember)
    _ = ∫ t in -d + centre..d + centre, s.indicator f t :=
      (integral_indicator_closed (by linarith only [dNonnegative]) measurableS containedS).symm
    _ = ∫ t in -d..d, s.indicator f (t + centre) := (intervalIntegral.integral_comp_add_right _ centre).symm
    _ = ∫ t in -d..d, w.indicator (fun x => f (x + centre)) t :=
      intervalIntegral.integral_congr fun t _ => translateIndicator t
    _ = _ := integral_indicator_closed (by linarith only [dNonnegative]) measurableW containedW

theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  have argument : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [argument]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (k : ℤ)

theorem wave_at_cell_center {q g : ℕ} (qPositive : 0 < q) (divides : q ∣ g)
    (l r a : ℕ) (t : ℝ) : wave g l r (t + (a : ℝ) / q) = wave g l r t := by
  unfold wave
  refine sum_congr rfl fun j _ => ?_
  obtain ⟨v, identity⟩ := divides
  have centerTerm : ((g * j : ℕ) : ℝ) * ((a : ℝ) / q) = ((v * j * a : ℕ) : ℝ) := by
    rw [identity]
    push_cast
    field_simp
  rw [mul_add, phase_add, centerTerm, phase_nat, mul_one]

theorem integral_cell_wave {n M B H q a g : ℕ} (qLower : 1 < q) (qBound : q ≤ M)
    (aMember : a ∈ numSet q) (divides : q ∣ g) (l r : ℕ) (k : ℤ) :
    (∫ t in (0 : ℝ)..1, (cell n M B H q a).indicator (fun x =>
      phase ((k : ℝ) * x) * wave g l r x) t) = phase ((k : ℝ) * ((a : ℝ) / q)) *
      ∫ t in window n M B H q, phase ((k : ℝ) * t) * wave g l r t := by
  rw [integral_cell_translate qLower qBound aMember, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  change phase ((k : ℝ) * (t + (a : ℝ) / q)) * wave g l r (t + (a : ℝ) / q) = _
  rw [wave_at_cell_center (by omega : 0 < q) divides, mul_add, phase_add]
  ring

def ramanujan (q : ℕ) (k : ℤ) : ℂ := ∑ a ∈ numSet q, phase ((k : ℝ) * ((a : ℝ) / q))

theorem centered_deep_wave_integral (n M B H R g l r : ℕ) (k : ℤ)
    (nPositive : 0 < n) (gPositive : 0 < g) (gBound : g ≤ M) (Bbound : B ≤ M)
    (width : 4 * H * M ≤ n) (Rpositive : 1 ≤ R) (Rbound : R ≤ B)
    (cover : (R : ℝ) * n * radius M ≤ H) :
    (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator
        (fun x => phase ((k : ℝ) * x) * wave g l r x) t) =
      ∑ q ∈ g.divisors.filter (fun q => R < q), ramanujan q k *
        ∫ t in window n M B H q, phase ((k : ℝ) * t) * wave g l r t := by
  classical
  let f (x : ℝ) := phase ((k : ℝ) * x) * wave g l r x
  have fContinuous : Continuous f := by unfold f wave phase; fun_prop
  have cellIntegrable (q a : ℕ) : IntervalIntegrable ((cell n M B H q a).indicator f) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (fContinuous.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
      (cell_measurable n M B H q a)
  have split : (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator f t) =
      ∑ q ∈ g.divisors, ∑ a ∈ numSet q, ∫ t in (0 : ℝ)..1, (cell n M B H q a).indicator f t := by
    calc
      _ = ∫ t in (0 : ℝ)..1, ∑ q ∈ g.divisors, ∑ a ∈ numSet q, (cell n M B H q a).indicator f t := by
        apply intervalIntegral.integral_congr
        intro t _
        exact deep_cell_indicator f n M g B H nPositive gPositive gBound Bbound width t
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum]
        · refine sum_congr rfl fun q _ => ?_
          rw [intervalIntegral.integral_finsetSum]
          exact fun a _ => cellIntegrable q a
        · intro q _
          have integrated := IntervalIntegrable.sum (numSet q) (fun a _ => cellIntegrable q a)
          convert integrated using 1
          funext t
          simp only [Finset.sum_apply]
  change (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator f t) = _
  rw [split, Finset.sum_filter]
  refine sum_congr rfl fun q qMember => ?_
  have qPositive := Nat.pos_of_mem_divisors qMember
  by_cases large : R < q
  · have qLower : 1 < q := Rpositive.trans_lt large
    have divides := (Nat.mem_divisors.mp qMember).1
    have qBound : q ≤ M := (Nat.le_of_dvd gPositive divides).trans gBound
    rw [if_pos large, ramanujan, sum_mul]
    exact sum_congr rfl fun a aMember => integral_cell_wave qLower qBound aMember divides l r k
  · rw [if_neg large]
    apply sum_eq_zero
    intro a _
    have emptyWindow := window_empty_of_small_modulus nPositive qPositive (le_of_not_gt large) Rbound cover
    have emptyCell : cell n M B H q a = ∅ := by simp [cell, emptyWindow]
    simp [emptyCell]

end
end DyadicMixedB4ArcCenters

end

section

open Finset MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcCenters

namespace DyadicMixedB4ProgressionApprox

noncomputable section

theorem continuous_phase_scale (t : ℝ) : Continuous (fun x : ℝ => phase (x * t)) := by
  unfold phase
  fun_prop

theorem norm_phase_sub_one_le (x : ℝ) : ‖phase x - 1‖ ≤ 2 * Real.pi * |x| := by
  unfold phase
  rw [mul_comm _ Complex.I, norm_exp_phase_sub_one]
  have sinBound := Real.abs_sin_le_abs (x := Real.pi * x)
  rw [abs_mul, abs_of_pos Real.pi_pos] at sinBound
  linarith only [sinBound]

def binAverage (g : ℕ) (t : ℝ) : ℂ :=
  (g : ℂ)⁻¹ * ∫ x in -(g : ℝ) / 2..(g : ℝ) / 2, phase (x * t)

theorem norm_binAverage_sub_one (g : ℕ) (gPositive : 0 < g) (t : ℝ) :
    ‖binAverage g t - 1‖ ≤ Real.pi * (g : ℝ) * |t| := by
  have gCastPositive : (0 : ℝ) < g := by exact_mod_cast gPositive
  have gComplexNe : (g : ℂ) ≠ 0 := by exact_mod_cast gPositive.ne'
  let a : ℝ := -(g : ℝ) / 2
  let b : ℝ := (g : ℝ) / 2
  have ordered : a ≤ b := by dsimp [a, b]; linarith only [gCastPositive]
  have length : b - a = (g : ℝ) := by dsimp [a, b]; ring
  have representation : binAverage g t - 1 = (g : ℂ)⁻¹ * ∫ x in a..b, phase (x * t) - 1 := by
    have constantIntegrable : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume a b := intervalIntegrable_const
    rw [intervalIntegral.integral_sub ((continuous_phase_scale t).intervalIntegrable a b) constantIntegrable,
      intervalIntegral.integral_const, length, Complex.real_smul, Complex.ofReal_natCast, mul_one, mul_sub,
      inv_mul_cancel₀ gComplexNe]
    rfl
  rw [representation, norm_mul, norm_inv, Complex.norm_natCast]
  have pointwise (x : ℝ) (member : x ∈ Set.Icc a b) :
      ‖phase (x * t) - 1‖ ≤ Real.pi * (g : ℝ) * |t| := by
    have xBound : |x| ≤ (g : ℝ) / 2 := abs_le.mpr ⟨by simpa only [a, neg_div] using member.1, member.2⟩
    refine (norm_phase_sub_one_le (x * t)).trans ?_
    rw [abs_mul]
    calc
      _ ≤ 2 * Real.pi * (((g : ℝ) / 2) * |t|) := by gcongr
      _ = _ := by ring
  have integralBound := intervalIntegral.integral_mono_on (μ := volume) ordered
    (((continuous_phase_scale t).sub continuous_const).norm.intervalIntegrable a b)
    (intervalIntegrable_const (c := Real.pi * (g : ℝ) * |t|)) pointwise
  rw [intervalIntegral.integral_const, length, smul_eq_mul] at integralBound
  have normBound := (intervalIntegral.norm_integral_le_integral_norm (f := fun x => phase (x * t) - 1) ordered).trans
    integralBound
  calc
    _ ≤ (g : ℝ)⁻¹ * ((g : ℝ) * (Real.pi * (g : ℝ) * |t|)) :=
      mul_le_mul_of_nonneg_left normBound (inv_nonneg.mpr gCastPositive.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ gCastPositive.ne', one_mul]

theorem translate_progression_bin (g j : ℕ) (t : ℝ) :
    (∫ x in (g : ℝ) * ((j : ℝ) - 1 / 2)..(g : ℝ) * ((j : ℝ) + 1 / 2), phase (x * t)) =
      phase (((g * j : ℕ) : ℝ) * t) * ∫ x in -(g : ℝ) / 2..(g : ℝ) / 2, phase (x * t) := by
  have translation := intervalIntegral.integral_comp_add_right (fun x => phase (x * t))
    (a := -(g : ℝ) / 2) (b := (g : ℝ) / 2) (((g * j : ℕ) : ℝ))
  rw [show -(g : ℝ) / 2 + ((g * j : ℕ) : ℝ) = (g : ℝ) * ((j : ℝ) - 1 / 2) by push_cast; ring,
    show (g : ℝ) / 2 + ((g * j : ℕ) : ℝ) = (g : ℝ) * ((j : ℝ) + 1 / 2) by push_cast; ring] at translation
  rw [← translation, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  change phase ((x + ((g * j : ℕ) : ℝ)) * t) = _
  rw [add_mul, phase_add, mul_comm]

def progressionAverage (g l r : ℕ) (t : ℝ) : ℂ :=
  if l ≤ r then (g : ℂ)⁻¹ *
    ∫ x in (g : ℝ) * ((l : ℝ) + 1 / 2)..(g : ℝ) * ((r : ℝ) + 1 / 2), phase (x * t) else 0

theorem progressionAverage_eq (g l r : ℕ) (t : ℝ) :
    progressionAverage g l r t = wave g l r t * binAverage g t := by
  by_cases ordered : l ≤ r
  · let endpoint (k : ℕ) := (g : ℝ) * ((k : ℝ) + 1 / 2)
    rw [progressionAverage, if_pos ordered, binAverage]
    change (g : ℂ)⁻¹ * (∫ x in endpoint l..endpoint r, phase (x * t)) = _
    rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico ordered (a := endpoint)
      (fun i _ => (continuous_phase_scale t).intervalIntegrable (endpoint i) (endpoint (i + 1)))]
    have eachBin (i : ℕ) : (∫ x in endpoint i..endpoint (i + 1), phase (x * t)) =
        phase (((g * (i + 1) : ℕ) : ℝ) * t) * ∫ x in -(g : ℝ) / 2..(g : ℝ) / 2, phase (x * t) := by
      unfold endpoint
      rw [show (g : ℝ) * ((i : ℝ) + 1 / 2) = (g : ℝ) * ((((i + 1 : ℕ) : ℝ)) - 1 / 2) by push_cast; ring]
      exact translate_progression_bin g (i + 1) t
    simp_rw [eachBin, ← sum_mul]
    have reindex : (∑ i ∈ Ico l r, phase (((g * (i + 1) : ℕ) : ℝ) * t)) = wave g l r t := by
      unfold wave
      apply sum_bij (fun i _ => i + 1)
      · intro i hi
        obtain ⟨lower, upper⟩ := mem_Ico.mp hi
        exact mem_Ioc.mpr ⟨by omega, by omega⟩
      · intro i _ j _ equal
        omega
      · intro j hj
        obtain ⟨lower, upper⟩ := mem_Ioc.mp hj
        exact ⟨j - 1, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro i _
        rfl
    rw [reindex]
    ring
  · have empty : Ioc l r = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i member
      have := mem_Ioc.mp member
      omega
    simp [progressionAverage, ordered, wave, empty]

theorem wave_local_bound {g : ℕ} (l r : ℕ) {t : ℝ} (gPositive : 0 < g) (tNonzero : t ≠ 0)
    (near : (g : ℝ) * |t| ≤ 1 / 2) : ‖wave g l r t‖ ≤ 2 / ((g : ℝ) * |t|) := by
  have gRealPositive : (0 : ℝ) < g := by exact_mod_cast gPositive
  have bound := waveBound (l := l) (u := g) (n := g * r) (i := 0) gPositive
    (by rw [Nat.mul_div_cancel_left r gPositive]) (by simpa [abs_mul, abs_of_pos gRealPositive] using near)
  calc
    _ ≤ (2 / (g : ℝ)) * smoothKernel (1 / (((g * r : ℕ) : ℝ) + 1)) 0 t := by simpa using bound
    _ ≤ (2 / (g : ℝ)) * (1 / |t|) := by
      unfold smoothKernel
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (abs_pos.mpr tNonzero) (le_add_of_nonneg_left (by positivity))) (by positivity)
    _ = _ := by ring

theorem norm_wave_sub_average_le {g : ℕ} (l r : ℕ) {t : ℝ} (gPositive : 0 < g)
    (near : (g : ℝ) * |t| ≤ 1 / 2) : ‖wave g l r t - progressionAverage g l r t‖ ≤ 2 * Real.pi := by
  rw [progressionAverage_eq, ← mul_one_sub, norm_mul, norm_sub_rev]
  have binBound := norm_binAverage_sub_one g gPositive t
  have step := mul_le_mul_of_nonneg_left binBound (norm_nonneg (wave g l r t))
  refine step.trans ?_
  by_cases tZero : t = 0
  · simp [tZero, Real.pi_pos.le]
  have prodPositive : 0 < (g : ℝ) * |t| := mul_pos (by exact_mod_cast gPositive) (abs_pos.mpr tZero)
  calc
    _ ≤ (2 / ((g : ℝ) * |t|)) * (Real.pi * (g : ℝ) * |t|) :=
      mul_le_mul_of_nonneg_right (wave_local_bound l r gPositive tZero near) (by positivity)
    _ = _ := by field_simp

end
end DyadicMixedB4ProgressionApprox

end

section

open MeasureTheory

namespace DyadicMixedB4SineKernel

noncomputable section

private theorem abs_sub_bound (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa using abs_sub_le x 0 y

theorem integral_cos_inv_sq_le {b : ℝ} (bLower : 1 ≤ b) :
    |∫ t in (1 : ℝ)..b, Real.cos t / t ^ 2| ≤ 1 := by
  have positive {t : ℝ} (member : t ∈ Set.Icc 1 b) : 0 < t :=
    zero_lt_one.trans_le member.1
  have denominator : ContinuousOn (fun t : ℝ => t ^ 2) (Set.Icc 1 b) :=
    (continuous_id.pow 2).continuousOn
  have cosineContinuous : ContinuousOn (fun t => Real.cos t / t ^ 2) (Set.Icc 1 b) :=
    Real.continuous_cos.continuousOn.div denominator fun t ht => pow_ne_zero 2 (positive ht).ne'
  have inverseContinuous : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Set.Icc 1 b) :=
    continuousOn_const.div denominator fun t ht => pow_ne_zero 2 (positive ht).ne'
  rw [← Set.uIcc_of_le bLower] at cosineContinuous inverseContinuous
  have integralBound := intervalIntegral.integral_mono_on (μ := volume) bLower
    cosineContinuous.abs.intervalIntegrable inverseContinuous.intervalIntegrable
    (fun t ht => by
      rw [abs_div, abs_of_nonneg (sq_nonneg t)]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one t) (sq_nonneg t))
  have inverseIntegral : (∫ t in (1 : ℝ)..b, 1 / t ^ 2) = 1 - b⁻¹ := by
    calc
      _ = ∫ t in (1 : ℝ)..b, t ^ (-2 : ℤ) := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only [zpow_neg, zpow_ofNat, one_div]
      _ = _ := by
        rw [integral_zpow (Or.inr ⟨by norm_num, Set.notMem_uIcc_of_lt zero_lt_one
          (zero_lt_one.trans_le bLower)⟩)]
        norm_num <;> ring
  exact (intervalIntegral.abs_integral_le_integral_abs bLower).trans
    (integralBound.trans (by rw [inverseIntegral]; exact sub_le_self _ (by positivity)))

theorem integral_sinc_tail {b : ℝ} (bLower : 1 ≤ b) :
    |∫ t in (1 : ℝ)..b, Real.sinc t| ≤ 3 := by
  let primitive (t : ℝ) := -Real.cos t / t
  let correction (t : ℝ) := Real.cos t / t ^ 2
  have positive {t : ℝ} (member : t ∈ Set.uIcc 1 b) : 0 < t := by
    rw [Set.uIcc_of_le bLower] at member
    exact zero_lt_one.trans_le member.1
  have derivative (t : ℝ) (member : t ∈ Set.uIcc 1 b) :
      HasDerivAt primitive (Real.sinc t + correction t) t := by
    have tNonzero := (positive member).ne'
    have calcDeriv := (Real.hasDerivAt_cos t).neg.div (hasDerivAt_id t) tNonzero
    convert calcDeriv using 1
    · rfl
    · rw [Real.sinc_of_ne_zero tNonzero]
      simp only [correction, id_eq, neg_neg, Pi.neg_apply]
      field_simp
      ring
  have correctionContinuous : ContinuousOn correction (Set.uIcc 1 b) :=
    Real.continuous_cos.continuousOn.div (continuous_id.pow 2).continuousOn
      (fun t ht => pow_ne_zero 2 (positive ht).ne')
  have sincInt := Real.continuous_sinc.intervalIntegrable (μ := volume) 1 b
  have correctionInt : IntervalIntegrable correction volume 1 b := correctionContinuous.intervalIntegrable
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative (sincInt.add correctionInt)
  rw [intervalIntegral.integral_add sincInt correctionInt] at integral
  have boundary (t : ℝ) (h : 1 ≤ t) : |primitive t| ≤ 1 := by
    have tPositive : 0 < t := zero_lt_one.trans_le h
    unfold primitive
    rw [abs_div, abs_neg, abs_of_pos tPositive]
    exact (div_le_one tPositive).mpr ((Real.abs_cos_le_one t).trans h)
  have exactIntegral : (∫ t in (1 : ℝ)..b, Real.sinc t) =
      (primitive b - primitive 1) - ∫ t in (1 : ℝ)..b, correction t := by linarith only [integral]
  rw [exactIntegral]
  have correctionBound : |∫ t in (1 : ℝ)..b, correction t| ≤ 1 := integral_cos_inv_sq_le bLower
  have boundaryBound := (abs_sub_bound (primitive b) (primitive 1)).trans
    (add_le_add (boundary b bLower) (boundary 1 le_rfl))
  exact (abs_sub_bound _ _).trans (by linarith only [boundaryBound, correctionBound])

private theorem integral_sinc_small {b : ℝ} (bNonnegative : 0 ≤ b) (bUpper : b ≤ 1) :
    |∫ t in (0 : ℝ)..b, Real.sinc t| ≤ 1 := by
  refine (intervalIntegral.abs_integral_le_integral_abs bNonnegative).trans ?_
  have integrated := intervalIntegral.integral_mono_on (μ := volume) bNonnegative
    (Real.continuous_sinc.abs.intervalIntegrable 0 b) intervalIntegrable_const
    (fun t _ => Real.abs_sinc_le_one t)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at integrated
  exact integrated.trans bUpper

theorem integral_sinc_from_zero (b : ℝ) : |∫ t in (0 : ℝ)..b, Real.sinc t| ≤ 4 := by
  have positiveBound (u : ℝ) (uNonnegative : 0 ≤ u) :
      |∫ t in (0 : ℝ)..u, Real.sinc t| ≤ 4 := by
    rcases le_total u 1 with small | large
    · exact (integral_sinc_small uNonnegative small).trans (by norm_num)
    rw [← intervalIntegral.integral_add_adjacent_intervals (Real.continuous_sinc.intervalIntegrable 0 1)
      (Real.continuous_sinc.intervalIntegrable 1 u)]
    have smallBound := integral_sinc_small (b := 1) zero_le_one le_rfl
    have tailBound := integral_sinc_tail large
    exact (abs_add_le _ _).trans (by linarith only [smallBound, tailBound])
  rcases le_total 0 b with bNonnegative | bNonpositive
  · exact positiveBound b bNonnegative
  have reflect := intervalIntegral.integral_comp_neg Real.sinc (a := 0) (b := -b)
  simp only [Real.sinc_neg, neg_zero, neg_neg] at reflect
  rw [intervalIntegral.integral_symm, ← reflect, abs_neg]
  exact positiveBound (-b) (neg_nonneg.mpr bNonpositive)

theorem integral_sinc_uniform (a b : ℝ) : |∫ t in a..b, Real.sinc t| ≤ 8 := by
  have partition := intervalIntegral.integral_add_adjacent_intervals
    (Real.continuous_sinc.intervalIntegrable (μ := volume) 0 a) (Real.continuous_sinc.intervalIntegrable a b)
  have subtract : (∫ t in a..b, Real.sinc t) =
      (∫ t in (0 : ℝ)..b, Real.sinc t) - ∫ t in (0 : ℝ)..a, Real.sinc t := by linarith only [partition]
  rw [subtract]
  exact (abs_sub_bound _ _).trans (by linarith only [integral_sinc_from_zero a, integral_sinc_from_zero b])

def sineKernel (B x : ℝ) : ℝ := 2 * B * Real.sinc (2 * Real.pi * B * x)

theorem sineKernel_continuous (B : ℝ) : Continuous (sineKernel B) :=
  continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))

theorem integral_sineKernel_uniform (B a b : ℝ) (BNonnegative : 0 ≤ B) :
    |∫ t in a..b, sineKernel B t| ≤ 8 := by
  rcases eq_or_lt_of_le BNonnegative with zero | positive
  · simp [← zero, sineKernel]
  let dilation : ℝ := 2 * Real.pi * B
  have dilationPositive : 0 < dilation := by unfold dilation; positivity
  change |∫ t in a..b, (2 * B) * Real.sinc (dilation * t)| ≤ 8
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ dilationPositive.ne',
    smul_eq_mul, ← mul_assoc]
  have scale : (2 * B) * dilation⁻¹ = Real.pi⁻¹ := by
    unfold dilation
    field_simp [positive.ne', Real.pi_ne_zero]
  rw [scale, abs_mul, abs_of_nonneg (inv_nonneg.mpr Real.pi_pos.le)]
  have divisor : Real.pi⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
  calc
    _ ≤ 1 * |∫ t in dilation * a..dilation * b, Real.sinc t| :=
      mul_le_mul_of_nonneg_right divisor (abs_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using integral_sinc_uniform (dilation * a) (dilation * b)

theorem hasDerivAt_slidingSineIntegral (B u v x : ℝ) :
    HasDerivAt (fun m => ∫ t in m + u..m + v, sineKernel B t)
      (sineKernel B (x + v) - sineKernel B (x + u)) x := by
  have primitive (y : ℝ) : HasDerivAt (fun z => ∫ t in (0 : ℝ)..z, sineKernel B t) (sineKernel B y) y :=
    intervalIntegral.integral_hasDerivAt_right ((sineKernel_continuous B).intervalIntegrable 0 y)
      (sineKernel_continuous B).aestronglyMeasurable.stronglyMeasurableAtFilter
      (sineKernel_continuous B).continuousAt
  have atV := (primitive (x + v)).comp x ((hasDerivAt_id x).add_const v)
  have atU := (primitive (x + u)).comp x ((hasDerivAt_id x).add_const u)
  have difference := atV.sub atU
  simp only [id_eq, Function.comp_def, mul_one] at difference
  have functions : (fun y => ∫ t in y + u..y + v, sineKernel B t) =
      (fun y => ∫ t in (0 : ℝ)..y + v, sineKernel B t) -
      (fun y => ∫ t in (0 : ℝ)..y + u, sineKernel B t) := by
    funext y
    have partition := intervalIntegral.integral_add_adjacent_intervals
      ((sineKernel_continuous B).intervalIntegrable (μ := volume) 0 (y + u))
      ((sineKernel_continuous B).intervalIntegrable (y + u) (y + v))
    change _ = (∫ t in (0 : ℝ)..y + v, sineKernel B t) - ∫ t in (0 : ℝ)..y + u, sineKernel B t
    linarith only [partition]
  rw [functions]
  exact difference

end
end DyadicMixedB4SineKernel

end

section

open MeasureTheory DyadicMixedB4SineKernel DyadicMixedB4Geometric

namespace DyadicMixedB4KernelVariation

noncomputable section

theorem abs_sineKernel_le (B x : ℝ) (BNonnegative : 0 ≤ B) : |sineKernel B x| ≤ 2 * B := by
  rw [sineKernel, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * B)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)

theorem abs_sineKernel_mul_abs_le (B x : ℝ) (BNonnegative : 0 ≤ B) : |sineKernel B x| * |x| ≤ 1 := by
  rcases eq_or_lt_of_le BNonnegative with zeroB | positiveB
  · simp [← zeroB, sineKernel]
  by_cases zeroX : x = 0
  · simp [zeroX]
  have argNonzero : 2 * Real.pi * B * x ≠ 0 := mul_ne_zero (by positivity) zeroX
  rw [sineKernel, Real.sinc_of_ne_zero argNonzero, abs_mul, abs_div,
    abs_of_pos (by positivity : 0 < 2 * B), abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi * B)]
  have absNonzero := (abs_pos.mpr zeroX).ne'
  have cancel : 2 * B * (|Real.sin (2 * Real.pi * B * x)| / (2 * Real.pi * B * |x|)) * |x| =
      |Real.sin (2 * Real.pi * B * x)| / Real.pi := by
    field_simp [positiveB.ne', Real.pi_ne_zero, absNonzero]
  rw [cancel]
  exact (div_le_one Real.pi_pos).mpr ((Real.abs_sin_le_one _).trans (by linarith [Real.pi_gt_three]))

theorem abs_sineKernel_le_smooth (B x : ℝ) (BNonnegative : 0 ≤ B) (BUpper : B ≤ 1) :
    |sineKernel B x| ≤ 3 * smoothKernel 1 0 x := by
  rw [smoothKernel, sub_zero, mul_one_div]
  apply (le_div_iff₀ (by positivity)).mpr
  rw [mul_add, mul_one]
  linarith only [abs_sineKernel_le B x BNonnegative, abs_sineKernel_mul_abs_le B x BNonnegative, BUpper]

theorem exists_closer_centre (c : ℝ) :
    ∃ r ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, |t - r| ≤ |t - c| := by
  rcases le_total c 0 with lower | cNonnegative
  · refine ⟨0, by simp, fun t ht => ?_⟩
    rw [sub_zero, abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr (lower.trans ht.1))]
    linarith only [lower]
  rcases le_total c 1 with cUpper | upper
  · exact ⟨c, ⟨cNonnegative, cUpper⟩, fun _ _ => le_rfl⟩
  · refine ⟨1, by simp, fun t ht => ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos (sub_nonpos.mpr (ht.2.trans upper))]
    linarith only [upper]

theorem integral_smoothKernel_rescale (N c : ℝ) (NPositive : 0 < N) :
    (∫ t in (0 : ℝ)..N, smoothKernel 1 c t) = ∫ t in (0 : ℝ)..1, smoothKernel N⁻¹ (c / N) t := by
  have scaling := intervalIntegral.smul_integral_comp_mul_left (smoothKernel 1 c)
    (a := 0) (b := 1) N
  rw [smul_eq_mul, mul_zero, mul_one] at scaling
  rw [← scaling, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  change N * smoothKernel 1 c (N * t) = smoothKernel N⁻¹ (c / N) t
  unfold smoothKernel
  rw [show N * t - c = N * (t - c / N) by field_simp]
  rw [abs_mul, abs_of_pos NPositive, mul_one_div]
  have inversePositive : 0 < N⁻¹ := inv_pos.mpr NPositive
  field_simp

theorem integral_smoothKernel_shift_le (N c : ℝ) (NPositive : 0 < N) :
    (∫ t in (0 : ℝ)..N, smoothKernel 1 c t) ≤ 2 * Real.log (N + 1) := by
  obtain ⟨r, rMember, closer⟩ := exists_closer_centre (c / N)
  have aPositive : 0 < N⁻¹ := inv_pos.mpr NPositive
  have ratio : (1 + N⁻¹) / N⁻¹ = N + 1 := by field_simp
  rw [integral_smoothKernel_rescale N c NPositive]
  have compare := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((cont_smoothKernel aPositive (c := c / N)).intervalIntegrable 0 1)
    ((cont_smoothKernel aPositive (c := r)).intervalIntegrable 0 1) (fun t member => by
      unfold smoothKernel
      exact one_div_le_one_div_of_le (by positivity) (add_le_add_right (closer t member) _))
  have original := integral_smoothKernel aPositive rMember.1 rMember.2
  rw [ratio] at original
  exact compare.trans original

theorem integral_abs_shifted_sineKernel_le (N B x : ℝ) (NPositive : 0 < N)
    (BNonnegative : 0 ≤ B) (BUpper : B ≤ 1) :
    (∫ t in (0 : ℝ)..N, |sineKernel B (t + x)|) ≤ 6 * Real.log (N + 1) := by
  have shifted : Continuous (fun t => sineKernel B (t + x)) :=
    (sineKernel_continuous B).comp (continuous_id.add continuous_const)
  have smooth : Continuous (fun t => 3 * smoothKernel 1 (-x) t) :=
    continuous_const.mul (cont_smoothKernel zero_lt_one)
  have compare := intervalIntegral.integral_mono_on (μ := volume) NPositive.le
    (shifted.abs.intervalIntegrable 0 N) (smooth.intervalIntegrable 0 N) (fun t _ => by
      simpa only [smoothKernel, sub_zero, sub_neg_eq_add] using
        abs_sineKernel_le_smooth B (t + x) BNonnegative BUpper)
  rw [intervalIntegral.integral_const_mul] at compare
  exact compare.trans (by linarith only [integral_smoothKernel_shift_le N (-x) NPositive])

theorem integral_slidingSine_deriv_bound (N B u v : ℝ) (NPositive : 0 < N)
    (BNonnegative : 0 ≤ B) (BUpper : B ≤ 1) :
    (∫ t in (0 : ℝ)..N, |sineKernel B (t + v) - sineKernel B (t + u)|) ≤ 12 * Real.log (N + 1) := by
  have continuousShift (x : ℝ) : Continuous (fun t => sineKernel B (t + x)) :=
    (sineKernel_continuous B).comp (continuous_id.add continuous_const)
  have normSum : IntervalIntegrable (fun t => |sineKernel B (t + v)| + |sineKernel B (t + u)|) volume 0 N :=
    ((continuousShift v).abs.add (continuousShift u).abs).intervalIntegrable 0 N
  have normDifference : IntervalIntegrable (fun t => |sineKernel B (t + v) - sineKernel B (t + u)|)
      volume 0 N := ((continuousShift v).sub (continuousShift u)).abs.intervalIntegrable 0 N
  have integrated := intervalIntegral.integral_mono_on (μ := volume) NPositive.le
    normDifference normSum (fun t _ => by simpa only [sub_zero, zero_sub, abs_neg] using
      (abs_sub_le (sineKernel B (t + v)) 0 (sineKernel B (t + u))))
  rw [intervalIntegral.integral_add ((continuousShift v).abs.intervalIntegrable 0 N)
    ((continuousShift u).abs.intervalIntegrable 0 N)] at integrated
  exact integrated.trans (by linarith only [integral_abs_shifted_sineKernel_le N B v NPositive BNonnegative BUpper,
    integral_abs_shifted_sineKernel_le N B u NPositive BNonnegative BUpper])

end
end DyadicMixedB4KernelVariation

end

section

open MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcCenters
open DyadicMixedB4ProgressionApprox DyadicMixedB4SineKernel

namespace DyadicMixedB4NearKernelFourier

noncomputable section

theorem phase_integral_symmetric (B x : ℝ) :
    (∫ β in -B..B, phase (x * β)) = (sineKernel B x : ℂ) := by
  by_cases BZero : B = 0
  · simp [BZero, sineKernel]
  by_cases xZero : x = 0
  · simp only [xZero, zero_mul, phase, Complex.ofReal_zero, Complex.exp_zero, sineKernel,
      mul_zero, Real.sinc_zero, mul_one, intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  let c : ℂ := (2 * (Real.pi : ℂ) * (x : ℂ)) * Complex.I
  let θ : ℝ := 2 * Real.pi * B * x
  have cNonzero : c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast xZero)) Complex.I_ne_zero
  have θNonzero : θ ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) BZero) xZero
  have frequency (β : ℝ) : phase (x * β) = Complex.exp (c * (β : ℂ)) := by
    unfold phase c
    congr 1
    push_cast
    ring
  have plus : c * (B : ℂ) = (θ : ℂ) * Complex.I := by unfold c θ; push_cast; ring
  have minus : c * ((-B : ℝ) : ℂ) = (-(θ : ℂ)) * Complex.I := by unfold c θ; push_cast; ring
  simp_rw [frequency]
  rw [integral_exp_mul_complex cNonzero, plus, minus, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg, sineKernel, Real.sinc_of_ne_zero θNonzero]
  push_cast
  unfold c θ
  push_cast
  field_simp [Real.pi_ne_zero, BZero, xZero, Complex.I_ne_zero]
  ring

theorem swap_phase_integral (B L R s : ℝ) :
    (∫ β in -B..B, ∫ x in L..R, phase ((s + x) * β)) =
      ∫ x in L..R, ∫ β in -B..B, phase ((s + x) * β) := by
  apply intervalIntegral_intervalIntegral_swap
  have continuous : Continuous (fun p : ℝ × ℝ => phase ((s + p.2) * p.1)) := by
    unfold phase
    fun_prop
  exact (continuous.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

theorem integrated_progressionAverage (g l r : ℕ) (B s : ℝ) (ordered : l ≤ r) :
    (∫ β in -B..B, phase (s * β) * progressionAverage g l r β) = (g : ℂ)⁻¹ *
      Complex.ofReal (∫ x in s + (g : ℝ) * ((l : ℝ) + 1 / 2)..s + (g : ℝ) * ((r : ℝ) + 1 / 2),
        sineKernel B x) := by
  let L := (g : ℝ) * ((l : ℝ) + 1 / 2)
  let R := (g : ℝ) * ((r : ℝ) + 1 / 2)
  simp_rw [progressionAverage, if_pos ordered]
  calc
    _ = (g : ℂ)⁻¹ * ∫ β in -B..B, ∫ x in L..R, phase ((s + x) * β) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro β _
      change phase (s * β) * ((g : ℂ)⁻¹ * ∫ x in L..R, phase (x * β)) = _
      rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro x _
      change phase (s * β) * phase (x * β) = phase ((s + x) * β)
      rw [add_mul, phase_add]
    _ = (g : ℂ)⁻¹ * ∫ x in L..R, ∫ β in -B..B, phase ((s + x) * β) := by rw [swap_phase_integral]
    _ = _ := by
      simp_rw [phase_integral_symmetric]
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_comp_add_left]

end
end DyadicMixedB4NearKernelFourier

end

section

open MeasureTheory DyadicMixedB4ArcGeometry DyadicMixedB4Geometric
open DyadicMixedB4ProgressionApprox DyadicMixedB4SineKernel DyadicMixedB4NearKernelFourier

namespace DyadicMixedB4WindowKernel

noncomputable section

def innerRadius (n M H q : ℕ) : ℝ := min (radius M) ((H : ℝ) / ((q : ℝ) * n))

theorem radius_nonnegative (M : ℕ) : 0 ≤ radius M := by unfold radius; positivity

theorem innerRadius_nonnegative (n M H q : ℕ) : 0 ≤ innerRadius n M H q := by
  unfold innerRadius
  exact le_min (radius_nonnegative M) (by positivity)

theorem window_subset_interval (n M B H q : ℕ) : window n M B H q ⊆ Set.Icc (-radius M) (radius M) :=
  fun _ member => abs_le.mp member.1

theorem set_integral_window (n M B H q : ℕ) {f : ℝ → ℂ} (continuous : Continuous f) :
    (∫ t in window n M B H q, f t) = (∫ t in -radius M..radius M, f t) -
      if q ≤ B then ∫ t in -innerRadius n M H q..innerRadius n M H q, f t else 0 := by
  let R := radius M
  let r := innerRadius n M H q
  have radiusOrdered : -R ≤ R := by have h := radius_nonnegative M; change -radius M ≤ radius M; linarith only [h]
  have innerOrdered : -r ≤ r := by
    have h := innerRadius_nonnegative n M H q
    change -innerRadius n M H q ≤ innerRadius n M H q
    linarith only [h]
  have innerCap : r ≤ R := min_le_left _ _
  have innerSubset : Set.Icc (-r) r ⊆ Set.Icc (-R) R := Set.Icc_subset_Icc (neg_le_neg innerCap) innerCap
  by_cases inside : q ≤ B
  · have setEquality : window n M B H q = Set.Icc (-R) R \ Set.Icc (-r) r := by
      ext t
      have notLarge : ¬B < q := not_lt_of_ge inside
      change (|t| ≤ R ∧ (B < q ∨ (H : ℝ) / ((q : ℝ) * n) < |t|)) ↔
        t ∈ Set.Icc (-R) R \ Set.Icc (-r) r
      simp only [notLarge, false_or, Set.mem_sdiff, Set.mem_Icc, ← abs_le, not_le]
      change (_ ∧ _) ↔ |t| ≤ R ∧ min R ((H : ℝ) / ((q : ℝ) * n)) < |t|
      rw [min_lt_iff]
      constructor
      · rintro ⟨upper, width⟩
        exact ⟨upper, Or.inr width⟩
      · rintro ⟨upper, outside | width⟩
        · exact (not_lt_of_ge upper outside).elim
        · exact ⟨upper, width⟩
    rw [setEquality, setIntegral_sdiff measurableSet_Icc continuous.continuousOn.integrableOn_Icc innerSubset,
      if_pos inside, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le radiusOrdered, ← intervalIntegral.integral_of_le innerOrdered]
  · have setEquality : window n M B H q = Set.Icc (-R) R := by
      ext t
      have large : B < q := lt_of_not_ge inside
      simp [window, large, R, ← abs_le]
    rw [setEquality, if_neg inside, sub_zero, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le radiusOrdered]

theorem norm_window_replacement_le (n M B H q g l r : ℕ) (s : ℝ) (gPositive : 0 < g)
    (radiusBound : (g : ℝ) * radius M ≤ 1 / 2) :
    ‖∫ t in window n M B H q, phase (s * t) * (wave g l r t - progressionAverage g l r t)‖ ≤
      (2 * Real.pi) * (2 * radius M) := by
  have massBound : volume (window n M B H q) ≤ volume (Set.Icc (-radius M) (radius M)) :=
    measure_mono (window_subset_interval n M B H q)
  have intervalFinite : volume (Set.Icc (-radius M) (radius M)) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have massFinite : volume (window n M B H q) < ⊤ := massBound.trans_lt intervalFinite
  have realMassBound : volume.real (window n M B H q) ≤ 2 * radius M := by
    calc
      _ ≤ (volume (Set.Icc (-radius M) (radius M))).toReal :=
        ENNReal.toReal_mono intervalFinite.ne massBound
      _ = _ := by rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [radius_nonnegative M])]; ring
  have pointBound (t : ℝ) (member : t ∈ window n M B H q) :
      ‖phase (s * t) * (wave g l r t - progressionAverage g l r t)‖ ≤ 2 * Real.pi := by
    have near := (mul_le_mul_of_nonneg_left member.1 (Nat.cast_nonneg g : (0 : ℝ) ≤ g)).trans radiusBound
    rw [norm_mul, norm_phase', one_mul]
    exact norm_wave_sub_average_le l r gPositive near
  exact (norm_setIntegral_le_of_norm_le_const massFinite pointBound).trans
    (mul_le_mul_of_nonneg_left realMassBound (by positivity))

def scalarKernel (g l r : ℕ) (W s : ℝ) : ℝ :=
  if l ≤ r then (g : ℝ)⁻¹ *
    ∫ x in s + (g : ℝ) * ((l : ℝ) + 1 / 2)..s + (g : ℝ) * ((r : ℝ) + 1 / 2), sineKernel W x else 0

theorem progressionAverage_continuous (g l r : ℕ) : Continuous (progressionAverage g l r) := by
  have binIdentity (t : ℝ) : binAverage g t = (g : ℂ)⁻¹ * (sineKernel ((g : ℝ) / 2) t : ℂ) := by
    unfold binAverage
    rw [neg_div]
    simp_rw [mul_comm _ t, phase_integral_symmetric]
  change Continuous (fun t : ℝ => progressionAverage g l r t)
  simp_rw [progressionAverage_eq, binIdentity]
  have waveContinuous : Continuous (wave g l r) := by unfold wave phase; fun_prop
  exact waveContinuous.mul (continuous_const.mul (Complex.continuous_ofReal.comp (sineKernel_continuous _)))

theorem integral_progression_window (n M B H q g l r : ℕ) (s : ℝ) :
    (∫ t in window n M B H q, phase (s * t) * progressionAverage g l r t) =
      Complex.ofReal (scalarKernel g l r (radius M) s -
        if q ≤ B then scalarKernel g l r (innerRadius n M H q) s else 0) := by
  have continuous : Continuous (fun t : ℝ => phase (s * t) * progressionAverage g l r t) := by
    have left : Continuous (fun t : ℝ => phase (s * t)) := by unfold phase; fun_prop
    exact left.mul (progressionAverage_continuous g l r)
  have identify (W : ℝ) : (∫ t in -W..W, phase (s * t) * progressionAverage g l r t) =
      (scalarKernel g l r W s : ℂ) := by
    by_cases ordered : l ≤ r
    · rw [integrated_progressionAverage g l r W s ordered, scalarKernel, if_pos ordered,
        Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    · simp [progressionAverage, scalarKernel, ordered]
  rw [set_integral_window n M B H q continuous, identify]
  by_cases inside : q ≤ B
  · rw [if_pos inside, if_pos inside, identify, Complex.ofReal_sub]
  · simp [inside]

end
end DyadicMixedB4WindowKernel

end

section

open Finset MeasureTheory

namespace DyadicMixedB4Abel

theorem kernel_sum_range_bound (n : ℕ) (coefficient : ℕ → ℂ) (kernel derivative : ℝ → ℝ)
    {P K : ℝ} (PNonnegative : 0 ≤ P) (KNonnegative : 0 ≤ K)
    (prefixBound : ∀ x ≤ n, ‖∑ j ∈ range x, coefficient j‖ ≤ P)
    (endpointBound : |kernel ((n - 1 : ℕ) : ℝ)| ≤ K)
    (hasDerivative : ∀ t, HasDerivAt kernel (derivative t) t) (continuous : Continuous derivative) :
    ‖∑ j ∈ range n, kernel (j : ℝ) • coefficient j‖ ≤
      (K + ∫ t in (0 : ℝ)..((n - 1 : ℕ) : ℝ), |derivative t|) * P := by
  have endBound : ‖kernel ((n - 1 : ℕ) : ℝ) • (∑ j ∈ range n, coefficient j)‖ ≤ K * P := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul endpointBound (prefixBound n le_rfl) (norm_nonneg _) KNonnegative
  have differenceBound (i : ℕ) : |kernel ((i + 1 : ℕ) : ℝ) - kernel (i : ℝ)| ≤
      ∫ t in (i : ℝ)..((i + 1 : ℕ) : ℝ), |derivative t| := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivative t)
      (continuous.intervalIntegrable (i : ℝ) ((i + 1 : ℕ) : ℝ))]
    exact intervalIntegral.abs_integral_le_integral_abs (by exact_mod_cast Nat.le_succ i)
  have integralPartition :
      (∑ i ∈ range (n - 1), ∫ t in (i : ℝ)..((i + 1 : ℕ) : ℝ), |derivative t|) =
        ∫ t in (0 : ℝ)..((n - 1 : ℕ) : ℝ), |derivative t| := by
    simpa only [Nat.cast_zero] using (intervalIntegral.sum_integral_adjacent_intervals
      (a := fun i : ℕ => (i : ℝ)) (n := n - 1) (μ := volume)
      (fun i _ => continuous.abs.intervalIntegrable (i : ℝ) ((i + 1 : ℕ) : ℝ)))
  have variationBound : ‖∑ i ∈ range (n - 1), (kernel ((i + 1 : ℕ) : ℝ) - kernel (i : ℝ)) •
      (∑ j ∈ range (i + 1), coefficient j)‖ ≤
      (∫ t in (0 : ℝ)..((n - 1 : ℕ) : ℝ), |derivative t|) * P := by
    refine (norm_sum_le _ _).trans ?_
    rw [← integralPartition, sum_mul]
    refine sum_le_sum fun i iMember => ?_
    have iBound := mem_range.mp iMember
    have prefixEstimate := prefixBound (i + 1) (by omega)
    have segmentNonnegative : 0 ≤ ∫ t in (i : ℝ)..((i + 1 : ℕ) : ℝ), |derivative t| :=
      intervalIntegral.integral_nonneg_of_forall (by exact_mod_cast Nat.le_succ i) (fun t => abs_nonneg _)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (differenceBound i) prefixEstimate (norm_nonneg _) segmentNonnegative
  rw [Finset.sum_range_by_parts (fun j : ℕ => kernel (j : ℝ)) coefficient n]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ K * P + (∫ t in (0 : ℝ)..((n - 1 : ℕ) : ℝ), |derivative t|) * P :=
      (add_le_add endBound variationBound)
    _ = _ := by ring

end DyadicMixedB4Abel

end

section

open MeasureTheory Finset DyadicMixedB4ArcGeometry DyadicMixedB4WindowKernel
open DyadicMixedB4SineKernel DyadicMixedB4KernelVariation

namespace DyadicMixedB4KernelControl

noncomputable section

def scalarGradient (g l r : ℕ) (W s : ℝ) : ℝ :=
  if l ≤ r then (g : ℝ)⁻¹ * (sineKernel W (s + (g : ℝ) * ((r : ℝ) + 1 / 2)) -
      sineKernel W (s + (g : ℝ) * ((l : ℝ) + 1 / 2))) else 0

theorem scalarKernel_derivative (g l r : ℕ) (W s : ℝ) :
    HasDerivAt (scalarKernel g l r W) (scalarGradient g l r W s) s := by
  unfold scalarKernel scalarGradient
  by_cases ordered : l ≤ r
  · simp only [if_pos ordered]
    exact (hasDerivAt_slidingSineIntegral W _ _ s).const_mul (g : ℝ)⁻¹
  · simp only [if_neg ordered]
    exact hasDerivAt_const s 0

theorem scalarGradient_continuous (g l r : ℕ) (W : ℝ) : Continuous (scalarGradient g l r W) := by
  unfold scalarGradient
  by_cases ordered : l ≤ r
  · simp only [if_pos ordered]
    exact continuous_const.mul (((sineKernel_continuous W).comp (continuous_id.add continuous_const)).sub
      ((sineKernel_continuous W).comp (continuous_id.add continuous_const)))
  · simp only [if_neg ordered]
    exact continuous_const

theorem abs_scalarKernel_le (g l r : ℕ) (W s : ℝ) (Wnonnegative : 0 ≤ W) :
    |scalarKernel g l r W s| ≤ 8 / (g : ℝ) := by
  unfold scalarKernel
  by_cases ordered : l ≤ r
  · simp only [if_pos ordered, abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg g : (0 : ℝ) ≤ g)]
    calc
      _ ≤ (g : ℝ)⁻¹ * 8 := mul_le_mul_of_nonneg_left (integral_sineKernel_uniform W _ _ Wnonnegative)
        (inv_nonneg.mpr (Nat.cast_nonneg g))
      _ = _ := by ring
  · simp [ordered] <;> positivity

theorem scalarGradient_variation_le (g l r : ℕ) (W N shift : ℝ) (NPositive : 0 < N)
    (Wnonnegative : 0 ≤ W) (Wupper : W ≤ 1) :
    (∫ t in (0 : ℝ)..N, |scalarGradient g l r W (t + shift)|) ≤ 12 / (g : ℝ) * Real.log (N + 1) := by
  unfold scalarGradient
  by_cases ordered : l ≤ r
  · simp only [if_pos ordered, abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg g : (0 : ℝ) ≤ g), add_assoc]
    rw [intervalIntegral.integral_const_mul]
    calc
      _ ≤ (g : ℝ)⁻¹ * (12 * Real.log (N + 1)) :=
        mul_le_mul_of_nonneg_left (integral_slidingSine_deriv_bound N W _ _ NPositive Wnonnegative Wupper) (by positivity)
      _ = _ := by ring
  · simp only [if_neg ordered, abs_zero, intervalIntegral.integral_zero]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith only [NPositive]))

def windowKernel (n M B H q g l r : ℕ) (s : ℝ) : ℝ := scalarKernel g l r (radius M) s -
  if q ≤ B then scalarKernel g l r (innerRadius n M H q) s else 0

def windowGradient (n M B H q g l r : ℕ) (s : ℝ) : ℝ := scalarGradient g l r (radius M) s -
  if q ≤ B then scalarGradient g l r (innerRadius n M H q) s else 0

theorem windowKernel_derivative (n M B H q g l r : ℕ) (s : ℝ) :
    HasDerivAt (windowKernel n M B H q g l r) (windowGradient n M B H q g l r s) s := by
  unfold windowKernel windowGradient
  by_cases inside : q ≤ B
  · simp only [if_pos inside]
    exact (scalarKernel_derivative g l r (radius M) s).sub (scalarKernel_derivative g l r (innerRadius n M H q) s)
  · simp only [if_neg inside, sub_zero]
    exact scalarKernel_derivative g l r (radius M) s

theorem windowGradient_continuous (n M B H q g l r : ℕ) : Continuous (windowGradient n M B H q g l r) := by
  unfold windowGradient
  by_cases inside : q ≤ B
  · simp only [if_pos inside]
    exact (scalarGradient_continuous g l r (radius M)).sub (scalarGradient_continuous g l r (innerRadius n M H q))
  · simp only [if_neg inside, sub_zero]
    exact scalarGradient_continuous g l r (radius M)

theorem abs_windowKernel_le (n M B H q g l r : ℕ) (s : ℝ) :
    |windowKernel n M B H q g l r s| ≤ 16 / (g : ℝ) := by
  unfold windowKernel
  have first := abs_scalarKernel_le g l r (radius M) s (radius_nonnegative M)
  by_cases inside : q ≤ B
  · simp only [if_pos inside]
    have second := abs_scalarKernel_le g l r (innerRadius n M H q) s (innerRadius_nonnegative n M H q)
    have difference : |scalarKernel g l r (radius M) s - scalarKernel g l r (innerRadius n M H q) s| ≤
        |scalarKernel g l r (radius M) s| + |scalarKernel g l r (innerRadius n M H q) s| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (scalarKernel g l r (radius M) s) 0 (scalarKernel g l r (innerRadius n M H q) s))
    refine difference.trans ?_
    rw [show (16 : ℝ) / g = 8 / g + 8 / g by ring]
    exact add_le_add first second
  · simp only [if_neg inside, sub_zero]
    exact first.trans (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))

theorem windowGradient_variation_le (n M B H q g l r : ℕ) (N shift : ℝ) (NPositive : 0 < N)
    (radiusUpper : radius M ≤ 1) :
    (∫ t in (0 : ℝ)..N, |windowGradient n M B H q g l r (t + shift)|) ≤
      24 / (g : ℝ) * Real.log (N + 1) := by
  let first (t : ℝ) := scalarGradient g l r (radius M) (t + shift)
  let second (t : ℝ) := scalarGradient g l r (innerRadius n M H q) (t + shift)
  have firstContinuous : Continuous first :=
    (scalarGradient_continuous g l r (radius M)).comp (continuous_id.add continuous_const)
  have secondContinuous : Continuous second :=
    (scalarGradient_continuous g l r (innerRadius n M H q)).comp (continuous_id.add continuous_const)
  have boundFirst := scalarGradient_variation_le g l r (radius M) N shift NPositive (radius_nonnegative M) radiusUpper
  have logNonnegative : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by linarith only [NPositive])
  unfold windowGradient
  by_cases inside : q ≤ B
  · simp only [if_pos inside]
    have boundSecond := scalarGradient_variation_le g l r (innerRadius n M H q) N shift NPositive
      (innerRadius_nonnegative n M H q) ((min_le_left _ _).trans radiusUpper)
    change (∫ t in (0 : ℝ)..N, |first t - second t|) ≤ _
    have differenceIntegrable : IntervalIntegrable (fun t => |first t - second t|) volume 0 N :=
      (firstContinuous.sub secondContinuous).abs.intervalIntegrable 0 N
    have sumIntegrable : IntervalIntegrable (fun t => |first t| + |second t|) volume 0 N :=
      (firstContinuous.abs.add secondContinuous.abs).intervalIntegrable 0 N
    have compare := intervalIntegral.integral_mono_on NPositive.le differenceIntegrable sumIntegrable
      (fun t _ => by simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (first t) 0 (second t)))
    rw [intervalIntegral.integral_add (firstContinuous.abs.intervalIntegrable 0 N)
      (secondContinuous.abs.intervalIntegrable 0 N)] at compare
    apply compare.trans
    rw [show (24 : ℝ) / g * Real.log (N + 1) =
      12 / g * Real.log (N + 1) + 12 / g * Real.log (N + 1) by ring]
    exact add_le_add boundFirst boundSecond
  · simp only [if_neg inside, sub_zero]
    exact boundFirst.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)) logNonnegative)

theorem weighted_windowKernel_sum_le (n M B H q g l r a X : ℕ) (coefficient : ℕ → ℂ)
    (nPositive : 0 < n) (aPositive : 0 < a) (lengthBound : a * X ≤ n)
    (radiusUpper : radius M ≤ 1) {P : ℝ} (PNonnegative : 0 ≤ P)
    (prefixBound : ∀ x ≤ X, ‖∑ j ∈ range x, coefficient j‖ ≤ P) :
    ‖∑ j ∈ range X, windowKernel n M B H q g l r ((a : ℝ) * ((j : ℝ) + 1) - n) • coefficient j‖ ≤
      (16 / (g : ℝ) + 24 / (g : ℝ) * Real.log ((n : ℝ) + 1)) * P := by
  let shift : ℝ := (a : ℝ) - n
  let f (t : ℝ) := windowKernel n M B H q g l r ((a : ℝ) * t + shift)
  let D (t : ℝ) := windowGradient n M B H q g l r ((a : ℝ) * t + shift) * (a : ℝ)
  have aRealPositive : (0 : ℝ) < a := by exact_mod_cast aPositive
  have nRealPositive : (0 : ℝ) < n := by exact_mod_cast nPositive
  have fDerivative (t : ℝ) : HasDerivAt f (D t) t := by
    have linear := ((hasDerivAt_id t).const_mul (a : ℝ)).add_const shift
    simp only [id_eq, mul_one] at linear
    exact (windowKernel_derivative n M B H q g l r ((a : ℝ) * t + shift)).comp t linear
  have DContinuous : Continuous D :=
    ((windowGradient_continuous n M B H q g l r).comp
      ((continuous_const.mul continuous_id).add continuous_const)).mul continuous_const
  let upper : ℝ := ((X - 1 : ℕ) : ℝ)
  have compareUpper : (a : ℝ) * upper ≤ n := by
    dsimp [upper]
    exact_mod_cast (Nat.mul_le_mul_left a (Nat.sub_le X 1)).trans lengthBound
  have variationBound : (∫ t in (0 : ℝ)..upper, |D t|) ≤ 24 / (g : ℝ) * Real.log ((n : ℝ) + 1) := by
    let gradient (t : ℝ) := |windowGradient n M B H q g l r (t + shift)|
    have gradientContinuous : Continuous gradient :=
      ((windowGradient_continuous n M B H q g l r).comp (continuous_id.add continuous_const)).abs
    have scaling := intervalIntegral.smul_integral_comp_mul_left gradient (a := 0) (b := upper) (a : ℝ)
    rw [smul_eq_mul, mul_zero] at scaling
    calc
      _ = (a : ℝ) * ∫ t in (0 : ℝ)..upper, gradient ((a : ℝ) * t) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _
        change |windowGradient n M B H q g l r ((a : ℝ) * t + shift) * (a : ℝ)| = _
        rw [abs_mul, abs_of_pos aRealPositive, mul_comm]
      _ = ∫ t in (0 : ℝ)..(a : ℝ) * upper, gradient t := scaling
      _ ≤ ∫ t in (0 : ℝ)..n, gradient t := intervalIntegral.integral_mono_interval le_rfl (by positivity)
        compareUpper (Filter.Eventually.of_forall (fun t => abs_nonneg _)) (gradientContinuous.intervalIntegrable _ _)
      _ ≤ _ := windowGradient_variation_le n M B H q g l r n shift nRealPositive radiusUpper
  have kernelBound := DyadicMixedB4Abel.kernel_sum_range_bound X coefficient f D PNonnegative
    (show 0 ≤ 16 / (g : ℝ) by positivity) prefixBound
    (abs_windowKernel_le n M B H q g l r _) fDerivative DContinuous
  have sameArgument (j : ℕ) : (a : ℝ) * ((j : ℝ) + 1) - n = (a : ℝ) * (j : ℝ) + shift := by
    unfold shift
    ring
  simp_rw [sameArgument]
  change ‖∑ j ∈ range X, f (j : ℝ) • coefficient j‖ ≤ _
  exact kernelBound.trans (mul_le_mul_of_nonneg_right (add_le_add_right variationBound _) PNonnegative)

end
end DyadicMixedB4KernelControl

end

section

open Finset MeasureTheory
open scoped ComplexConjugate

namespace DyadicMixedB4Fourier

noncomputable section

def frequency (k : ℤ) : ℂ := (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

def mode (k : ℤ) (t : ℝ) : ℂ := Complex.exp (frequency k * (t : ℂ))

theorem continuous_mode (k : ℤ) : Continuous (mode k) := by
  unfold mode
  fun_prop

theorem periodic_mode (k : ℤ) : Function.Periodic (mode k) 1 := by
  intro t
  unfold mode
  rw [Complex.ofReal_add, Complex.ofReal_one, mul_add, Complex.exp_add]
  have onePhase : Complex.exp (frequency k * 1) = 1 := by
    simp [frequency, Complex.exp_int_mul_two_pi_mul_I]
  rw [onePhase, mul_one]

theorem hasDerivAt_mode (k : ℤ) (t : ℝ) :
    HasDerivAt (mode k) (frequency k * mode k t) t := by
  have linear : HasDerivAt (fun z : ℂ => frequency k * z) (frequency k) (t : ℂ) := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id (t : ℂ)).const_mul (frequency k)
  change HasDerivAt (fun x : ℝ => Complex.exp (frequency k * (x : ℂ)))
    (frequency k * Complex.exp (frequency k * (t : ℂ))) t
  rw [mul_comm (frequency k)]
  exact linear.cexp.comp_ofReal (z := t)

theorem mode_integral (k : ℤ) :
    (∫ t in (0 : ℝ)..1, mode k t) = if k = 0 then 1 else 0 := by
  by_cases zero : k = 0
  · simp [zero, mode, frequency]
  · have kNonzero : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr zero
    have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have frequencyNonzero : frequency k ≠ 0 := by
      exact mul_ne_zero kNonzero (mul_ne_zero (mul_ne_zero (by norm_num) piNonzero) Complex.I_ne_zero)
    change (∫ t in (0 : ℝ)..1, Complex.exp (frequency k * (t : ℂ))) = _
    rw [ite_eq_right zero, integral_exp_mul_complex frequencyNonzero]
    simp [frequency, Complex.exp_int_mul_two_pi_mul_I]

theorem mode_mul_conj (j k : ℤ) (t : ℝ) :
    mode j t * star (mode k t) = mode (j - k) t := by
  change Complex.exp (frequency j * (t : ℂ)) *
    conj (Complex.exp (frequency k * (t : ℂ))) = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  unfold mode frequency
  congr 1
  have conjTwo : (starRingEnd ℂ) 2 = 2 := by
    simpa only [Nat.cast_ofNat] using (map_natCast (starRingEnd ℂ) 2)
  simp [map_mul, Complex.conj_I, Int.cast_sub, conjTwo]
  ring

theorem parseval_finite_modes (limit : ℕ) (coefficient : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1,
      ((‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ j ∈ range limit, ((‖coefficient j‖ ^ 2 : ℝ) : ℂ) := by
  let entry (j k : ℕ) (t : ℝ) : ℂ :=
    coefficient j * star (coefficient k) * mode ((j : ℤ) - (k : ℤ)) t
  have entryContinuous (j k : ℕ) : Continuous (entry j k) :=
    continuous_const.mul (continuous_mode ((j : ℤ) - (k : ℤ)))
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ j ∈ range limit, ∑ k ∈ range limit, entry j k t := by
      apply intervalIntegral.integral_congr
      intro t _
      change ((‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) t‖ ^ 2 : ℝ) : ℂ) = _
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      change (∑ j ∈ range limit, coefficient j * mode (j : ℤ) t) *
          star (∑ j ∈ range limit, coefficient j * mode (j : ℤ) t) = _
      rw [star_sum, sum_mul_sum]
      refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
      rw [star_mul]
      calc
        _ = coefficient j * star (coefficient k) *
            (mode (j : ℤ) t * star (mode (k : ℤ) t)) := by ac_rfl
        _ = _ := by rw [mode_mul_conj]
    _ = ∑ j ∈ range limit, ∑ k ∈ range limit, ∫ t in (0 : ℝ)..1, entry j k t := by
      rw [intervalIntegral.integral_finsetSum]
      · refine sum_congr rfl fun j _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        exact fun k _ => (entryContinuous j k).intervalIntegrable _ _
      · intro j _
        exact (continuous_finsetSum _ fun k _ => entryContinuous j k).intervalIntegrable _ _
    _ = _ := by
      refine sum_congr rfl fun j jMember => ?_
      rw [sum_eq_single_of_mem j jMember]
      · simp [entry, intervalIntegral.integral_const_mul, mode_integral, Complex.mul_conj']
      · intro k _ different
        have frequencyNonzero : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
        simp [entry, intervalIntegral.integral_const_mul, mode_integral, frequencyNonzero]

theorem periodic_mode_sum (limit : ℕ) (coefficient : ℕ → ℂ) :
    Function.Periodic (fun t => ∑ j ∈ range limit, coefficient j * mode (j : ℤ) t) 1 := by
  intro t
  refine sum_congr rfl fun j _ => ?_
  rw [periodic_mode]

theorem hasDerivAt_mode_sum (limit : ℕ) (coefficient : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (fun x => ∑ j ∈ range limit, coefficient j * mode (j : ℤ) x)
      (∑ j ∈ range limit, (coefficient j * frequency (j : ℤ)) * mode (j : ℤ) t) t := by
  apply HasDerivAt.fun_sum
  intro j _
  simpa only [mul_assoc] using (hasDerivAt_mode (j : ℤ) t).const_mul (coefficient j)

end
end DyadicMixedB4Fourier

end

section

open Finset MeasureTheory Set

namespace DyadicMixedB4Sampling

theorem sample_mul_length_le_integrals {f gradient : ℝ → ℝ} {a b centre : ℝ}
    (derivative : ∀ x, HasDerivAt f (gradient x) x) (gradientContinuous : Continuous gradient)
    (centreLower : a ≤ centre) (centreUpper : centre ≤ b) :
    (b - a) * f centre ≤ (∫ x in a..b, f x) + (b - a) * ∫ x in a..b, |gradient x| := by
  have fDifferentiable : Differentiable ℝ f := fun x => (derivative x).differentiableAt
  have fContinuous : Continuous f := fDifferentiable.continuous
  let variation : ℝ := ∫ x in a..b, |gradient x|
  have difference {x y : ℝ} (left : a ≤ x) (ordered : x ≤ y) (right : y ≤ b) :
      |f y - f x| ≤ variation := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => derivative z)
      (gradientContinuous.intervalIntegrable x y)]
    exact (intervalIntegral.abs_integral_le_integral_abs ordered).trans
      (intervalIntegral.integral_mono_interval left ordered right
        (Filter.Eventually.of_forall fun z => abs_nonneg (gradient z))
        (gradientContinuous.abs.intervalIntegrable a b))
  have pointwise (x : ℝ) (membership : x ∈ Icc a b) : f centre ≤ f x + variation := by
    have absoluteDifference : |f centre - f x| ≤ variation := by
      rcases le_total x centre with ordered | ordered
      · exact difference membership.1 ordered centreUpper
      · rw [abs_sub_comm]
        exact difference centreLower ordered membership.2
    linarith only [absoluteDifference, le_abs_self (f centre - f x)]
  have integrated := intervalIntegral.integral_mono_on (μ := volume) (centreLower.trans centreUpper)
    ((continuous_const : Continuous fun _ : ℝ => f centre).intervalIntegrable a b)
    ((fContinuous.add continuous_const).intervalIntegrable a b) pointwise
  change (∫ _ in a..b, f centre) ≤ (∫ x in a..b, f x + variation) at integrated
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (fContinuous.intervalIntegrable a b)
      ((continuous_const : Continuous fun _ : ℝ => variation).intervalIntegrable a b),
    intervalIntegral.integral_const] at integrated
  simpa only [variation, smul_eq_mul] using integrated

theorem separated_samples_le_integrals {f gradient : ℝ → ℝ} {a b radius : ℝ}
    (points : Finset ℝ) (ordered : a ≤ b) (radiusPositive : 0 < radius)
    (windowFits : ∀ x ∈ points, a ≤ x - radius ∧ x + radius ≤ b)
    (separated : (points : Set ℝ).Pairwise (fun x y => 2 * radius ≤ |x - y|))
    (fNonnegative : ∀ x, 0 ≤ f x) (derivative : ∀ x, HasDerivAt f (gradient x) x)
    (gradientContinuous : Continuous gradient) :
    (2 * radius) * (∑ x ∈ points, f x) ≤
      (∫ x in a..b, f x) + (2 * radius) * ∫ x in a..b, |gradient x| := by
  classical
  let window (x : ℝ) := Ioc (x - radius) (x + radius)
  have windowOrdered (x : ℝ) : x - radius ≤ x + radius := by linarith
  have disjoint : Set.Pairwise (points : Set ℝ) (fun x y => Disjoint (window x) (window y)) := by
    intro x xMember y yMember distinct
    rw [Set.disjoint_left]
    intro z inX inY
    have hx : x - radius < z ∧ z ≤ x + radius := inX
    have hy : y - radius < z ∧ z ≤ y + radius := inY
    have close : |x - y| < 2 * radius := by
      rw [abs_lt]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    exact (not_lt_of_ge (separated xMember yMember distinct)) close
  have unionFits : (⋃ x ∈ points, window x) ⊆ Ioc a b := by
    intro z membership
    obtain ⟨x, atPoint, inside⟩ := Set.mem_iUnion₂.mp membership
    obtain ⟨left, right⟩ := windowFits x atPoint
    exact Ioc_subset_Ioc left right inside
  have compare {g : ℝ → ℝ} (gContinuous : Continuous g) (gNonnegative : ∀ x, 0 ≤ g x) :
      (∑ x ∈ points, ∫ t in x - radius..x + radius, g t) ≤ ∫ t in a..b, g t := by
    calc
      _ = ∫ t in ⋃ x ∈ points, window x, g t := by
        rw [integral_biUnion_finset points (fun x _ => measurableSet_Ioc) disjoint
          (fun x _ => (gContinuous.intervalIntegrable (x - radius) (x + radius)).1)]
        exact sum_congr rfl fun x _ => intervalIntegral.integral_of_le (windowOrdered x)
      _ ≤ _ := by
        rw [intervalIntegral.integral_of_le ordered]
        exact setIntegral_mono_set (gContinuous.intervalIntegrable a b).1
          (Filter.Eventually.of_forall gNonnegative) unionFits.eventuallySubset
  have fDifferentiable : Differentiable ℝ f := fun x => (derivative x).differentiableAt
  have fContinuous : Continuous f := fDifferentiable.continuous
  calc
    _ = ∑ x ∈ points, (2 * radius) * f x := mul_sum points _ _
    _ ≤ ∑ x ∈ points, ((∫ t in x - radius..x + radius, f t) +
        (2 * radius) * (∫ t in x - radius..x + radius, |gradient t|)) := by
      refine sum_le_sum fun x _ => ?_
      have localInequality := sample_mul_length_le_integrals derivative gradientContinuous
        (by linarith : x - radius ≤ x) (by linarith : x ≤ x + radius)
      rwa [show x + radius - (x - radius) = 2 * radius by ring] at localInequality
    _ = (∑ x ∈ points, ∫ t in x - radius..x + radius, f t) +
        (2 * radius) * (∑ x ∈ points, ∫ t in x - radius..x + radius, |gradient t|) := by
      rw [sum_add_distrib, mul_sum]
    _ ≤ _ := add_le_add (compare fContinuous fNonnegative)
      (mul_le_mul_of_nonneg_left (compare gradientContinuous.abs fun t => abs_nonneg (gradient t))
        (by positivity))

end DyadicMixedB4Sampling

end

section

open Finset Set
open scoped RealInnerProductSpace

namespace DyadicMixedB4Fourier

noncomputable section

theorem integral_three_periods {f : ℝ → ℝ} (continuous : Continuous f)
    (periodic : Function.Periodic f 1) :
    (∫ t in (-1 : ℝ)..2, f t) = 3 * ∫ t in (0 : ℝ)..1, f t := by
  have shift (a b : ℝ) : (∫ t in a..b, f t) = ∫ t in a + 1..b + 1, f t := by
    calc
      _ = ∫ t in a..b, f (t + 1) := intervalIntegral.integral_congr fun t _ => (periodic t).symm
      _ = _ := intervalIntegral.integral_comp_add_right f 1
  have first : (∫ t in (-1 : ℝ)..0, f t) = ∫ t in (0 : ℝ)..1, f t := by
    convert shift (-1) 0 using 2 <;> norm_num
  have last : (∫ t in (0 : ℝ)..1, f t) = ∫ t in (1 : ℝ)..2, f t := by
    convert shift 0 1 using 2 <;> norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable (-1) 1)
      (continuous.intervalIntegrable 1 2),
    ← intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable (-1) 0)
      (continuous.intervalIntegrable 0 1), first, ← last]
  ring

theorem parseval_real (limit : ℕ) (coefficient : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) t‖ ^ 2) =
      ∑ j ∈ range limit, ‖coefficient j‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, ← intervalIntegral.integral_ofReal]
  exact parseval_finite_modes limit coefficient

theorem norm_frequency_nat (j : ℕ) : ‖frequency (j : ℤ)‖ = (j : ℝ) * (2 * Real.pi) := by
  rw [frequency, Int.cast_natCast, norm_mul, Complex.norm_natCast, norm_mul, Complex.norm_I,
    mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

theorem additive_large_sieve (limit : ℕ) (coefficient : ℕ → ℂ) (points : Finset ℝ)
    {radius : ℝ} (radiusPositive : 0 < radius) (radiusUpper : radius ≤ 1)
    (unitInterval : (points : Set ℝ) ⊆ Icc 0 1)
    (separated : (points : Set ℝ).Pairwise (fun x y => 2 * radius ≤ |x - y|)) :
    (∑ x ∈ points, ‖∑ j ∈ range limit, coefficient j * mode (j : ℤ) x‖ ^ 2) ≤
      (3 / (2 * radius) + 6 * (1 + 2 * Real.pi * limit)) *
        ∑ j ∈ range limit, ‖coefficient j‖ ^ 2 := by
  let polynomial (t : ℝ) := ∑ j ∈ range limit, coefficient j * mode (j : ℤ) t
  let derivativePolynomial (t : ℝ) :=
    ∑ j ∈ range limit, (coefficient j * frequency (j : ℤ)) * mode (j : ℤ) t
  let energy (t : ℝ) := ‖polynomial t‖ ^ 2
  let derivativeEnergy (t : ℝ) := ‖derivativePolynomial t‖ ^ 2
  let variation (t : ℝ) := 2 * ⟪polynomial t, derivativePolynomial t⟫
  let band : ℝ := 1 + 2 * Real.pi * limit
  let mass := ∑ j ∈ range limit, ‖coefficient j‖ ^ 2
  have bandPositive : 0 < band := by dsimp [band]; positivity
  have polynomialDerivative (t : ℝ) : HasDerivAt polynomial (derivativePolynomial t) t :=
    hasDerivAt_mode_sum limit coefficient t
  have energyDerivative (t : ℝ) : HasDerivAt energy (variation t) t :=
    (polynomialDerivative t).norm_sq
  have polynomialContinuous : Continuous polynomial :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_mode (j : ℤ))
  have derivativeContinuous : Continuous derivativePolynomial :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_mode (j : ℤ))
  have energyContinuous : Continuous energy := polynomialContinuous.norm.pow 2
  have derivativeEnergyContinuous : Continuous derivativeEnergy := derivativeContinuous.norm.pow 2
  have variationContinuous : Continuous variation :=
    continuous_const.mul (polynomialContinuous.inner derivativeContinuous)
  have polynomialPeriodic : Function.Periodic polynomial 1 := periodic_mode_sum limit coefficient
  have derivativePeriodic : Function.Periodic derivativePolynomial 1 := periodic_mode_sum limit _
  have energyPeriodic : Function.Periodic energy 1 := fun t => by
    unfold energy
    rw [polynomialPeriodic]
  have variationPeriodic : Function.Periodic (fun t => |variation t|) 1 := fun t => by
    change |variation (t + 1)| = |variation t|
    dsimp only [variation]
    rw [polynomialPeriodic, derivativePeriodic]
  have energyIntegral : (∫ t in (0 : ℝ)..1, energy t) = mass := parseval_real limit coefficient
  have derivativeIntegral : (∫ t in (0 : ℝ)..1, derivativeEnergy t) ≤ band ^ 2 * mass := by
    change (∫ t in (0 : ℝ)..1,
      ‖∑ j ∈ range limit, (coefficient j * frequency (j : ℤ)) * mode (j : ℤ) t‖ ^ 2) ≤ _
    rw [parseval_real]
    unfold mass
    rw [mul_sum]
    refine sum_le_sum fun j member => ?_
    have jBound : (j : ℝ) ≤ limit := by exact_mod_cast (mem_range.mp member).le
    have frequencyBound : ‖frequency (j : ℤ)‖ ≤ band := by
      rw [norm_frequency_nat]
      dsimp [band]
      nlinarith [mul_nonneg (sub_nonneg.mpr jBound) Real.pi_pos.le]
    calc
      _ = ‖frequency (j : ℤ)‖ ^ 2 * ‖coefficient j‖ ^ 2 := by rw [norm_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) frequencyBound 2) (sq_nonneg _)
  have pointwise (t : ℝ) : |variation t| ≤ band * energy t + band⁻¹ * derivativeEnergy t := by
    have quadratic : 2 * ‖polynomial t‖ * ‖derivativePolynomial t‖ ≤
        band * energy t + band⁻¹ * derivativeEnergy t := by
      have square := sq_nonneg (band * ‖polynomial t‖ - ‖derivativePolynomial t‖)
      have multiplied :
          (2 * ‖polynomial t‖ * ‖derivativePolynomial t‖ - band * energy t) * band ≤
            derivativeEnergy t := by
        dsimp [energy, derivativeEnergy]
        nlinarith only [square]
      have divided := (le_div_iff₀ bandPositive).mpr multiplied
      rw [inv_mul_eq_div]
      linarith only [divided]
    calc
      _ ≤ 2 * ‖polynomial t‖ * ‖derivativePolynomial t‖ := by
        unfold variation
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ _ := quadratic
  have variationIntegral : (∫ t in (0 : ℝ)..1, |variation t|) ≤ 2 * band * mass := by
    have scaledEnergy : IntervalIntegrable (fun t => band * energy t)
        MeasureTheory.volume 0 1 := (continuous_const.mul energyContinuous).intervalIntegrable 0 1
    have scaledDerivative : IntervalIntegrable (fun t => band⁻¹ * derivativeEnergy t)
        MeasureTheory.volume 0 1 := (continuous_const.mul derivativeEnergyContinuous).intervalIntegrable 0 1
    have integrated := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (by norm_num : (0 : ℝ) ≤ 1)
      (variationContinuous.abs.intervalIntegrable 0 1)
      (((continuous_const.mul energyContinuous).add
        (continuous_const.mul derivativeEnergyContinuous)).intervalIntegrable 0 1)
      (fun t _ => pointwise t)
    calc
      _ ≤ ∫ t in (0 : ℝ)..1, band * energy t + band⁻¹ * derivativeEnergy t := integrated
      _ = band * mass + band⁻¹ * ∫ t in (0 : ℝ)..1, derivativeEnergy t := by
        rw [intervalIntegral.integral_add scaledEnergy scaledDerivative,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, energyIntegral]
      _ ≤ band * mass + band⁻¹ * (band ^ 2 * mass) :=
        (add_le_add_right (mul_le_mul_of_nonneg_left derivativeIntegral (inv_nonneg.mpr bandPositive.le)) _)
      _ = _ := by field_simp [bandPositive.ne']; ring
  have windowFits (t : ℝ) (member : t ∈ points) : -1 ≤ t - radius ∧ t + radius ≤ 2 := by
    obtain ⟨lower, upper⟩ := unitInterval member
    constructor <;> linarith
  have samples := DyadicMixedB4Sampling.separated_samples_le_integrals points
    (by norm_num : (-1 : ℝ) ≤ 2) radiusPositive windowFits separated
    (fun t => sq_nonneg ‖polynomial t‖) energyDerivative variationContinuous
  rw [integral_three_periods energyContinuous energyPeriodic, energyIntegral,
    integral_three_periods variationContinuous.abs variationPeriodic] at samples
  change (∑ t ∈ points, energy t) ≤ (3 / (2 * radius) + 6 * band) * mass
  have multiplied : (∑ t ∈ points, energy t) * (2 * radius) ≤
      3 * mass + (2 * radius) * (3 * (2 * band * mass)) := by
    rw [mul_comm]
    exact samples.trans (by gcongr)
  calc
    _ ≤ (3 * mass + (2 * radius) * (3 * (2 * band * mass))) / (2 * radius) :=
      (le_div_iff₀ (by positivity)).mpr multiplied
    _ = _ := by field_simp [radiusPositive.ne']; ring

end
end DyadicMixedB4Fourier

end

section

namespace BombieriVinogradov.LargeSieve

/-- A nonzero rational with denominator at most `D` has absolute value at least `1 / D`. -/
theorem ratAbsLowerBound {D : Nat} (hD : 0 < D) {z : Rat}
    (hzden : z.den <= D) (hz : Ne z 0) :
    (1 : Real) / (D : Real) <= |(z : Real)| := by
  have hnumNat : 1 <= z.num.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hz))
  have hnum : (1 : Real) <= |(z.num : Real)| := by
    calc
      (1 : Real) <= (z.num.natAbs : Real) := by exact_mod_cast hnumNat
      _ = |(z.num : Real)| := by simp
  have hDReal : 0 < (D : Real) := by exact_mod_cast hD
  have hdenReal : 0 < (z.den : Real) := by exact_mod_cast z.den_pos
  have hrecip : (1 : Real) / (D : Real) <= 1 / (z.den : Real) := by
    gcongr
  calc
    (1 : Real) / (D : Real) <= 1 / (z.den : Real) := hrecip
    _ <= |(z.num : Real)| / (z.den : Real) := by gcongr
    _ = |(z : Real)| := by
      rw [Rat.cast_def, abs_div, abs_of_pos hdenReal]

/-- Distinct rationals with denominators at most `Q` are at least `1 / Q^2` apart. -/
theorem ratAbsSubLowerBound {Q : Nat} (hQ : 0 < Q) {x y : Rat}
    (hx : x.den <= Q) (hy : y.den <= Q) (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= |(x : Real) - (y : Real)| := by
  let z : Rat := x - y
  have hz : Ne z 0 := sub_ne_zero.mpr hxy
  have hden : z.den <= x.den * y.den :=
    Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.sub_den_dvd x y)
  have hdenQ : z.den <= Q ^ 2 := by
    calc
      z.den <= x.den * y.den := hden
      _ <= Q * Q := Nat.mul_le_mul hx hy
      _ = Q ^ 2 := by ring
  simpa [z, Nat.cast_pow] using
    ratAbsLowerBound (D := Q ^ 2) (Nat.pow_pos hQ) hdenQ hz

/-- Circular distance between representatives in the half-open interval `[0, 1)`. -/
def ratCircleDistance (x y : Rat) : Real :=
  min |(x : Real) - (y : Real)| (1 - |(x : Real) - (y : Real)|)

/-- Farey-type rationals in `[0, 1)` remain `1 / Q^2` apart around the circle. -/
theorem ratCircleSeparation {Q : Nat} (hQ : 0 < Q) {x y : Rat}
    (hx0 : 0 <= x) (hx1 : x < 1) (hy0 : 0 <= y) (hy1 : y < 1)
    (hxden : x.den <= Q) (hyden : y.den <= Q) (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= ratCircleDistance x y := by
  have hlinear := ratAbsSubLowerBound hQ hxden hyden hxy
  have hsub_lt_one : |x - y| < (1 : Rat) := by
    rw [abs_lt]
    constructor <;> linarith
  let w : Rat := 1 - |x - y|
  have hwpos : 0 < w := sub_pos.mpr hsub_lt_one
  have hwden : w.den <= Q ^ 2 := by
    have hxyden : (x - y).den <= Q ^ 2 := by
      apply Nat.le_trans
      · exact Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.sub_den_dvd x y)
      · simpa [pow_two] using Nat.mul_le_mul hxden hyden
    simpa [w] using hxyden
  have hcircular : (1 : Real) / (Q : Real) ^ 2 <= |(w : Real)| := by
    simpa only [Nat.cast_pow] using
      ratAbsLowerBound (D := Q ^ 2) (Nat.pow_pos hQ) hwden hwpos.ne'
  have hwcast : |(w : Real)| = 1 - |(x : Real) - (y : Real)| := by
    rw [abs_of_pos]
    · simp [w]
    · exact_mod_cast hwpos
  rw [ratCircleDistance, le_min_iff]
  exact And.intro hlinear (hwcast ▸ hcircular)

end BombieriVinogradov.LargeSieve

namespace BombieriVinogradov.LargeSieve

/-- The reduced rational representative of a unit modulo `q`. -/
def unitFraction {q : Nat} (a : (ZMod q)ˣ) : Rat :=
  (a.val.val : Rat) / (q : Rat)

/-- A unit representative is coprime to its modulus. -/
theorem unitFraction_coprime {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    Nat.Coprime a.val.val q := by
  rw [← ZMod.isUnit_iff_coprime]
  simpa only [ZMod.natCast_zmod_val] using a.isUnit

/-- The reduced denominator of `unitFraction a` is exactly the modulus. -/
theorem unitFraction_den {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    (unitFraction a).den = q := by
  have hqInt : (0 : Int) < q := by exact_mod_cast NeZero.pos q
  have hcInt : Nat.Coprime (a.val.val : Int).natAbs (q : Int).natAbs := by
    change Nat.Coprime a.val.val q
    exact unitFraction_coprime a
  have hden : ((unitFraction a).den : Int) = (q : Int) := by
    simpa [unitFraction] using Rat.den_div_eq_of_coprime hqInt hcInt
  exact Int.ofNat_inj.mp hden

/-- The reduced numerator of `unitFraction a` is the standard unit representative. -/
theorem unitFraction_num {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    (unitFraction a).num = (a.val.val : Int) := by
  have hqInt : (0 : Int) < q := by exact_mod_cast NeZero.pos q
  have hcInt : Nat.Coprime (a.val.val : Int).natAbs (q : Int).natAbs := by
    change Nat.Coprime a.val.val q
    exact unitFraction_coprime a
  simpa [unitFraction] using Rat.num_div_eq_of_coprime hqInt hcInt

/-- The finite dependent index of reduced fractions with denominator at most `Q`. -/
abbrev FareyIndex (Q : Nat) :=
  Sigma fun q : {q : Nat // q ∈ Finset.Icc 1 Q} => (ZMod q.1)ˣ

/-- The rational value represented by a Farey index. -/
def fareyValue {Q : Nat} (i : FareyIndex Q) : Rat :=
  unitFraction i.2

theorem fareyValue_den {Q : Nat} (i : FareyIndex Q) :
    (fareyValue i).den = i.1.1 := by
  let _ : NeZero i.1.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp i.1.2).1⟩
  exact unitFraction_den i.2

theorem fareyValue_nonneg {Q : Nat} (i : FareyIndex Q) :
    0 <= fareyValue i := by
  unfold fareyValue unitFraction
  positivity

theorem fareyValue_lt_one {Q : Nat} (i : FareyIndex Q) :
    fareyValue i < 1 := by
  let _ : NeZero i.1.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp i.1.2).1⟩
  unfold fareyValue unitFraction
  rw [div_lt_one]
  · exact_mod_cast ZMod.val_lt i.2.val
  · exact_mod_cast NeZero.pos i.1.1

/-- Reduced Farey indices have unique rational values. -/
theorem fareyValue_injective (Q : Nat) :
    Function.Injective (fareyValue (Q := Q)) := by
  intro x y hxy
  have hxpos : 0 < x.1.1 := (Finset.mem_Icc.mp x.1.2).1
  have hypos : 0 < y.1.1 := (Finset.mem_Icc.mp y.1.2).1
  let _ : NeZero x.1.1 := ⟨hxpos.ne'⟩
  let _ : NeZero y.1.1 := ⟨hypos.ne'⟩
  have hq : x.1.1 = y.1.1 := by
    calc
      x.1.1 = (fareyValue x).den := (fareyValue_den x).symm
      _ = (fareyValue y).den := congrArg Rat.den hxy
      _ = y.1.1 := fareyValue_den y
  cases x with
  | mk q a =>
      cases y with
      | mk r b =>
          simp only at hq
          have hqr : q = r := Subtype.ext hq
          subst r
          have hnum : (a.val.val : Int) = (b.val.val : Int) := by
            calc
              (a.val.val : Int) = (unitFraction a).num := (unitFraction_num a).symm
              _ = (unitFraction b).num := congrArg Rat.num hxy
              _ = (b.val.val : Int) := unitFraction_num b
          have habNat : a.val.val = b.val.val := Int.ofNat_inj.mp hnum
          have habZMod : a.val = b.val := ZMod.val_injective q.1 habNat
          have hab : a = b := Units.ext habZMod
          subst b
          rfl

/-- Distinct reduced Farey points are separated by at least `1 / Q^2` on the circle. -/
theorem fareyValue_circle_separation {Q : Nat} (hQ : 0 < Q)
    {x y : FareyIndex Q} (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= ratCircleDistance (fareyValue x) (fareyValue y) := by
  apply ratCircleSeparation hQ
  · exact fareyValue_nonneg x
  · exact fareyValue_lt_one x
  · exact fareyValue_nonneg y
  · exact fareyValue_lt_one y
  · rw [fareyValue_den]
    exact (Finset.mem_Icc.mp x.1.2).2
  · rw [fareyValue_den]
    exact (Finset.mem_Icc.mp y.1.2).2
  · intro hvalue
    exact hxy (fareyValue_injective Q hvalue)

end BombieriVinogradov.LargeSieve

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

/-- The finite set of primitive complex Dirichlet characters of level `q`. -/
def primitiveCharacters (q : Nat) : Finset (DirichletCharacter Complex q) := by
  classical
  exact Finset.univ.filter DirichletCharacter.IsPrimitive

/-- The interval character sum `S(chi)` in Vaughan's Theorem 4. -/
def intervalCharacterSum (a : Int -> Complex) (M : Int) (N q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ n ∈ Ioc M (M + (N : Int)), a n * chi (n : ZMod q)

/-- A character transform of a function on the unit group of `ZMod q`. -/
def unitCharacterSum {q : Nat} (a : (ZMod q)ˣ -> Complex)
    (chi : DirichletCharacter Complex q) : Complex := by
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  exact ∑ x, a x * chi (x : ZMod q)

end BombieriVinogradov.LargeSieve

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.LargeSieve

noncomputable local instance unitFintype (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- A nonnegative sum over primitive characters is bounded by the sum over all characters. -/
theorem primitiveSum_le_all (q : Nat) (f : DirichletCharacter Complex q -> Real)
    (hf : ∀ chi, 0 <= f chi) :
    ∑ chi ∈ primitiveCharacters q, f chi <= ∑ chi, f chi := by
  classical
  exact Finset.sum_le_univ_sum_of_nonneg (s := primitiveCharacters q) hf

/-- On units, complex conjugation of a character value is evaluation at the inverse. -/
theorem star_character_apply_unit {q : Nat} (chi : DirichletCharacter Complex q)
    (x : (ZMod q)ˣ) :
    star (chi (x : ZMod q)) = chi ((x : ZMod q)⁻¹) := by
  rw [MulChar.star_apply']
  rw [MulChar.inv_apply_eq_inv']
  simp

/-- Orthogonality of all complex Dirichlet characters on the unit group. -/
theorem characterOrthogonalityOnUnits {q : Nat} [NeZero q]
    (x y : (ZMod q)ˣ) :
    (∑ chi : DirichletCharacter Complex q,
        star (chi (x : ZMod q)) * chi (y : ZMod q)) =
      if x = y then (q.totient : Complex) else 0 := by
  simp_rw [star_character_apply_unit]
  simpa only [Units.val_inj] using
    (DirichletCharacter.sum_char_inv_mul_char_eq (R := Complex)
      x.isUnit (y : ZMod q))

/-- Finite Parseval identity for the Dirichlet-character transform on `(ZMod q)^*`. -/
theorem characterParseval {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    (∑ chi : DirichletCharacter Complex q,
        star (unitCharacterSum a chi) * unitCharacterSum a chi) =
      (q.totient : Complex) * ∑ x, star (a x) * a x := by
  classical
  unfold unitCharacterSum
  simp_rw [star_sum, star_mul, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, y]
    rw [Finset.sum_comm]
  have rearrange (chi : DirichletCharacter Complex q) (x y : (ZMod q)ˣ) :
      star (chi (x : ZMod q)) * star (a x) *
          (a y * chi (y : ZMod q)) =
        (star (a x) * a y) *
          (star (chi (x : ZMod q)) * chi (y : ZMod q)) := by
    ring
  simp_rw [rearrange]
  simp_rw [← Finset.mul_sum]
  simp_rw [characterOrthogonalityOnUnits]
  simp [mul_ite]
  rw [← Finset.sum_mul]
  ring

/-- Real norm-squared form of character Parseval, ready for analytic inequalities. -/
theorem characterParseval_normSq {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    (∑ chi : DirichletCharacter Complex q, ‖unitCharacterSum a chi‖ ^ 2) =
      (q.totient : Real) * ∑ x, ‖a x‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp_rw [← Complex.normSq_eq_norm_sq]
  push_cast
  simpa only [Complex.normSq_eq_conj_mul_self, RCLike.star_def] using
    (characterParseval a)

/--
Discarding imprimitive characters gives the fixed-modulus primitive-character
bound that feeds the large-sieve argument.
-/
theorem primitiveCharacterParseval_le {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum a chi‖ ^ 2 <=
      (q.totient : Real) * ∑ x, ‖a x‖ ^ 2 := by
  calc
    _ <= ∑ chi : DirichletCharacter Complex q,
        ‖unitCharacterSum a chi‖ ^ 2 :=
      primitiveSum_le_all q _ (fun chi => sq_nonneg ‖unitCharacterSum a chi‖)
    _ = _ := characterParseval_normSq a

end BombieriVinogradov.LargeSieve

end

section

open Complex Finset Real

namespace BombieriVinogradov.LargeSieve

noncomputable section

noncomputable local instance fareyUnitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

def additivePhase (x : ℝ) : ℂ := circleMap 0 1 (2 * Real.pi * x)

theorem additivePhase_add (x y : ℝ) : additivePhase (x + y) = additivePhase x * additivePhase y := by
  dsimp [additivePhase]
  rw [circleMap_zero_mul, one_mul, mul_add]

theorem norm_additivePhase (x : ℝ) : ‖additivePhase x‖ = 1 := by
  simp [additivePhase, norm_circleMap_zero]

def fareyIndices (Q : ℕ) : Finset (FareyIndex Q) :=
  (Icc 1 Q).attach.sigma fun _ => Finset.univ

def fareyAdditiveSample {Q : ℕ} (a : ℕ → ℂ) (N : ℕ) (i : FareyIndex Q) : ℂ :=
  ∑ n ∈ range N, a n * additivePhase ((n : ℝ) * (fareyValue i : ℝ))

theorem mode_nat_additivePhase (n : ℕ) (t : ℝ) :
    DyadicMixedB4Fourier.mode (n : ℤ) t = additivePhase ((n : ℝ) * t) := by
  rw [DyadicMixedB4Fourier.mode, DyadicMixedB4Fourier.frequency, additivePhase, circleMap_zero]
  simp only [Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  ring

theorem norm_gaussSum_stdAddChar_sq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (primitive : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
  rw [DirichletCharacter.norm_gaussSum_stdAddChar primitive, Real.sq_sqrt (Nat.cast_nonneg q)]

theorem additiveLargeSieve {Q N : ℕ} (QPositive : 0 < Q) (a : ℕ → ℂ) :
    ∑ i ∈ fareyIndices Q, ‖fareyAdditiveSample a N i‖ ^ 2 ≤
      64 * ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ range N, ‖a k‖ ^ 2 := by
  classical
  let realFarey : FareyIndex Q ↪ ℝ :=
    ⟨fun i => fareyValue i, fun _ _ equal => fareyValue_injective Q (Rat.cast_injective equal)⟩
  let points := (fareyIndices Q).map realFarey
  let radius : ℝ := 1 / (2 * (Q : ℝ) ^ 2)
  have QCast : (0 : ℝ) < Q := by exact_mod_cast QPositive
  have QOne : (1 : ℝ) ≤ Q := by exact_mod_cast QPositive
  have QSquared : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := one_le_pow₀ QOne
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  have radiusUpper : radius ≤ 1 := by
    dsimp [radius]
    apply (div_le_one (by positivity)).mpr
    linarith
  have radiusDouble : 2 * radius = 1 / (Q : ℝ) ^ 2 := by
    dsimp [radius]
    field_simp [QCast.ne']
  have contained : (points : Set ℝ) ⊆ Set.Icc 0 1 := by
    intro t member
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp member
    change (fareyValue i : ℝ) ∈ Set.Icc 0 1
    constructor
    · exact_mod_cast fareyValue_nonneg i
    · exact_mod_cast (fareyValue_lt_one i).le
  have separated : (points : Set ℝ).Pairwise (fun x y => 2 * radius ≤ |x - y|) := by
    intro x xMember y yMember different
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp xMember
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp yMember
    rw [radiusDouble]
    have indexDifferent : i ≠ j := fun equal => different (congrArg realFarey equal)
    exact (fareyValue_circle_separation QPositive indexDifferent).trans (min_le_left _ _)
  have bound := DyadicMixedB4Fourier.additive_large_sieve N a points radiusPositive radiusUpper
    contained separated
  rw [show 3 / (2 * radius) = 3 * (Q : ℝ) ^ 2 by rw [radiusDouble]; field_simp [QCast.ne']] at bound
  dsimp only [points] at bound
  rw [Finset.sum_map] at bound
  simp_rw [mode_nat_additivePhase] at bound
  change (∑ i ∈ fareyIndices Q, ‖fareyAdditiveSample a N i‖ ^ 2) ≤ _ at bound
  refine bound.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _))
  nlinarith only [QSquared, Nat.cast_nonneg (α := ℝ) N,
    mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) (Nat.cast_nonneg (α := ℝ) N)]

end
end BombieriVinogradov.LargeSieve

end

section

noncomputable section

open Complex Finset Real
open scoped BigOperators ComplexConjugate

namespace BombieriVinogradov.LargeSieve

noncomputable local instance characterReductionUnitFintype
    (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _

/-- The real additive phase at an integral multiple of a reduced fraction is
Mathlib's standard additive character on the corresponding residue. -/
theorem additivePhase_int_unitFraction {q : Nat} [NeZero q]
    (n : Int) (u : (ZMod q)ˣ) :
    additivePhase ((n : Real) * (unitFraction u : Real)) =
      ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) := by
  rw [show (n : ZMod q) * (u : ZMod q) =
    (n * u.val.val : Int) by norm_num]
  rw [ZMod.stdAddChar_coe]
  rw [additivePhase, circleMap_zero]
  unfold unitFraction
  push_cast
  field_simp [NeZero.ne q]

/-- A Dirichlet-character-weighted sum over units equals the corresponding
sum over all residues, since character values vanish on nonunits. -/
theorem sum_units_eq_sum_residues {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (f : ZMod q -> Complex) :
    ∑ u : (ZMod q)ˣ, chi (u : ZMod q) * f u =
      ∑ x : ZMod q, chi x * f x := by
  classical
  let s : Finset (ZMod q) := Finset.univ.filter IsUnit
  have hunits : (∑ u : (ZMod q)ˣ, chi (u : ZMod q) * f u) =
      ∑ x ∈ s, chi x * f x := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (ZMod q)ˣ))
      (t := s) (fun u hu => (u : ZMod q))
    · intro u hu
      simp [s, u.isUnit]
    · intro u hu v hv huv
      exact Units.ext huv
    · intro x hx
      have hxunit : IsUnit x := by simpa [s] using hx
      exact ⟨hxunit.unit, Finset.mem_univ _, hxunit.unit_spec⟩
    · intro u hu
      rfl
  rw [hunits]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hxuniv hxnot
  have hxnonunit : ¬IsUnit x := by simpa [s] using hxnot
  rw [MulChar.map_nonunit chi hxnonunit, zero_mul]

/-- The additive interval sum at one reduced residue modulo `q`. -/
def intervalAdditiveResidueSum (a : Int -> Complex) (M : Int) (N q : Nat)
    [NeZero q] (u : (ZMod q)ˣ) : Complex :=
  ∑ n ∈ Ioc M (M + (N : Int)),
    a n * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))

/-- Primitive Gauss-sum inversion converts one multiplicative character sum
to a character transform of additive interval samples. -/
theorem gauss_mul_intervalCharacterSum {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi)
    (a : Int -> Complex) (M : Int) (N : Nat) :
    gaussSum chi⁻¹ ZMod.stdAddChar * intervalCharacterSum a M N q chi =
      unitCharacterSum (intervalAdditiveResidueSum a M N q) chi⁻¹ := by
  classical
  have hchiInv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hchi
  have hshift (n : Int) :
      ∑ u : (ZMod q)ˣ,
          chi⁻¹ (u : ZMod q) *
            ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) =
        chi (n : ZMod q) * gaussSum chi⁻¹ ZMod.stdAddChar := by
    calc
      _ = ∑ x : ZMod q,
          chi⁻¹ x * ZMod.stdAddChar ((n : ZMod q) * x) :=
        sum_units_eq_sum_residues chi⁻¹ _
      _ = gaussSum chi⁻¹ (ZMod.stdAddChar.mulShift (n : ZMod q)) := by
        simp only [gaussSum, AddChar.mulShift_apply]
      _ = _ := by
        simpa using
          (gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hchiInv (n : ZMod q))
  unfold intervalCharacterSum unitCharacterSum intervalAdditiveResidueSum
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    gaussSum chi⁻¹ ZMod.stdAddChar * (a n * chi (n : ZMod q)) =
        a n * (chi (n : ZMod q) * gaussSum chi⁻¹ ZMod.stdAddChar) := by ring
    _ = a n * ∑ u : (ZMod q)ˣ,
        chi⁻¹ (u : ZMod q) * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) := by
      rw [hshift n]
    _ = ∑ u : (ZMod q)ˣ,
        a n * (chi⁻¹ (u : ZMod q) *
          ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))) := by
      rw [Finset.mul_sum]
    _ = ∑ u : (ZMod q)ˣ,
        a n * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) *
          chi⁻¹ (u : ZMod q) := by
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- Squared-norm form of primitive Gauss-sum inversion. -/
theorem q_mul_norm_intervalCharacterSum_sq {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi)
    (a : Int -> Complex) (M : Int) (N : Nat) :
    (q : Real) * ‖intervalCharacterSum a M N q chi‖ ^ 2 =
      ‖unitCharacterSum (intervalAdditiveResidueSum a M N q) chi⁻¹‖ ^ 2 := by
  have hchiInv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hchi
  calc
    (q : Real) * ‖intervalCharacterSum a M N q chi‖ ^ 2 =
        ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ ^ 2 *
          ‖intervalCharacterSum a M N q chi‖ ^ 2 := by
      rw [norm_gaussSum_stdAddChar_sq hchiInv]
    _ = ‖gaussSum chi⁻¹ ZMod.stdAddChar * intervalCharacterSum a M N q chi‖ ^ 2 := by
      rw [norm_mul]
      ring
    _ = _ := by
      rw [gauss_mul_intervalCharacterSum hchi a M N]

/-- Inversion permutes the finite set of primitive characters. -/
theorem sum_primitive_inv (q : Nat) (f : DirichletCharacter Complex q -> Real) :
    ∑ chi ∈ primitiveCharacters q, f chi⁻¹ =
      ∑ chi ∈ primitiveCharacters q, f chi := by
  classical
  apply Finset.sum_bij (s := primitiveCharacters q) (t := primitiveCharacters q)
    (fun chi hchi => chi⁻¹)
  · intro chi hchi
    have hprimitive : DirichletCharacter.IsPrimitive chi := by
      simpa [primitiveCharacters] using hchi
    have hinv : DirichletCharacter.IsPrimitive chi⁻¹ := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
      exact hprimitive
    simpa [primitiveCharacters] using hinv
  · intro chi hchi psi hpsi heq
    simpa only [inv_inv] using congrArg Inv.inv heq
  · intro psi hpsi
    refine ⟨psi⁻¹, ?_, ?_⟩
    · have hprimitive : DirichletCharacter.IsPrimitive psi := by
        simpa [primitiveCharacters] using hpsi
      have hinv : DirichletCharacter.IsPrimitive psi⁻¹ := by
        rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
        exact hprimitive
      simpa [primitiveCharacters] using hinv
    · simp
  · intro chi hchi
    rfl

/-- At a fixed positive modulus, the source weight `q / phi(q)` cancels
exactly against the Gauss norm and character Parseval constants. -/
theorem weightedPrimitiveCharacterSum_le_additive {q : Nat} [NeZero q]
    (a : Int -> Complex) (M : Int) (N : Nat) :
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
      ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2 := by
  classical
  let b : (ZMod q)ˣ -> Complex := intervalAdditiveResidueSum a M N q
  let S : Real := ∑ chi ∈ primitiveCharacters q,
    ‖intervalCharacterSum a M N q chi‖ ^ 2
  let E : Real := ∑ u : (ZMod q)ˣ, ‖b u‖ ^ 2
  have hscaled : (q : Real) * S =
      ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi⁻¹‖ ^ 2 := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have hprimitive : DirichletCharacter.IsPrimitive chi := by
      simpa [primitiveCharacters] using hchi
    exact q_mul_norm_intervalCharacterSum_sq hprimitive a M N
  have hinv :
      (∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi⁻¹‖ ^ 2) =
        ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi‖ ^ 2 := by
    exact sum_primitive_inv q (fun chi => ‖unitCharacterSum b chi‖ ^ 2)
  have hparseval :
      ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi‖ ^ 2 <=
        (q.totient : Real) * E := by
    simpa [E] using primitiveCharacterParseval_le b
  have hcore : (q : Real) * S <= (q.totient : Real) * E := by
    rw [hscaled, hinv]
    exact hparseval
  have hphi : 0 < (q.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  change ((q : Real) / (q.totient : Real)) * S <= E
  calc
    ((q : Real) / (q.totient : Real)) * S =
        ((q : Real) * S) / (q.totient : Real) := by ring
    _ <= ((q.totient : Real) * E) / (q.totient : Real) := by
      exact (div_le_div_iff_of_pos_right hphi).2 hcore
    _ = E := by field_simp

/-- Reindex an integer interval of length `N` by `range N`. -/
theorem sum_int_Ioc_eq_sum_range {R : Type*} [AddCommMonoid R]
    (f : Int -> R) (M : Int) (N : Nat) :
    ∑ n ∈ Ioc M (M + (N : Int)), f n =
      ∑ k ∈ range N, f (M + (k : Int) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hle : M <= M + (N : Int) := by omega
      rw [Nat.cast_succ]
      rw [← add_assoc]
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hle]
      rw [Finset.sum_insert]
      · rw [Finset.sum_range_succ, ih]
        simp [add_comm, add_assoc]
      · simp

/-- Coefficients on `M < n <= M + N`, shifted to indices `0 <= k < N`. -/
def shiftedIntervalCoefficients (a : Int -> Complex) (M : Int) (k : Nat) : Complex :=
  a (M + (k : Int) + 1)

/-- Translation of an additive interval sum produces only a unit-norm common
phase, followed by the Farey sample of the shifted coefficients. -/
theorem intervalAdditiveResidueSum_eq_phase_mul_fareySample
    {Q q : Nat} [NeZero q] (hq : q ∈ Icc 1 Q)
    (a : Int -> Complex) (M : Int) (N : Nat) (u : (ZMod q)ˣ) :
    intervalAdditiveResidueSum a M N q u =
      additivePhase (((M + 1 : Int) : Real) * (unitFraction u : Real)) *
        fareyAdditiveSample (shiftedIntervalCoefficients a M) N ⟨⟨q, hq⟩, u⟩ := by
  rw [intervalAdditiveResidueSum, sum_int_Ioc_eq_sum_range]
  unfold fareyAdditiveSample shiftedIntervalCoefficients fareyValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← additivePhase_int_unitFraction (M + (k : Int) + 1) u]
  rw [show (((M + (k : Int) + 1 : Int) : Real) * (unitFraction u : Real)) =
      (((M + 1 : Int) : Real) * (unitFraction u : Real)) +
        ((k : Real) * (unitFraction u : Real)) by
    push_cast
    ring]
  rw [additivePhase_add]
  ring

/-- Norm form of interval translation, ready for the additive large sieve. -/
theorem norm_intervalAdditiveResidueSum_eq_fareySample
    {Q q : Nat} [NeZero q] (hq : q ∈ Icc 1 Q)
    (a : Int -> Complex) (M : Int) (N : Nat) (u : (ZMod q)ˣ) :
    ‖intervalAdditiveResidueSum a M N q u‖ =
      ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N ⟨⟨q, hq⟩, u⟩‖ := by
  rw [intervalAdditiveResidueSum_eq_phase_mul_fareySample hq a M N u]
  rw [norm_mul, norm_additivePhase, one_mul]

/-- Expand a sum over the explicit dependent Farey index into moduli and
units. -/
theorem sum_fareyIndices_eq_sum_attach {Q : Nat} (f : FareyIndex Q -> Real) :
    ∑ i ∈ fareyIndices Q, f i =
      ∑ q ∈ (Icc 1 Q).attach, ∑ u : (ZMod q.1)ˣ, f ⟨q, u⟩ := by
  unfold fareyIndices
  rw [Finset.sum_sigma]

/-- Total additive energy at one modulus, defined as zero at the unused
modulus `q = 0`. -/
def modulusAdditiveEnergy (a : Int -> Complex) (M : Int) (N q : Nat) : Real :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2

theorem modulusAdditiveEnergy_eq {q : Nat} [NeZero q]
    (a : Int -> Complex) (M : Int) (N : Nat) :
    modulusAdditiveEnergy a M N q =
      ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2 := by
  simp [modulusAdditiveEnergy, NeZero.ne q]

/-- The sum of fixed-modulus additive energies is exactly the Farey energy of
the shifted coefficient sequence. -/
theorem sum_modulusAdditiveEnergy_eq_fareySamples
    (Q : Nat) (a : Int -> Complex) (M : Int) (N : Nat) :
    ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q =
      ∑ i ∈ fareyIndices Q,
        ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N i‖ ^ 2 := by
  rw [sum_fareyIndices_eq_sum_attach]
  rw [← Finset.sum_attach (Icc 1 Q) (modulusAdditiveEnergy a M N)]
  apply Finset.sum_congr rfl
  intro q hqattach
  let _ : NeZero q.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp q.2).1⟩
  rw [modulusAdditiveEnergy_eq]
  apply Finset.sum_congr rfl
  intro u hu
  rw [norm_intervalAdditiveResidueSum_eq_fareySample q.2 a M N u]

/-- The primitive Dirichlet-character large sieve with explicit constant
`64`, including arbitrary integer interval origin. -/
theorem characterLargeSieveNat (M : Int) (N Q : Nat) (a : Int -> Complex)
    (hQ : 1 <= Q) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
      64 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2 := by
  by_cases hNzero : N = 0
  · subst N
    simp [intervalCharacterSum]
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQ
  have hfixed :
      (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            ‖intervalCharacterSum a M N q chi‖ ^ 2) <=
        ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q := by
    apply Finset.sum_le_sum
    intro q hq
    let _ : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
    rw [modulusAdditiveEnergy_eq]
    exact weightedPrimitiveCharacterSum_le_additive a M N
  calc
    _ <= ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q := hfixed
    _ = ∑ i ∈ fareyIndices Q,
        ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N i‖ ^ 2 :=
      sum_modulusAdditiveEnergy_eq_fareySamples Q a M N
    _ <= 64 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ k ∈ range N, ‖shiftedIntervalCoefficients a M k‖ ^ 2 :=
      additiveLargeSieve hQpos (shiftedIntervalCoefficients a M)
    _ = 64 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2 := by
      rw [sum_int_Ioc_eq_sum_range (fun n => ‖a n‖ ^ 2) M N]
      rfl

end BombieriVinogradov.LargeSieve

end

section

open Finset
open scoped Classical

namespace DyadicMixedB4DualCharacter

noncomputable section

theorem character_pair_orthogonality {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) :
    (∑ x : ZMod q, χ x * star (ψ x)) = if χ = ψ then (q.totient : ℂ) else 0 := by
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  simp_rw [MulChar.star_apply', ← MulChar.mul_apply]
  by_cases same : χ = ψ
  · subst ψ
    simp only [mul_inv_cancel, ite_true]
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · rw [if_neg same]
    exact MulChar.sum_eq_zero_of_ne_one (fun eq => same (mul_inv_eq_one.mp eq))

theorem dual_parseval {q : ℕ} [NeZero q] (characters : Finset (DirichletCharacter ℂ q))
    (c : DirichletCharacter ℂ q → ℂ) :
    (∑ x : ZMod q, ‖∑ χ ∈ characters, c χ * χ x‖ ^ 2) =
      (q.totient : ℝ) * ∑ χ ∈ characters, ‖c χ‖ ^ 2 := by
  let entry (χ ψ : DirichletCharacter ℂ q) (x : ZMod q) :=
    c χ * star (c ψ) * (χ x * star (ψ x))
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_pow,
    ← Complex.mul_conj']
  change (∑ x : ZMod q, (∑ χ ∈ characters, c χ * χ x) *
      star (∑ ψ ∈ characters, c ψ * ψ x)) =
    (q.totient : ℂ) * ∑ χ ∈ characters, c χ * star (c χ)
  calc
    _ = ∑ x : ZMod q, ∑ χ ∈ characters, ∑ ψ ∈ characters, entry χ ψ x := by
      refine sum_congr rfl fun x _ => ?_
      rw [star_sum, sum_mul_sum]
      refine sum_congr rfl fun χ _ => sum_congr rfl fun ψ _ => ?_
      rw [star_mul]
      unfold entry
      ac_rfl
    _ = ∑ χ ∈ characters, ∑ ψ ∈ characters, ∑ x : ZMod q, entry χ ψ x := by
      rw [Finset.sum_comm]
      exact sum_congr rfl fun χ _ => Finset.sum_comm
    _ = _ := by
      rw [mul_sum]
      refine sum_congr rfl fun χ member => ?_
      rw [sum_eq_single_of_mem χ member]
      · simp only [entry, ← Finset.mul_sum, character_pair_orthogonality, ite_true]
        ring
      · intro ψ _ different
        simp only [entry, ← Finset.mul_sum, character_pair_orthogonality,
          if_neg (Ne.symm different), mul_zero]

theorem sum_natCast_range_eq_zmod {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q] (f : ZMod q → R) :
    ∑ u ∈ range q, f (u : ZMod q) = ∑ z : ZMod q, f z := by
  apply sum_bij (s := range q) (t := (univ : Finset (ZMod q))) (fun u _ => (u : ZMod q))
  · simp
  · intro u uMember v vMember equal
    have valEqual := congrArg ZMod.val equal
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp uMember),
      Nat.mod_eq_of_lt (mem_range.mp vMember)] using valEqual
  · intro z _
    exact ⟨z.val, mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
  · intro u _
    rfl

theorem sum_natCast_mul_range {q : ℕ} [NeZero q] (k : ℕ) (f : ZMod q → ℝ) :
    ∑ u ∈ range (k * q), f (u : ZMod q) = (k : ℝ) * ∑ z : ZMod q, f z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have periodic (u : ℕ) : ((k * q + u : ℕ) : ZMod q) = (u : ZMod q) := by push_cast; simp
    simp_rw [periodic]
    rw [sum_natCast_range_eq_zmod]
    push_cast
    ring

theorem sum_natCast_le_cover {q : ℕ} [NeZero q] (X : ℕ) (f : ZMod q → ℝ)
    (nonnegative : ∀ x, 0 ≤ f x) :
    ∑ u ∈ range X, f (u : ZMod q) ≤ ((X / q + 1 : ℕ) : ℝ) * ∑ z : ZMod q, f z := by
  have bound : X ≤ (X / q + 1) * q := by
    calc
      X = X / q * q + X % q := by rw [Nat.mul_comm, Nat.div_add_mod]
      _ ≤ X / q * q + q := Nat.add_le_add_left (Nat.mod_lt _ (NeZero.pos q)).le _
      _ = _ := by ring
  refine (sum_le_sum_of_subset_of_nonneg (range_mono bound) (fun _ _ _ => nonnegative _)).trans_eq ?_
  exact sum_natCast_mul_range (X / q + 1) f

theorem dual_interval_le {q : ℕ} [NeZero q] (X : ℕ) (characters : Finset (DirichletCharacter ℂ q))
    (c : DirichletCharacter ℂ q → ℂ) :
    (∑ u ∈ range X, ‖∑ χ ∈ characters, c χ * χ (u : ZMod q)‖ ^ 2) ≤
      ((X : ℝ) + q) * ∑ χ ∈ characters, ‖c χ‖ ^ 2 := by
  have coefficientBound : ((X / q + 1 : ℕ) : ℝ) * (q.totient : ℝ) ≤ (X : ℝ) + q := by
    exact_mod_cast (show (X / q + 1) * q.totient ≤ X + q from calc
      _ ≤ (X / q + 1) * q := Nat.mul_le_mul_left _ (Nat.totient_le q)
      _ = X / q * q + q := by ring
      _ ≤ _ := Nat.add_le_add_right (Nat.div_mul_le_self X q) _)
  calc
    _ ≤ ((X / q + 1 : ℕ) : ℝ) * ∑ z : ZMod q, ‖∑ χ ∈ characters, c χ * χ z‖ ^ 2 :=
      sum_natCast_le_cover X _ (fun _ => sq_nonneg _)
    _ = (((X / q + 1 : ℕ) : ℝ) * (q.totient : ℝ)) * ∑ χ ∈ characters, ‖c χ‖ ^ 2 := by
      rw [dual_parseval, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right coefficientBound (sum_nonneg fun _ _ => sq_nonneg _)

end
end DyadicMixedB4DualCharacter

end

section

open Finset MeasureTheory

namespace DyadicMixedB4MaximalSieve

open DyadicMixedB4Fourier DyadicMixedB4Geometric BombieriVinogradov.LargeSieve

noncomputable section

theorem wave_one_eq_mode_sum (x : ℕ) (t : ℝ) :
    wave 1 0 x t = ∑ k ∈ range x, mode ((k : ℤ) + 1) t := by
  have indices : Ioc (0 : ℕ) x = Ico 1 (x + 1) := by
    ext k
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [wave, indices, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine sum_congr rfl fun k _ => ?_
  simp only [one_mul, Nat.cast_add, Nat.cast_one]
  unfold phase mode frequency
  congr 1
  push_cast
  ring

theorem prefix_integral {x Y : ℕ} (xBound : x ≤ Y) (a : ℕ → ℂ) :
    (∑ j ∈ range x, a j) = ∫ t in (0 : ℝ)..1,
      (∑ j ∈ range Y, a j * mode ((j : ℤ) + 1) t) * star (wave 1 0 x t) := by
  let entry (j k : ℕ) (t : ℝ) := a j * mode ((j : ℤ) - (k : ℤ)) t
  have continuousEntry (j k : ℕ) : Continuous (entry j k) :=
    continuous_const.mul (continuous_mode ((j : ℤ) - (k : ℤ)))
  symm
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ j ∈ range Y, ∑ k ∈ range x, entry j k t := by
      apply intervalIntegral.integral_congr
      intro t _
      change (∑ j ∈ range Y, a j * mode ((j : ℤ) + 1) t) * star (wave 1 0 x t) = _
      rw [wave_one_eq_mode_sum, star_sum, sum_mul_sum]
      refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
      rw [mul_assoc, mode_mul_conj]
      simp only [entry, add_sub_add_right_eq_sub]
    _ = ∑ j ∈ range Y, ∑ k ∈ range x, ∫ t in (0 : ℝ)..1, entry j k t := by
      rw [intervalIntegral.integral_finsetSum]
      · refine sum_congr rfl fun j _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        exact fun k _ => (continuousEntry j k).intervalIntegrable 0 1
      · intro j _
        exact (continuous_finsetSum _ fun k _ => continuousEntry j k).intervalIntegrable 0 1
    _ = ∑ k ∈ range x, ∑ j ∈ range Y, ∫ t in (0 : ℝ)..1, entry j k t := sum_comm
    _ = _ := by
      refine sum_congr rfl fun k membership => ?_
      have membershipY : k ∈ range Y := mem_range.mpr ((mem_range.mp membership).trans_le xBound)
      rw [sum_eq_single_of_mem k membershipY]
      · simp [entry, intervalIntegral.integral_const_mul, mode_integral]
      · intro j _ different
        have nonzero : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
        simp [entry, intervalIntegral.integral_const_mul, mode_integral, nonzero]

def prefixMajorant (Y : ℕ) (t : ℝ) : ℝ :=
  2 * smoothKernel (1 / ((Y : ℝ) + 1)) 0 t + 2 * smoothKernel (1 / ((Y : ℝ) + 1)) 1 t

theorem prefixMajorant_continuous (Y : ℕ) : Continuous (prefixMajorant Y) := by
  have positive : (0 : ℝ) < 1 / ((Y : ℝ) + 1) := by positivity
  exact (continuous_const.mul (cont_smoothKernel positive)).add
    (continuous_const.mul (cont_smoothKernel positive))

theorem prefixMajorant_positive (Y : ℕ) (t : ℝ) : 0 < prefixMajorant Y t := by
  unfold prefixMajorant smoothKernel
  positivity

theorem wave_one_le_prefixMajorant {x Y : ℕ} (xBound : x ≤ Y) {t : ℝ}
    (membership : t ∈ Set.Icc (0 : ℝ) 1) : ‖wave 1 0 x t‖ ≤ prefixMajorant Y t := by
  obtain ⟨i, iMember, dist⟩ := nearestCenter 1 t membership.1 membership.2
  have bound := waveBound (l := 0) (u := 1) (n := Y) (by decide) (by simpa using xBound) dist
  have iRange : i < 2 := mem_range.mp iMember
  have aNonnegative : (0 : ℝ) ≤ 1 / ((Y : ℝ) + 1) := by positivity
  obtain zero | one : i = 0 ∨ i = 1 := by omega
  · simpa [prefixMajorant, zero] using bound.trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (nonneg_smoothKernel (c := 1) (t := t) aNonnegative)))
  · simpa [prefixMajorant, one] using bound.trans
      (le_add_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (nonneg_smoothKernel (c := 0) (t := t) aNonnegative)))

theorem integral_prefixMajorant_positive (Y : ℕ) :
    0 < ∫ t in (0 : ℝ)..1, prefixMajorant Y t := by
  exact intervalIntegral.integral_pos (by norm_num) (prefixMajorant_continuous Y).continuousOn
    (fun t _ => (prefixMajorant_positive Y t).le)
    ⟨0, by simp, prefixMajorant_positive Y 0⟩

theorem integral_prefixMajorant_le (Y : ℕ) :
    (∫ t in (0 : ℝ)..1, prefixMajorant Y t) ≤ 8 * Real.log ((Y : ℝ) + 2) := by
  let a : ℝ := 1 / ((Y : ℝ) + 1)
  have aPositive : 0 < a := by dsimp [a]; positivity
  have left := integral_smoothKernel aPositive (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)
  have right := integral_smoothKernel aPositive (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)
  have ratio : (1 + a) / a = (Y : ℝ) + 2 := by dsimp [a]; field_simp; ring
  rw [ratio] at left right
  have intLeft : IntervalIntegrable (fun t => 2 * smoothKernel a 0 t) volume 0 1 :=
    (continuous_const.mul (cont_smoothKernel aPositive)).intervalIntegrable 0 1
  have intRight : IntervalIntegrable (fun t => 2 * smoothKernel a 1 t) volume 0 1 :=
    (continuous_const.mul (cont_smoothKernel aPositive)).intervalIntegrable 0 1
  change (∫ t in (0 : ℝ)..1, 2 * smoothKernel a 0 t + 2 * smoothKernel a 1 t) ≤ _
  rw [intervalIntegral.integral_add intLeft intRight, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  linarith only [left, right]

theorem integral_weighted_cauchy {w f : ℝ → ℝ} (wContinuous : Continuous w)
    (fContinuous : Continuous f) (wNonnegative : ∀ t, 0 ≤ w t)
    (massPositive : 0 < ∫ t in (0 : ℝ)..1, w t) :
    (∫ t in (0 : ℝ)..1, w t * f t) ^ 2 ≤
      (∫ t in (0 : ℝ)..1, w t) * (∫ t in (0 : ℝ)..1, w t * f t ^ 2) := by
  let mass : ℝ := ∫ t in (0 : ℝ)..1, w t
  let first : ℝ := ∫ t in (0 : ℝ)..1, w t * f t
  let second : ℝ := ∫ t in (0 : ℝ)..1, w t * f t ^ 2
  have nonnegative := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (fun t => mul_nonneg (wNonnegative t) (sq_nonneg (mass * f t - first)))
  have integral1 : IntervalIntegrable (fun t => mass ^ 2 * (w t * f t ^ 2)) volume 0 1 :=
    (continuous_const.mul (wContinuous.mul (fContinuous.pow 2))).intervalIntegrable 0 1
  have integral2 : IntervalIntegrable (fun t => (-2 * mass * first) * (w t * f t)) volume 0 1 :=
    (continuous_const.mul (wContinuous.mul fContinuous)).intervalIntegrable 0 1
  have integral3 : IntervalIntegrable (fun t => first ^ 2 * w t) volume 0 1 :=
    (continuous_const.mul wContinuous).intervalIntegrable 0 1
  have expanded : (∫ t in (0 : ℝ)..1, w t * (mass * f t - first) ^ 2) =
      mass ^ 2 * second + (-2 * mass * first) * first + first ^ 2 * mass := by
    calc
      _ = ∫ t in (0 : ℝ)..1, mass ^ 2 * (w t * f t ^ 2) +
          (-2 * mass * first) * (w t * f t) + first ^ 2 * w t := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        have sumIntegrable : IntervalIntegrable (fun t => mass ^ 2 * (w t * f t ^ 2) +
          (-2 * mass * first) * (w t * f t)) volume 0 1 := integral1.add integral2
        rw [intervalIntegral.integral_add sumIntegrable integral3,
          intervalIntegral.integral_add integral1 integral2]
        simp only [intervalIntegral.integral_const_mul, mass, first, second]
  rw [expanded] at nonnegative
  change first ^ 2 ≤ mass * second
  apply (mul_le_mul_iff_right₀ massPositive).mp
  nlinarith only [nonnegative]

def twist (a : ℤ → ℂ) (t : ℝ) (m : ℤ) : ℂ := a m * mode m t

theorem continuous_twistedCharacterSum (a : ℤ → ℂ) (Y q : ℕ) (χ : DirichletCharacter ℂ q) :
    Continuous (fun t => intervalCharacterSum (twist a t) 0 Y q χ) := by
  unfold intervalCharacterSum twist
  exact continuous_finsetSum _ fun m _ => (continuous_const.mul (continuous_mode m)).mul continuous_const

def finitePrefixEnergy (Y : ℕ) (a : ℕ → ℂ) : ℝ :=
  (range (Y + 1)).sup' (by simp) (fun x => ‖∑ j ∈ range x, a j‖ ^ 2)

def finiteTwistedSum (Y : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ range Y, a j * mode ((j : ℤ) + 1) t

theorem continuous_finiteTwistedSum (Y : ℕ) (a : ℕ → ℂ) : Continuous (finiteTwistedSum Y a) :=
  continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_mode _))

theorem finitePrefixEnergy_le_twists (Y : ℕ) (a : ℕ → ℂ) :
    finitePrefixEnergy Y a ≤ (∫ t in (0 : ℝ)..1, prefixMajorant Y t) *
      (∫ t in (0 : ℝ)..1, prefixMajorant Y t * ‖finiteTwistedSum Y a t‖ ^ 2) := by
  unfold finitePrefixEnergy
  apply Finset.sup'_le (by simp) _
  intro x xMember
  have xBound : x ≤ Y := Nat.le_of_lt_succ (mem_range.mp xMember)
  let polynomial := finiteTwistedSum Y a
  have polynomialContinuous : Continuous polynomial := continuous_finiteTwistedSum Y a
  have waveContinuous : Continuous (wave 1 0 x) := by unfold wave phase; fun_prop
  have integrandContinuous : Continuous (fun t => polynomial t * star (wave 1 0 x t)) :=
    polynomialContinuous.mul waveContinuous.star
  have normBound : ‖∑ j ∈ range x, a j‖ ≤
      ∫ t in (0 : ℝ)..1, prefixMajorant Y t * ‖polynomial t‖ := by
    rw [prefix_integral xBound]
    apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans
    apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (integrandContinuous.norm.intervalIntegrable 0 1)
      (((prefixMajorant_continuous Y).mul polynomialContinuous.norm).intervalIntegrable 0 1)
    intro t member
    rw [norm_mul, norm_star, mul_comm]
    exact mul_le_mul_of_nonneg_right (wave_one_le_prefixMajorant xBound member) (norm_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg _) normBound 2).trans
    (integral_weighted_cauchy (prefixMajorant_continuous Y) polynomialContinuous.norm
      (fun t => (prefixMajorant_positive Y t).le) (integral_prefixMajorant_positive Y))

end
end DyadicMixedB4MaximalSieve

end

section

open Finset MeasureTheory DyadicMixedB4MaximalSieve DyadicMixedB4DualCharacter

namespace DyadicMixedB4MixedCharacter

noncomputable section

def characterCoefficients {q : ℕ} (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (j : ℕ) : ℂ :=
  a j * χ ((j + 1 : ℕ) : ZMod q)

def mixture {q : ℕ} (characters : Finset (DirichletCharacter ℂ q))
    (a : ℕ → ℂ) (c : DirichletCharacter ℂ q → ℂ) (u j : ℕ) : ℂ :=
  a j * ∑ χ ∈ characters, c χ * χ (u : ZMod q) * χ ((j + 1 : ℕ) : ZMod q)

theorem finiteTwistedSum_mixture {q : ℕ} (Y : ℕ) (characters : Finset (DirichletCharacter ℂ q))
    (a : ℕ → ℂ) (c : DirichletCharacter ℂ q → ℂ) (u : ℕ) (t : ℝ) :
    finiteTwistedSum Y (mixture characters a c u) t =
      ∑ χ ∈ characters, (c χ * finiteTwistedSum Y (characterCoefficients a χ) t) * χ (u : ZMod q) := by
  let entry (j : ℕ) (χ : DirichletCharacter ℂ q) :=
    ((c χ * characterCoefficients a χ j) * DyadicMixedB4Fourier.mode ((j : ℤ) + 1) t) * χ (u : ZMod q)
  calc
    _ = ∑ j ∈ range Y, ∑ χ ∈ characters, entry j χ := by
      unfold finiteTwistedSum mixture
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun χ _ => ?_
      unfold entry characterCoefficients
      ring
    _ = ∑ χ ∈ characters, ∑ j ∈ range Y, entry j χ := sum_comm
    _ = _ := by
      refine sum_congr rfl fun χ _ => ?_
      unfold finiteTwistedSum
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      unfold entry
      ring

theorem mixed_character_prefix_moment {q : ℕ} [NeZero q] (X Y : ℕ)
    (characters : Finset (DirichletCharacter ℂ q)) (a : ℕ → ℂ)
    (c : DirichletCharacter ℂ q → ℂ) {C : ℝ}
    (cBound : ∀ χ ∈ characters, ‖c χ‖ ≤ C) :
    (∑ u ∈ range X, finitePrefixEnergy Y (mixture characters a c u)) ≤
      (∫ t in (0 : ℝ)..1, prefixMajorant Y t) * (((X : ℝ) + q) * C ^ 2) *
        ∫ t in (0 : ℝ)..1, prefixMajorant Y t *
          ∑ χ ∈ characters, ‖finiteTwistedSum Y (characterCoefficients a χ) t‖ ^ 2 := by
  let w := prefixMajorant Y
  let mass : ℝ := ∫ t in (0 : ℝ)..1, w t
  let bound : ℝ := ((X : ℝ) + q) * C ^ 2
  let polynomial (u : ℕ) := finiteTwistedSum Y (mixture characters a c u)
  let characterEnergy (t : ℝ) := ∑ χ ∈ characters, ‖finiteTwistedSum Y (characterCoefficients a χ) t‖ ^ 2
  have wContinuous : Continuous w := prefixMajorant_continuous Y
  have wPositive (t : ℝ) : 0 < w t := prefixMajorant_positive Y t
  have massPositive : 0 < mass := integral_prefixMajorant_positive Y
  have polynomialContinuous (u : ℕ) : Continuous (polynomial u) := continuous_finiteTwistedSum _ _
  have characterEnergyContinuous : Continuous characterEnergy :=
    continuous_finsetSum _ fun χ _ => (continuous_finiteTwistedSum Y (characterCoefficients a χ)).norm.pow 2
  have atPhase (t : ℝ) : (∑ u ∈ range X, ‖polynomial u t‖ ^ 2) ≤ bound * characterEnergy t := by
    have dual := dual_interval_le X characters
      (fun χ => c χ * finiteTwistedSum Y (characterCoefficients a χ) t)
    simp only [polynomial, finiteTwistedSum_mixture]
    refine dual.trans ?_
    unfold bound characterEnergy
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_sum]
    refine sum_le_sum fun χ member => ?_
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (cBound χ member) 2) (sq_nonneg _)
  have integralSum :
      (∑ u ∈ range X, ∫ t in (0 : ℝ)..1, w t * ‖polynomial u t‖ ^ 2) =
        ∫ t in (0 : ℝ)..1, w t * ∑ u ∈ range X, ‖polynomial u t‖ ^ 2 := by
    have intPolynomial (u : ℕ) : IntervalIntegrable (fun t => w t * ‖polynomial u t‖ ^ 2)
        volume 0 1 := (wContinuous.mul ((polynomialContinuous u).norm.pow 2)).intervalIntegrable 0 1
    rw [← intervalIntegral.integral_finsetSum (fun u _ => intPolynomial u)]
    apply intervalIntegral.integral_congr
    intro t _
    change (∑ u ∈ range X, w t * ‖polynomial u t‖ ^ 2) = w t * ∑ u ∈ range X, ‖polynomial u t‖ ^ 2
    exact (mul_sum _ _ _).symm
  have continuousSquareSum : Continuous (fun t => ∑ u ∈ range X, ‖polynomial u t‖ ^ 2) :=
    continuous_finsetSum _ fun u _ => (polynomialContinuous u).norm.pow 2
  change _ ≤ mass * bound * ∫ t in (0 : ℝ)..1, w t * characterEnergy t
  calc
    _ ≤ ∑ u ∈ range X, mass * ∫ t in (0 : ℝ)..1, w t * ‖polynomial u t‖ ^ 2 := by
      exact sum_le_sum fun u _ => finitePrefixEnergy_le_twists Y (mixture characters a c u)
    _ = mass * ∫ t in (0 : ℝ)..1, w t * ∑ u ∈ range X, ‖polynomial u t‖ ^ 2 := by
      rw [← mul_sum, integralSum]
    _ ≤ mass * ∫ t in (0 : ℝ)..1, w t * (bound * characterEnergy t) := by
      refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
        ((wContinuous.mul continuousSquareSum).intervalIntegrable 0 1)
        ((wContinuous.mul (continuous_const.mul characterEnergyContinuous)).intervalIntegrable 0 1)
        (fun t _ => mul_le_mul_of_nonneg_left (atPhase t) (wPositive t).le)) massPositive.le
    _ = _ := by
      have commute : (∫ t in (0 : ℝ)..1, w t * (bound * characterEnergy t)) =
          ∫ t in (0 : ℝ)..1, bound * (w t * characterEnergy t) := by
        apply intervalIntegral.integral_congr
        intro t _
        change w t * (bound * characterEnergy t) = bound * (w t * characterEnergy t)
        exact mul_left_comm _ _ _
      rw [commute, intervalIntegral.integral_const_mul, ← mul_assoc]

end
end DyadicMixedB4MixedCharacter

end

section

open Finset MeasureTheory DyadicMixedB4KernelControl DyadicMixedB4WindowKernel
open DyadicMixedB4ArcGeometry DyadicMixedB4MixedCharacter DyadicMixedB4MaximalSieve

namespace DyadicMixedB4DyadicBlock

noncomputable section

theorem sum_sqrt_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (nonnegative : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, Real.sqrt (f i)) ≤ Real.sqrt ((s.card : ℝ) * ∑ i ∈ s, f i) := by
  have squares : (∑ i ∈ s, Real.sqrt (f i)) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i := by
    have cs := sum_mul_sq_le_sq_mul_sq s (fun _ : ι => (1 : ℝ)) (fun i => Real.sqrt (f i))
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at cs
    have simplify : (∑ i ∈ s, Real.sqrt (f i) ^ 2) = ∑ i ∈ s, f i :=
      sum_congr rfl fun i member => Real.sq_sqrt (nonnegative i member)
    rwa [simplify] at cs
  calc
    _ = Real.sqrt ((∑ i ∈ s, Real.sqrt (f i)) ^ 2) :=
      (Real.sqrt_sq (sum_nonneg fun i _ => Real.sqrt_nonneg (f i))).symm
    _ ≤ _ := Real.sqrt_le_sqrt squares

theorem prefix_norm_le_sqrt_energy (Y x : ℕ) (a : ℕ → ℂ) (xBound : x ≤ Y) :
    ‖∑ j ∈ range x, a j‖ ≤ Real.sqrt (finitePrefixEnergy Y a) := by
  have member : x ∈ range (Y + 1) := mem_range.mpr (Nat.lt_succ_of_le xBound)
  have square := Finset.le_sup' (fun k => ‖∑ j ∈ range k, a j‖ ^ 2) member
  calc
    _ = Real.sqrt (‖∑ j ∈ range x, a j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt square

theorem finitePrefixEnergy_nonnegative (Y : ℕ) (a : ℕ → ℂ) : 0 ≤ finitePrefixEnergy Y a := by
  have member : 0 ∈ range (Y + 1) := by simp
  exact (sq_nonneg ‖∑ j ∈ range 0, a j‖).trans (Finset.le_sup' (fun x => ‖∑ j ∈ range x, a j‖ ^ 2) member)

theorem weighted_mixture_block_le {d : ℕ} [NeZero d] (n M B H q g l r X Y : ℕ)
    (nPositive : 0 < n) (radiusUpper : radius M ≤ 1)
    (characters : Finset (DirichletCharacter ℂ d)) (a : ℕ → ℂ) (c : DirichletCharacter ℂ d → ℂ)
    (support : Finset ℕ) (supportBound : support ⊆ range X) (start length : ℕ → ℕ) (weight : ℕ → ℂ)
    (startPositive : ∀ u ∈ support, 0 < start u) (lengthBound : ∀ u ∈ support, length u ≤ Y)
    (productBound : ∀ u ∈ support, start u * length u ≤ n)
    {W C : ℝ} (WNonnegative : 0 ≤ W) (CNonnegative : 0 ≤ C)
    (weightBound : ∀ u ∈ support, ‖weight u‖ ≤ W) (characterBound : ∀ χ ∈ characters, ‖c χ‖ ≤ C) :
    ‖∑ u ∈ support, weight u * (∑ j ∈ range (length u), windowKernel n M B H q g l r
      ((start u : ℝ) * ((j : ℝ) + 1) - n) • mixture characters a c u j)‖ ≤
      W * (16 / (g : ℝ) + 24 / (g : ℝ) * Real.log ((n : ℝ) + 1)) * C *
        Real.sqrt ((X : ℝ) * ((X : ℝ) + d) *
          (∫ t in (0 : ℝ)..1, prefixMajorant Y t) *
          ∫ t in (0 : ℝ)..1, prefixMajorant Y t *
            ∑ χ ∈ characters, ‖finiteTwistedSum Y (characterCoefficients a χ) t‖ ^ 2) := by
  let L : ℝ := 16 / (g : ℝ) + 24 / (g : ℝ) * Real.log ((n : ℝ) + 1)
  let E (u : ℕ) := finitePrefixEnergy Y (mixture characters a c u)
  let I : ℝ := ∫ t in (0 : ℝ)..1, prefixMajorant Y t
  let J : ℝ := ∫ t in (0 : ℝ)..1, prefixMajorant Y t *
    ∑ χ ∈ characters, ‖finiteTwistedSum Y (characterCoefficients a χ) t‖ ^ 2
  have logNonnegative : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have LNonnegative : 0 ≤ L := by dsimp [L]; positivity
  have Epositive (u : ℕ) : 0 ≤ E u := finitePrefixEnergy_nonnegative Y _
  have oneBound (u : ℕ) (uMember : u ∈ support) :
      ‖∑ j ∈ range (length u), windowKernel n M B H q g l r
        ((start u : ℝ) * ((j : ℝ) + 1) - n) • mixture characters a c u j‖ ≤ L * Real.sqrt (E u) :=
    weighted_windowKernel_sum_le n M B H q g l r (start u) (length u) (mixture characters a c u)
      nPositive (startPositive u uMember) (productBound u uMember) radiusUpper (Real.sqrt_nonneg _)
      (fun x xBound => prefix_norm_le_sqrt_energy Y x _ (xBound.trans (lengthBound u uMember)))
  have moment : (∑ u ∈ range X, E u) ≤ I * (((X : ℝ) + d) * C ^ 2) * J :=
    mixed_character_prefix_moment X Y characters a c characterBound
  change _ ≤ W * L * C * Real.sqrt ((X : ℝ) * ((X : ℝ) + d) * I * J)
  calc
    _ ≤ ∑ u ∈ support, ‖weight u * (∑ j ∈ range (length u), windowKernel n M B H q g l r
        ((start u : ℝ) * ((j : ℝ) + 1) - n) • mixture characters a c u j)‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ support, W * (L * Real.sqrt (E u)) := by
      refine sum_le_sum fun u uMember => ?_
      rw [norm_mul]
      exact mul_le_mul (weightBound u uMember) (oneBound u uMember) (norm_nonneg _) WNonnegative
    _ ≤ ∑ u ∈ range X, W * (L * Real.sqrt (E u)) :=
      sum_le_sum_of_subset_of_nonneg supportBound
        (fun u _ _ => mul_nonneg WNonnegative (mul_nonneg LNonnegative (Real.sqrt_nonneg (E u))))
    _ = W * L * ∑ u ∈ range X, Real.sqrt (E u) := by simp only [← mul_assoc, ← mul_sum]
    _ ≤ W * L * Real.sqrt ((X : ℝ) * ∑ u ∈ range X, E u) :=
      mul_le_mul_of_nonneg_left (by simpa only [card_range] using sum_sqrt_le (range X) E (fun u _ => Epositive u))
        (mul_nonneg WNonnegative LNonnegative)
    _ ≤ W * L * Real.sqrt ((X : ℝ) * (I * (((X : ℝ) + d) * C ^ 2) * J)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left moment (Nat.cast_nonneg _)))
        (mul_nonneg WNonnegative LNonnegative)
    _ = _ := by
      rw [show (X : ℝ) * (I * (((X : ℝ) + d) * C ^ 2) * J) =
        C ^ 2 * ((X : ℝ) * ((X : ℝ) + d) * I * J) by ring, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq CNonnegative]
      ring

end
end DyadicMixedB4DyadicBlock

end

section

open Finset MeasureTheory ArithmeticFunction DyadicMixedB4DyadicBlock
open DyadicMixedB4ArcGeometry DyadicMixedB4KernelControl DyadicMixedB4MixedCharacter DyadicMixedB4MaximalSieve

namespace DyadicMixedB4FixedBlock

noncomputable section

def mangoldtAbove (U j : ℕ) : ℂ := if U < j + 1 then (Λ (j + 1) : ℂ) else 0

theorem sum_Ioc_as_range_prefix {R : Type*} [AddCommMonoid R] (U L : ℕ) (F : ℕ → R) :
    (∑ b ∈ Ioc U L, F b) = ∑ j ∈ range L, if U < j + 1 then F (j + 1) else 0 := by
  rw [← sum_filter]
  symm
  apply sum_bij (s := (range L).filter (fun j => U < j + 1)) (t := Ioc U L) (fun j _ => j + 1)
  · intro j membership
    obtain ⟨upper, lower⟩ := mem_filter.mp membership
    exact mem_Ioc.mpr ⟨lower, Nat.succ_le_of_lt (mem_range.mp upper)⟩
  · intro j _ k _ equality
    omega
  · intro b membership
    obtain ⟨lower, upper⟩ := mem_Ioc.mp membership
    exact ⟨b - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), by omega⟩, by omega⟩
  · intro j _
    rfl

theorem fixed_conductor_block_le {d : ℕ} [NeZero d] (n M B H q step lower upper A g U : ℕ)
    (nPositive : 0 < n) (APositive : 0 < A) (gPositive : 0 < g) (radiusUpper : radius M ≤ 1)
    (indices : Finset ℕ) (indexRange : indices ⊆ Ico A (2 * A)) (indexDivisible : ∀ a ∈ indices, g ∣ a)
    (weight : ℕ → ℂ) {W C : ℝ} (WNonnegative : 0 ≤ W) (CNonnegative : 0 ≤ C)
    (weightBound : ∀ a ∈ indices, ‖weight a‖ ≤ W) (characters : Finset (DirichletCharacter ℂ d))
    (c : DirichletCharacter ℂ d → ℂ) (cBound : ∀ χ ∈ characters, ‖c χ‖ ≤ C) :
    let X := (2 * A) / g + 1
    let Y := n / A
    ‖∑ a ∈ indices, weight a * (∑ j ∈ range (n / a), windowKernel n M B H q step lower upper
      ((a : ℝ) * ((j : ℝ) + 1) - n) • mixture characters (mangoldtAbove U) c (a / g) j)‖ ≤
      W * (16 / (step : ℝ) + 24 / (step : ℝ) * Real.log ((n : ℝ) + 1)) * C *
        Real.sqrt ((X : ℝ) * ((X : ℝ) + d) *
          (∫ t in (0 : ℝ)..1, prefixMajorant Y t) *
          ∫ t in (0 : ℝ)..1, prefixMajorant Y t *
            ∑ χ ∈ characters, ‖finiteTwistedSum Y (characterCoefficients (mangoldtAbove U) χ) t‖ ^ 2) := by
  dsimp only
  let X := (2 * A) / g + 1
  let Y := n / A
  let quotients := indices.image (fun a => a / g)
  let start (u : ℕ) := g * u
  let length (u : ℕ) := n / start u
  have startExact (a : ℕ) (member : a ∈ indices) : start (a / g) = a := Nat.mul_div_cancel' (indexDivisible a member)
  have injOn : Set.InjOn (fun a => a / g) (indices : Set ℕ) := by
    intro a aMember b bMember equality
    exact (startExact a aMember).symm.trans ((congrArg start equality).trans (startExact b bMember))
  have supportBound : quotients ⊆ range X := by
    intro u membership
    obtain ⟨a, member, rfl⟩ := mem_image.mp membership
    have upperA := (mem_Ico.mp (indexRange member)).2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right upperA.le))
  have startPositive (u : ℕ) (membership : u ∈ quotients) : 0 < start u := by
    obtain ⟨a, member, rfl⟩ := mem_image.mp membership
    rw [startExact a member]
    exact APositive.trans_le (mem_Ico.mp (indexRange member)).1
  have lengthBound (u : ℕ) (membership : u ∈ quotients) : length u ≤ Y := by
    obtain ⟨a, member, rfl⟩ := mem_image.mp membership
    unfold length
    rw [startExact a member]
    apply (Nat.le_div_iff_mul_le APositive).mpr
    exact (Nat.mul_le_mul_left _ (mem_Ico.mp (indexRange member)).1).trans (Nat.div_mul_le_self n a)
  have productBound (u : ℕ) (_ : u ∈ quotients) : start u * length u ≤ n := by
    unfold length
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  have mappedWeightBound (u : ℕ) (membership : u ∈ quotients) : ‖weight (start u)‖ ≤ W := by
    obtain ⟨a, member, rfl⟩ := mem_image.mp membership
    rw [startExact a member]
    exact weightBound a member
  have main := weighted_mixture_block_le n M B H q step lower upper X Y nPositive radiusUpper characters
    (mangoldtAbove U) c quotients supportBound start length (fun u => weight (start u)) startPositive lengthBound
    productBound WNonnegative CNonnegative mappedWeightBound cBound
  unfold quotients at main
  rw [sum_image injOn] at main
  have convertSum : (∑ a ∈ indices, weight (start (a / g)) *
      (∑ j ∈ range (length (a / g)), windowKernel n M B H q step lower upper
        ((start (a / g) : ℝ) * ((j : ℝ) + 1) - n) • mixture characters (mangoldtAbove U) c (a / g) j)) =
      ∑ a ∈ indices, weight a * (∑ j ∈ range (n / a), windowKernel n M B H q step lower upper
        ((a : ℝ) * ((j : ℝ) + 1) - n) • mixture characters (mangoldtAbove U) c (a / g) j) := by
    refine sum_congr rfl fun a member => ?_
    unfold length
    rw [startExact a member]
  rwa [convertSum] at main

end
end DyadicMixedB4FixedBlock

end

section

open Finset MeasureTheory DyadicMixedB4MaximalSieve BombieriVinogradov.LargeSieve

namespace DyadicMixedB4PrimitiveEnergy

noncomputable section

def primitiveEnergy (Y q : ℕ) (a : ℤ → ℂ) (t : ℝ) : ℝ :=
  ∑ χ ∈ primitiveCharacters q, ‖intervalCharacterSum (twist a t) 0 Y q χ‖ ^ 2

def integratedPrimitiveEnergy (Y q : ℕ) (a : ℤ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, prefixMajorant Y t * primitiveEnergy Y q a t

theorem primitiveEnergy_nonnegative (Y q : ℕ) (a : ℤ → ℂ) (t : ℝ) : 0 ≤ primitiveEnergy Y q a t :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem primitiveEnergy_continuous (Y q : ℕ) (a : ℤ → ℂ) : Continuous (primitiveEnergy Y q a) :=
  continuous_finsetSum _ fun χ _ => (continuous_twistedCharacterSum a Y q χ).norm.pow 2

theorem integratedPrimitiveEnergy_nonnegative (Y q : ℕ) (a : ℤ → ℂ) : 0 ≤ integratedPrimitiveEnergy Y q a :=
  intervalIntegral.integral_nonneg_of_forall zero_le_one
    (fun t => mul_nonneg (prefixMajorant_positive Y t).le (primitiveEnergy_nonnegative Y q a t))

theorem sum_primitiveEnergy_le (Y Q : ℕ) (a : ℤ → ℂ) (t : ℝ) (QPositive : 1 ≤ Q) :
    (∑ q ∈ Icc 1 Q, primitiveEnergy Y q a t) ≤ 64 * ((Y : ℝ) + (Q : ℝ) ^ 2) *
      ∑ m ∈ Ioc (0 : ℤ) (Y : ℤ), ‖a m‖ ^ 2 := by
  have normTwist (m : ℤ) : ‖twist a t m‖ = ‖a m‖ := by
    rw [twist, norm_mul, show ‖DyadicMixedB4Fourier.mode m t‖ = 1 by
      simp [DyadicMixedB4Fourier.mode, DyadicMixedB4Fourier.frequency, Complex.norm_exp], mul_one]
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * primitiveEnergy Y q a t := by
      refine sum_le_sum fun q member => ?_
      have qPositive := (mem_Icc.mp member).1
      have totientPositive : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr qPositive
      have weight : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) :=
        (one_le_div totientPositive).mpr (by exact_mod_cast Nat.totient_le q)
      exact le_mul_of_one_le_left (primitiveEnergy_nonnegative Y q a t) weight
    _ ≤ _ := by
      simpa only [primitiveEnergy, zero_add, normTwist] using characterLargeSieveNat 0 Y Q (twist a t) QPositive

theorem sum_integratedPrimitiveEnergy_le (Y Q : ℕ) (a : ℤ → ℂ) (QPositive : 1 ≤ Q) :
    (∑ q ∈ Icc 1 Q, integratedPrimitiveEnergy Y q a) ≤
      (∫ t in (0 : ℝ)..1, prefixMajorant Y t) * (64 * ((Y : ℝ) + (Q : ℝ) ^ 2) *
        ∑ m ∈ Ioc (0 : ℤ) (Y : ℤ), ‖a m‖ ^ 2) := by
  let w := prefixMajorant Y
  let P : ℝ := 64 * ((Y : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Ioc (0 : ℤ) (Y : ℤ), ‖a m‖ ^ 2
  have wContinuous : Continuous w := prefixMajorant_continuous Y
  have integrable (q : ℕ) : IntervalIntegrable (fun t => w t * primitiveEnergy Y q a t) volume 0 1 :=
    (wContinuous.mul (primitiveEnergy_continuous Y q a)).intervalIntegrable 0 1
  have sumContinuous : Continuous (fun t => ∑ q ∈ Icc 1 Q, primitiveEnergy Y q a t) :=
    continuous_finsetSum _ fun q _ => primitiveEnergy_continuous Y q a
  change _ ≤ (∫ t in (0 : ℝ)..1, w t) * P
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ q ∈ Icc 1 Q, w t * primitiveEnergy Y q a t := by
      unfold integratedPrimitiveEnergy
      rw [intervalIntegral.integral_finsetSum (fun q _ => integrable q)]
    _ = ∫ t in (0 : ℝ)..1, w t * ∑ q ∈ Icc 1 Q, primitiveEnergy Y q a t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact (mul_sum _ _ _).symm
    _ ≤ ∫ t in (0 : ℝ)..1, w t * P := by
      exact intervalIntegral.integral_mono_on zero_le_one
        ((wContinuous.mul sumContinuous).intervalIntegrable 0 1)
        ((wContinuous.mul continuous_const).intervalIntegrable 0 1)
        (fun t _ => mul_le_mul_of_nonneg_left (sum_primitiveEnergy_le Y Q a t QPositive)
          (prefixMajorant_positive Y t).le)
    _ = _ := intervalIntegral.integral_mul_const _ _

theorem dyadic_integratedPrimitiveEnergy_le (Y D : ℕ) (a : ℤ → ℂ) (DPositive : 0 < D) :
    (∑ q ∈ Ico D (2 * D), integratedPrimitiveEnergy Y q a) ≤
      (∫ t in (0 : ℝ)..1, prefixMajorant Y t) * (64 * ((Y : ℝ) + ((2 * D : ℕ) : ℝ) ^ 2) *
        ∑ m ∈ Ioc (0 : ℤ) (Y : ℤ), ‖a m‖ ^ 2) := by
  have subset : Ico D (2 * D) ⊆ Icc 1 (2 * D) := by
    intro q member
    obtain ⟨lower, upper⟩ := mem_Ico.mp member
    exact mem_Icc.mpr ⟨DPositive.trans_le lower, upper.le⟩
  exact (sum_le_sum_of_subset_of_nonneg subset (fun q _ _ => integratedPrimitiveEnergy_nonnegative Y q a)).trans
    (sum_integratedPrimitiveEnergy_le Y (2 * D) a (by omega))

def naturalCoefficientExtension (a : ℕ → ℂ) (m : ℤ) : ℂ := a ((m - 1).toNat)

theorem characterCoefficients_eq_extension {q : ℕ} (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) :
    DyadicMixedB4MixedCharacter.characterCoefficients a χ =
      fun (j : ℕ) => naturalCoefficientExtension a ((j : ℤ) + 1) * χ (((j : ℤ) + 1 : ℤ) : ZMod q) := by
  funext j
  simp [DyadicMixedB4MixedCharacter.characterCoefficients, naturalCoefficientExtension]

end
end DyadicMixedB4PrimitiveEnergy

end

section

open Finset MeasureTheory ArithmeticFunction BombieriVinogradov.LargeSieve
open DyadicMixedB4FixedBlock DyadicMixedB4PrimitiveEnergy DyadicMixedB4DyadicBlock
open DyadicMixedB4MaximalSieve DyadicMixedB4MixedCharacter

namespace DyadicMixedB4BilinearEnergy

noncomputable section

def prefixMass (Y : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, prefixMajorant Y t

theorem prefixMass_nonnegative (Y : ℕ) : 0 ≤ prefixMass Y :=
  intervalIntegral.integral_nonneg_of_forall zero_le_one (fun t => (prefixMajorant_positive Y t).le)

def mangoldtExtension (U : ℕ) : ℤ → ℂ := naturalCoefficientExtension (mangoldtAbove U)

def blockEnergy (n A U g d : ℕ) : ℝ :=
  let X := (2 * A) / g + 1
  let Y := n / A
  Real.sqrt ((X : ℝ) * ((X : ℝ) + d) * prefixMass Y *
    integratedPrimitiveEnergy Y d (mangoldtExtension U))

theorem finiteTwistedSum_eq_primitiveEnergy {d : ℕ} (Y U : ℕ) (χ : DirichletCharacter ℂ d) (t : ℝ) :
    finiteTwistedSum Y (characterCoefficients (mangoldtAbove U) χ) t =
      intervalCharacterSum (twist (mangoldtExtension U) t) 0 Y d χ := by
  unfold finiteTwistedSum intervalCharacterSum
  rw [sum_int_Ioc_eq_sum_range]
  simp only [zero_add]
  refine sum_congr rfl fun j _ => ?_
  rw [characterCoefficients_eq_extension]
  unfold twist mangoldtExtension
  ring

theorem energy_mangoldt_le (U Y : ℕ) :
    (∑ b ∈ Ioc (0 : ℤ) (Y : ℤ), ‖mangoldtExtension U b‖ ^ 2) ≤
      (Y : ℝ) * Real.log ((Y : ℝ) + 2) ^ 2 := by
  have atOne (j : ℕ) (membership : j ∈ range Y) : ‖mangoldtAbove U j‖ ≤ Real.log ((Y : ℝ) + 2) := by
    unfold mangoldtAbove
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      exact vonMangoldt_le_log.trans (Real.log_le_log (by positivity)
        (by exact_mod_cast (show j + 1 ≤ Y + 2 by have := mem_range.mp membership; omega)))
    · rw [norm_zero]
      exact Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) Y])
  calc
    _ = ∑ j ∈ range Y, ‖mangoldtAbove U j‖ ^ 2 := by
      rw [← zero_add (Y : ℤ), sum_int_Ioc_eq_sum_range]
      simp [mangoldtExtension, naturalCoefficientExtension]
    _ ≤ ∑ _ ∈ range Y, Real.log ((Y : ℝ) + 2) ^ 2 :=
      sum_le_sum fun j member => pow_le_pow_left₀ (norm_nonneg _) (atOne j member) 2
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_range]

theorem sum_sqrt_dyadic_energy_le (Y U D : ℕ) (DPositive : 0 < D) :
    (∑ d ∈ Ico D (2 * D), Real.sqrt (integratedPrimitiveEnergy Y d (mangoldtExtension U))) ≤
      16 * Real.log ((Y : ℝ) + 2) * Real.sqrt ((D : ℝ) * prefixMass Y * ((Y : ℝ) + (D : ℝ) ^ 2) * Y) := by
  let J d := integratedPrimitiveEnergy Y d (mangoldtExtension U)
  let L := Real.log ((Y : ℝ) + 2)
  have LNonnegative : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) Y])
  have massNonnegative := prefixMass_nonnegative Y
  have setCard : (Ico D (2 * D)).card = D := by rw [Nat.card_Ico]; omega
  have bound : (∑ d ∈ Ico D (2 * D), J d) ≤
      256 * prefixMass Y * ((Y : ℝ) + (D : ℝ) ^ 2) * (Y : ℝ) * L ^ 2 := by
    calc
      _ ≤ prefixMass Y * (64 * ((Y : ℝ) + ((2 * D : ℕ) : ℝ) ^ 2) *
          ∑ b ∈ Ioc (0 : ℤ) (Y : ℤ), ‖mangoldtExtension U b‖ ^ 2) :=
        dyadic_integratedPrimitiveEnergy_le Y D (mangoldtExtension U) DPositive
      _ ≤ prefixMass Y * (64 * ((Y : ℝ) + ((2 * D : ℕ) : ℝ) ^ 2) * ((Y : ℝ) * L ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (energy_mangoldt_le U Y) (by positivity)) massNonnegative
      _ ≤ _ := by
        push_cast
        nlinarith only [mul_nonneg massNonnegative (mul_nonneg (sq_nonneg (Y : ℝ)) (sq_nonneg L))]
  calc
    _ ≤ Real.sqrt ((D : ℝ) * ∑ d ∈ Ico D (2 * D), J d) := by
      simpa only [setCard] using sum_sqrt_le (Ico D (2 * D)) J
        (fun d _ => integratedPrimitiveEnergy_nonnegative Y d (mangoldtExtension U))
    _ ≤ Real.sqrt ((D : ℝ) * (256 * prefixMass Y * ((Y : ℝ) + (D : ℝ) ^ 2) * (Y : ℝ) * L ^ 2)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg _))
    _ = _ := by
      have factor : (D : ℝ) * (256 * prefixMass Y * ((Y : ℝ) + (D : ℝ) ^ 2) * (Y : ℝ) * L ^ 2) =
          (16 * L) ^ 2 * ((D : ℝ) * prefixMass Y * ((Y : ℝ) + (D : ℝ) ^ 2) * Y) := by ring
      rw [factor, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 16 * L)]

end
end DyadicMixedB4BilinearEnergy

end

section

open Finset BombieriVinogradov.LargeSieve DyadicMixedB4DualCharacter
open scoped Classical

namespace DyadicMixedB4GaussLift

noncomputable section

theorem sum_range_blocks {R : Type*} [AddCommMonoid R] (d f : ℕ) (F : ℕ → R) :
    ∑ x ∈ range (d * f), F x = ∑ j ∈ range f, ∑ a ∈ range d, F (d * j + a) := by
  induction f with
  | zero => simp
  | succ f ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

theorem stdAddChar_nat_fraction {q : ℕ} [NeZero q] (k : ℕ) :
    ZMod.stdAddChar (k : ZMod q) = additivePhase ((k : ℝ) / q) := by
  rw [← Int.cast_natCast k, ZMod.stdAddChar_coe]
  unfold additivePhase
  rw [circleMap_zero, Complex.ofReal_one, one_mul]
  push_cast
  congr 1
  ring

theorem stdAddChar_mul_nat_fraction {q : ℕ} [NeZero q] (k a : ℕ) :
    ZMod.stdAddChar ((k : ZMod q) * (a : ZMod q)) = additivePhase ((k : ℝ) * a / q) := by
  rw [← Nat.cast_mul, stdAddChar_nat_fraction, Nat.cast_mul]

set_option maxHeartbeats 600000 in
theorem sum_phase_fraction_eq_if_dvd {q : ℕ} [NeZero q] (k : ℕ) :
    (∑ a ∈ range q, additivePhase ((k : ℝ) * a / q)) = if q ∣ k then (q : ℂ) else 0 := by
  simp_rw [← stdAddChar_mul_nat_fraction]
  rw [sum_natCast_range_eq_zmod (fun z => ZMod.stdAddChar ((k : ZMod q) * z))]
  simp_rw [mul_comm (k : ZMod q)]
  rw [AddChar.sum_mulShift (k : ZMod q) (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  have zeroIff : (k : ZMod q) = 0 ↔ q ∣ k := by rw [ZMod.natCast_eq_zero_iff]
  by_cases divides : q ∣ k
  · simp [divides, zeroIff.mpr divides]
  · have nonzero : (k : ZMod q) ≠ 0 := fun zero => divides (zeroIff.mp zero)
    simp [divides, nonzero]

theorem gaussSum_as_fraction_sum {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod d)) =
      ∑ a ∈ range d, χ (a : ZMod d) * additivePhase ((k : ℝ) * a / d) := by
  unfold gaussSum
  rw [← sum_natCast_range_eq_zmod]
  simp_rw [AddChar.mulShift_apply, stdAddChar_mul_nat_fraction]

set_option maxHeartbeats 600000 in
theorem lift_gaussSum {d f : ℕ} [NeZero d] [NeZero f]
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    (∑ u ∈ range (d * f), χ (u : ZMod d) * additivePhase ((k : ℝ) * u / ((d : ℝ) * f))) =
      if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
  have dNonzero : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have fNonzero : (f : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne f
  rw [sum_range_blocks, Finset.sum_comm]
  have liftEntry (a j : ℕ) :
      χ ((d * j + a : ℕ) : ZMod d) * additivePhase ((k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f)) =
        (χ (a : ZMod d) * additivePhase ((k : ℝ) * a / ((d : ℝ) * f))) *
          additivePhase ((k : ℝ) * j / f) := by
    have angle : (k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f) =
        (k : ℝ) * a / ((d : ℝ) * f) + (k : ℝ) * j / f := by
      push_cast
      field_simp
      ring
    rw [angle, additivePhase_add, ← mul_assoc]
    have same : ((d * j + a : ℕ) : ZMod d) = (a : ZMod d) := by push_cast; simp
    rw [same]
  simp_rw [liftEntry, ← mul_sum, sum_phase_fraction_eq_if_dvd]
  by_cases divisible : f ∣ k
  · simp only [if_pos divisible, ← Finset.sum_mul, gaussSum_as_fraction_sum]
    rw [mul_comm _ (f : ℂ)]
    apply congrArg (fun z : ℂ => (f : ℂ) * z)
    refine sum_congr rfl fun a _ => ?_
    have h : (k : ℝ) = ((k / f : ℕ) : ℝ) * f := by
      exact_mod_cast (Nat.div_mul_cancel divisible).symm
    have sameAngle : (k : ℝ) * a / ((d : ℝ) * f) = (((k / f : ℕ) : ℝ)) * a / d := by
      conv_lhs => rw [h]
      field_simp
    rw [sameAngle]
  · simp [divisible]

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

theorem moebius_coprime_indicator {M : ℕ} (MPositive : 0 < M) (u : ℕ) :
    (∑ e ∈ M.divisors.filter (fun e => e ∣ u), moebiusComplex e) =
      if u.Coprime M then (1 : ℂ) else 0 := by
  let g := u.gcd M
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_right u MPositive
  have divisorsEquality : M.divisors.filter (fun e => e ∣ u) = g.divisors := by
    ext e
    rw [mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨eDividesM, _⟩, eDividesU⟩
      exact ⟨Nat.dvd_gcd eDividesU eDividesM, gPositive.ne'⟩
    · rintro ⟨eDividesG, _⟩
      exact ⟨⟨eDividesG.trans (Nat.gcd_dvd_right u M), MPositive.ne'⟩,
        eDividesG.trans (Nat.gcd_dvd_left u M)⟩
  have convolution : (∑ e ∈ g.divisors, μ e) = (1 : ArithmeticFunction ℤ) g := by
    rw [← coe_mul_zeta_apply (f := μ), moebius_mul_coe_zeta]
  rw [divisorsEquality]
  simp_rw [moebiusComplex, ← Int.cast_sum, convolution]
  change (((1 : ArithmeticFunction ℤ) g : ℤ) : ℂ) = if g = 1 then (1 : ℂ) else 0
  by_cases one : g = 1
  · simp [one, one_apply]
  · simp [one, one_apply]

theorem changeLevel_nat_indicator {d M : ℕ} (dDivides : d ∣ M) (χ : DirichletCharacter ℂ d)
    (u : ℕ) : DirichletCharacter.changeLevel dDivides χ (u : ZMod M) =
      (if u.Coprime M then (1 : ℂ) else 0) * χ (u : ZMod d) := by
  by_cases coprime : u.Coprime M
  · rw [if_pos coprime, one_mul]
    have same := DirichletCharacter.changeLevel_eq_cast_of_dvd χ dDivides (ZMod.unitOfCoprime u coprime)
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast dDivides] at same
    exact same
  · rw [if_neg coprime, zero_mul]
    exact MulChar.map_nonunit _ (fun unit => coprime ((ZMod.isUnit_iff_coprime u M).mp unit))

theorem sum_filter_dvd_range {R : Type*} [AddCommMonoid R] {e M : ℕ}
    (ePositive : 0 < e) (eDivides : e ∣ M) (F : ℕ → R) :
    (∑ u ∈ (range M).filter (fun u => e ∣ u), F u) = ∑ v ∈ range (M / e), F (e * v) := by
  have quotient : e * (M / e) = M := Nat.mul_div_cancel' eDivides
  symm
  apply sum_bij (s := range (M / e)) (t := (range M).filter (fun u => e ∣ u)) (fun v _ => e * v)
  · intro v vMember
    refine mem_filter.mpr ⟨mem_range.mpr ?_, dvd_mul_right e v⟩
    rw [← quotient]
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp vMember) ePositive
  · intro v _ w _ eq
    exact Nat.eq_of_mul_eq_mul_left ePositive eq
  · intro u uMember
    obtain ⟨uRange, v, h⟩ := mem_filter.mp uMember
    refine ⟨v, mem_range.mpr ?_, h.symm⟩
    have prodLt : e * v < e * (M / e) := h ▸ quotient.symm ▸ mem_range.mp uRange
    exact Nat.lt_of_mul_lt_mul_left prodLt
  · intro v _
    rfl

theorem sum_inducedGauss_moebius {d M : ℕ} [NeZero M] (dDivides : d ∣ M)
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M)) =
      ∑ e ∈ M.divisors, moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) * additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) := by
  rw [gaussSum_as_fraction_sum]
  calc
    _ = ∑ u ∈ range M, ∑ e ∈ M.divisors.filter (fun e => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      refine sum_congr rfl fun u _ => ?_
      rw [changeLevel_nat_indicator, ← moebius_coprime_indicator (NeZero.pos M), mul_assoc, sum_mul]
    _ = ∑ e ∈ M.divisors, ∑ u ∈ (range M).filter (fun u => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = _ := by
      refine sum_congr rfl fun e eMember => ?_
      have eDivides := (Nat.mem_divisors.mp eMember).1
      have ePositive := Nat.pos_of_mem_divisors eMember
      have eNonzero : (e : ℝ) ≠ 0 := by exact_mod_cast ePositive.ne'
      have MNonzero : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
      have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
      have quotientNonzero : ((M / e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast quotientPositive.ne'
      have quotient : (M : ℝ) = e * ((M / e : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' eDivides).symm
      rw [sum_filter_dvd_range ePositive eDivides, mul_sum]
      refine sum_congr rfl fun v _ => ?_
      have scales : (k : ℝ) * (e * v : ℕ) / M = (k : ℝ) * v / ((M / e : ℕ) : ℝ) := by
        push_cast
        rw [quotient]
        field_simp
      rw [scales, Nat.cast_mul, map_mul]
      ring

end
end DyadicMixedB4MoebiusGauss

end

section

open Finset DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss
open scoped Classical

namespace DyadicMixedB4ImprimitiveBound

noncomputable section

theorem norm_primitive_gauss_shift_le {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (primitive : χ.IsPrimitive) (x : ZMod d) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ ≤ Real.sqrt d := by
  rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar primitive, norm_mul,
    DirichletCharacter.norm_gaussSum_stdAddChar primitive]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (DirichletCharacter.norm_le_one _ _)

theorem conductor_cofactor {M d e : ℕ} [NeZero d] [NeZero M] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (coprime : e.Coprime d) :
    0 < M / e / d ∧ d * (M / e / d) = M / e ∧ e * (d * (M / e / d)) = M := by
  have eDivides := (Nat.mem_divisors.mp eMember).1
  have ePositive := Nat.pos_of_mem_divisors eMember
  have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
  have joint : e * d ∣ M := coprime.mul_dvd_of_dvd_of_dvd eDivides dDivides
  have dividesQuotient : d ∣ M / e := (Nat.dvd_div_iff_mul_dvd eDivides).mpr (by simpa [mul_comm] using joint)
  have quotient := Nat.mul_div_cancel' dividesQuotient
  exact ⟨Nat.div_pos (Nat.le_of_dvd quotientPositive dividesQuotient) (NeZero.pos d), quotient,
    by rw [quotient, Nat.mul_div_cancel' eDivides]⟩

theorem norm_induced_gauss_term {M d e : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (k : ℕ) {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) :
    ‖moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) *
          BombieriVinogradov.LargeSieve.additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ)))‖ ≤
      if e.Coprime d ∧ (M / e / d) ∣ k then ((M / e / d : ℕ) : ℝ) * Real.sqrt d else 0 := by
  by_cases coprime : e.Coprime d
  · obtain ⟨fPositive, hFactor, _⟩ := conductor_cofactor dDivides eMember coprime
    let f := M / e / d
    letI : NeZero f := ⟨fPositive.ne'⟩
    have liftIdentity : (∑ v ∈ range (M / e), χ (v : ZMod d) *
        BombieriVinogradov.LargeSieve.additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) =
        if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
      convert lift_gaussSum (f := f) χ k using 1
      rw [show (M / e : ℕ) = d * f from hFactor.symm, Nat.cast_mul]
    rw [liftIdentity]
    by_cases divides : f ∣ k
    · have divides' : (M / e / d) ∣ k := divides
      have relevant : e.Coprime d ∧ (M / e / d) ∣ k := ⟨coprime, divides'⟩
      simp only [if_pos divides, if_pos relevant, norm_mul, Complex.norm_natCast]
      have factor : ‖moebiusComplex e‖ * ‖χ (e : ZMod d)‖ ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)).trans
          (by simpa only [mul_one] using norm_moebiusComplex_le_one e)
      refine (mul_le_of_le_one_left (by positivity) factor).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_primitive_gauss_shift_le primitive _) (Nat.cast_nonneg _)
    · have divides' : ¬(M / e / d) ∣ k := divides
      simp [divides, divides', coprime]
  · have valZero : χ (e : ZMod d) = 0 := MulChar.map_nonunit _
      (fun h => coprime ((ZMod.isUnit_iff_coprime e d).mp h))
    simp [coprime, valZero]

theorem norm_induced_gauss_le {M d : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M))‖ ≤
      Real.sqrt d * ∑ f ∈ k.divisors.filter (fun f => d * f ∣ M), (f : ℝ) := by
  let cof (e : ℕ) := M / e / d
  let support := M.divisors.filter (fun e => e.Coprime d ∧ cof e ∣ k)
  let bound := k.divisors.filter (fun f => d * f ∣ M)
  have imageSubset : support.image cof ⊆ bound := by
    intro f member
    obtain ⟨e, eMember, rfl⟩ := mem_image.mp member
    obtain ⟨divisor, coprime, divides⟩ := mem_filter.mp eMember
    obtain ⟨_, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨divides, kPositive.ne'⟩,
      ⟨e, by rw [mul_comm]; exact identity.symm⟩⟩
  have injectiveOn : Set.InjOn cof (support : Set ℕ) := by
    intro e eMember e' e'Member same
    obtain ⟨divisor, coprime, _⟩ := mem_filter.mp eMember
    obtain ⟨divisor', coprime', _⟩ := mem_filter.mp e'Member
    obtain ⟨fPositive, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    obtain ⟨_, _, identity'⟩ := conductor_cofactor dDivides divisor' coprime'
    change e * (d * cof e) = M at identity
    change e' * (d * cof e') = M at identity'
    rw [← same] at identity'
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (NeZero.pos d) fPositive) (identity.trans identity'.symm)
  have sumBound : (∑ e ∈ support, (cof e : ℝ)) ≤ ∑ f ∈ bound, (f : ℝ) := by
    rw [← sum_image injectiveOn]
    exact sum_le_sum_of_subset_of_nonneg imageSubset fun _ _ _ => Nat.cast_nonneg _
  rw [sum_inducedGauss_moebius]
  refine (norm_sum_le _ _).trans ?_
  have boundTerms := sum_le_sum (s := M.divisors)
    (fun e member => norm_induced_gauss_term dDivides member k primitive)
  refine boundTerms.trans ?_
  change (∑ e ∈ M.divisors, if e.Coprime d ∧ cof e ∣ k then (cof e : ℝ) * Real.sqrt d else 0) ≤
    Real.sqrt d * ∑ f ∈ bound, (f : ℝ)
  rw [← sum_filter, ← sum_mul, mul_comm (Real.sqrt d)]
  exact mul_le_mul_of_nonneg_right sumBound (Real.sqrt_nonneg _)

end
end DyadicMixedB4ImprimitiveBound

end

section

open Finset DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss BombieriVinogradov.LargeSieve
open scoped Classical ComplexConjugate

namespace DyadicMixedB4Ramanujan

noncomputable section

theorem phase_eq_additivePhase (x : ℝ) : phase x = additivePhase x := by
  simp only [phase, additivePhase, circleMap_zero, Complex.ofReal_one, one_mul]

theorem phase_neg (x : ℝ) : phase (-x) = conj (phase x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  have conjTwo : (starRingEnd ℂ) 2 = 2 := by
    simpa only [Nat.cast_ofNat] using (map_natCast (starRingEnd ℂ) 2)
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, conjTwo]
  ring

theorem norm_ramanujan_neg (q : ℕ) (k : ℤ) : ‖ramanujan q (-k)‖ = ‖ramanujan q k‖ := by
  have equality : ramanujan q (-k) = conj (ramanujan q k) := by
    simp only [ramanujan, Int.cast_neg, neg_mul, phase_neg, map_sum]
  rw [equality, Complex.norm_conj]

theorem numSet_eq_coprime_filter {q : ℕ} (qLower : 1 < q) :
    numSet q = (range q).filter (fun a => a.Coprime q) := by
  ext a
  simp only [numSet, mem_filter, mem_range]
  constructor
  · rintro ⟨upper, coprime⟩
    refine ⟨?_, coprime⟩
    by_contra! lower
    have equality : a = q := by omega
    subst a
    change q.gcd q = 1 at coprime
    rw [Nat.gcd_self] at coprime
    omega
  · rintro ⟨upper, coprime⟩
    exact ⟨upper.trans (Nat.lt_succ_self q), coprime⟩

theorem ramanujan_natural_gauss {q : ℕ} [NeZero q] (qLower : 1 < q) (k : ℕ) :
    ramanujan q (k : ℤ) = gaussSum (1 : DirichletCharacter ℂ q) (ZMod.stdAddChar.mulShift (k : ZMod q)) := by
  rw [ramanujan, numSet_eq_coprime_filter qLower, sum_filter, gaussSum_as_fraction_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [Int.cast_natCast, phase_eq_additivePhase, mul_div_assoc]
  by_cases coprime : a.Coprime q
  · rw [if_pos coprime, MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr coprime), one_mul]
  · rw [if_neg coprime, MulChar.map_nonunit _ (fun unit => coprime ((ZMod.isUnit_iff_coprime a q).mp unit)), zero_mul]

theorem ramanujan_moebius {q : ℕ} [NeZero q] (qLower : 1 < q) (k : ℕ) :
    ramanujan q (k : ℤ) = ∑ e ∈ q.divisors,
      moebiusComplex e * if (q / e) ∣ k then ((q / e : ℕ) : ℂ) else 0 := by
  rw [ramanujan_natural_gauss qLower]
  have lifted := sum_inducedGauss_moebius (one_dvd q) (1 : DirichletCharacter ℂ 1) k
  rw [DirichletCharacter.changeLevel_one] at lifted
  rw [lifted]
  have oneValue (m : ℕ) : (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 := by
    rw [Subsingleton.elim (m : ZMod 1) (1 : ZMod 1), map_one]
  refine sum_congr rfl fun e eMember => ?_
  have positive : 0 < q / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) (Nat.mem_divisors.mp eMember).1)
    (Nat.pos_of_mem_divisors eMember)
  letI : NeZero (q / e) := ⟨positive.ne'⟩
  simp only [oneValue, mul_one, one_mul, sum_phase_fraction_eq_if_dvd]

theorem norm_ramanujan_le_divisor_sum {q : ℕ} [NeZero q] (qLower : 1 < q) (k : ℕ) :
    ‖ramanujan q (k : ℤ)‖ ≤ ∑ e ∈ q.divisors,
      if (q / e) ∣ k then ((q / e : ℕ) : ℝ) else 0 := by
  rw [ramanujan_moebius qLower]
  refine (norm_sum_le _ _).trans (sum_le_sum fun e _ => ?_)
  by_cases divides : (q / e) ∣ k
  · simp only [if_pos divides, norm_mul, Complex.norm_natCast]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (norm_moebiusComplex_le_one e)
  · simp [divides]

theorem sum_multiples_weight (N d : ℕ) :
    (∑ x ∈ range (N + 1), if d ∣ x then (d : ℝ) else 0) ≤ (N : ℝ) + d := by
  have decompose : (range (N + 1)).filter (fun x => d ∣ x) =
      insert 0 ((range (N + 1)).filter (fun x => x ≠ 0 ∧ d ∣ x)) := by
    ext x
    by_cases zero : x = 0
    · subst x; simp
    · simp [zero]
  have count : ((range (N + 1)).filter (fun x => d ∣ x)).card = N / d + 1 := by
    rw [decompose, card_insert_of_notMem (by simp), Nat.card_multiples']
  rw [← sum_filter, sum_const, count, nsmul_eq_mul]
  exact_mod_cast (show (N / d + 1) * d ≤ N + d by rw [add_mul, one_mul]; exact Nat.add_le_add_right (Nat.div_mul_le_self N d) _)

theorem sum_norm_ramanujan_le {q : ℕ} [NeZero q] (qLower : 1 < q) (N : ℕ) :
    (∑ k ∈ range (N + 1), ‖ramanujan q (k : ℤ)‖) ≤ (q.divisors.card : ℝ) * ((N : ℝ) + q) := by
  calc
    _ ≤ ∑ k ∈ range (N + 1), ∑ e ∈ q.divisors, if (q / e) ∣ k then ((q / e : ℕ) : ℝ) else 0 :=
      sum_le_sum fun k _ => norm_ramanujan_le_divisor_sum qLower k
    _ = ∑ e ∈ q.divisors, ∑ k ∈ range (N + 1), if (q / e) ∣ k then ((q / e : ℕ) : ℝ) else 0 := sum_comm
    _ ≤ ∑ _ ∈ q.divisors, ((N : ℝ) + q) := by
      refine sum_le_sum fun e _ => (sum_multiples_weight N (q / e)).trans ?_
      exact add_le_add_right (by exact_mod_cast Nat.div_le_self q e) _
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem sum_norm_shifted_ramanujan_le {q : ℕ} [NeZero q] (qLower : 1 < q) (N : ℕ) :
    (∑ k ∈ range (N + 1), ‖ramanujan q ((k : ℤ) - (N : ℤ))‖) ≤
      (q.divisors.card : ℝ) * ((N : ℝ) + q) := by
  calc
    _ = ∑ k ∈ range (N + 1), ‖ramanujan q ((N - k : ℕ) : ℤ)‖ := by
      refine sum_congr rfl fun k membership => ?_
      have bound := Nat.le_of_lt_succ (mem_range.mp membership)
      rw [show (k : ℤ) - (N : ℤ) = -((N - k : ℕ) : ℤ) by rw [Nat.cast_sub bound, neg_sub], norm_ramanujan_neg]
    _ = ∑ k ∈ range (N + 1), ‖ramanujan q (k : ℤ)‖ := by
      simpa only [Nat.add_sub_cancel] using
        sum_range_reflect (fun k : ℕ => ‖ramanujan q (k : ℤ)‖) (N + 1)
    _ ≤ _ := sum_norm_ramanujan_le qLower N

end
end DyadicMixedB4Ramanujan

end

section

open Finset BombieriVinogradov.LargeSieve

namespace DyadicMixedB4RamanujanCharacters

noncomputable section

noncomputable local instance unitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

theorem unit_character_expansion {r : ℕ} [NeZero r] (F : (ZMod r)ˣ → ℂ) (b : (ZMod r)ˣ) :
    F b = (∑ χ : DirichletCharacter ℂ r,
      (∑ x : (ZMod r)ˣ, star (χ (x : ZMod r)) * F x) * χ (b : ZMod r)) / (r.totient : ℂ) := by
  classical
  have positive : 0 < r.totient := Nat.totient_pos.mpr (NeZero.pos r)
  have divisor : (r.totient : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  apply (eq_div_iff divisor).mpr
  symm
  calc
    _ = ∑ χ : DirichletCharacter ℂ r, ∑ x : (ZMod r)ˣ,
        F x * (star (χ (x : ZMod r)) * χ (b : ZMod r)) := by
      refine sum_congr rfl fun χ _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun x _ => by ring
    _ = ∑ x : (ZMod r)ˣ, ∑ χ : DirichletCharacter ℂ r,
        F x * (star (χ (x : ZMod r)) * χ (b : ZMod r)) := sum_comm
    _ = ∑ x : (ZMod r)ˣ, F x * (if x = b then (r.totient : ℂ) else 0) := by
      exact sum_congr rfl fun x _ => by rw [← mul_sum, characterOrthogonalityOnUnits]
    _ = _ := by simp [mul_ite]

set_option maxHeartbeats 600000 in
theorem unit_twisted_gauss {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (a v : (ZMod r)ˣ) :
    (∑ x : (ZMod r)ˣ, star (χ (x : ZMod r)) *
        ZMod.stdAddChar ((a : ZMod r) * (x : ZMod r) * (v : ZMod r))) =
      χ (a : ZMod r) * χ (v : ZMod r) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  calc
    _ = ∑ x : (ZMod r)ˣ, χ⁻¹ (x : ZMod r) *
        ZMod.stdAddChar (((a * v : (ZMod r)ˣ) : ZMod r) * (x : ZMod r)) := by
      refine sum_congr rfl fun x _ => ?_
      rw [MulChar.star_apply', Units.val_mul]
      rw [show (a : ZMod r) * (x : ZMod r) * (v : ZMod r) =
        ((a : ZMod r) * (v : ZMod r)) * (x : ZMod r) by ring]
    _ = ∑ x : ZMod r, χ⁻¹ x * ZMod.stdAddChar (((a * v : (ZMod r)ˣ) : ZMod r) * x) :=
      sum_units_eq_sum_residues χ⁻¹ (fun x : ZMod r => ZMod.stdAddChar (((a * v : (ZMod r)ˣ) : ZMod r) * x))
    _ = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (a * v : (ZMod r)ˣ)) := rfl
    _ = (χ⁻¹)⁻¹ ((a * v : (ZMod r)ˣ) : ZMod r) * gaussSum χ⁻¹ ZMod.stdAddChar :=
      gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar (a * v)
    _ = _ := by simp only [inv_inv, Units.val_mul, map_mul]

def twistedRamanujan {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (a b : (ZMod r)ˣ) : ℂ :=
  ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((a : ZMod r) * (b : ZMod r) * (ZMod.unitsMap divides u : ZMod r)) *
    ZMod.stdAddChar ((-(n : ZMod q)) * (u : ZMod q))

def characterFactor {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (χ : DirichletCharacter ℂ r) : ℂ :=
  gaussSum χ⁻¹ ZMod.stdAddChar *
    gaussSum (DirichletCharacter.changeLevel divides χ) (ZMod.stdAddChar.mulShift (-(n : ZMod q))) /
      (r.totient : ℂ)

theorem transform_twistedRamanujan {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (a : (ZMod r)ˣ) (χ : DirichletCharacter ℂ r) :
    (∑ b : (ZMod r)ˣ, star (χ (b : ZMod r)) * twistedRamanujan divides n a b) =
      χ (a : ZMod r) * gaussSum χ⁻¹ ZMod.stdAddChar *
        gaussSum (DirichletCharacter.changeLevel divides χ) (ZMod.stdAddChar.mulShift (-(n : ZMod q))) := by
  let lifted := DirichletCharacter.changeLevel divides χ
  have level (u : (ZMod q)ˣ) : χ (ZMod.unitsMap divides u : ZMod r) = lifted (u : ZMod q) := by
    rw [ZMod.unitsMap_val, ← DirichletCharacter.changeLevel_eq_cast_of_dvd]
  unfold twistedRamanujan
  simp_rw [mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ u : (ZMod q)ˣ, (∑ b : (ZMod r)ˣ, star (χ (b : ZMod r)) *
        ZMod.stdAddChar ((a : ZMod r) * (b : ZMod r) * (ZMod.unitsMap divides u : ZMod r))) *
          ZMod.stdAddChar ((-(n : ZMod q)) * (u : ZMod q)) := by
      refine sum_congr rfl fun u _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun b _ => by ring
    _ = (χ (a : ZMod r) * gaussSum χ⁻¹ ZMod.stdAddChar) *
        ∑ u : (ZMod q)ˣ, lifted (u : ZMod q) * ZMod.stdAddChar ((-(n : ZMod q)) * (u : ZMod q)) := by
      simp_rw [unit_twisted_gauss, level]
      rw [mul_sum]
      exact sum_congr rfl fun u _ => by ring
    _ = _ := by
      apply congrArg (fun z : ℂ => χ (a : ZMod r) * gaussSum χ⁻¹ ZMod.stdAddChar * z)
      exact sum_units_eq_sum_residues lifted (fun u : ZMod q => ZMod.stdAddChar ((-(n : ZMod q)) * u))

theorem twistedRamanujan_expansion {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (a b : (ZMod r)ˣ) :
    twistedRamanujan divides n a b = ∑ χ : DirichletCharacter ℂ r,
      characterFactor divides n χ * χ (a : ZMod r) * χ (b : ZMod r) := by
  rw [unit_character_expansion (twistedRamanujan divides n a) b]
  simp_rw [transform_twistedRamanujan, sum_div]
  refine sum_congr rfl fun χ _ => ?_
  unfold characterFactor
  ring

end
end DyadicMixedB4RamanujanCharacters

end

section

open Finset DyadicMixedB4GaussLift DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open BombieriVinogradov.LargeSieve DyadicMixedB4Ramanujan DyadicMixedB4RamanujanCharacters

namespace DyadicMixedB4RamanujanUnits

noncomputable section

noncomputable local instance unitFintype (q : ℕ) : Fintype (ZMod q)ˣ := Fintype.ofFinite _

theorem stdAddChar_int_fraction {q : ℕ} [NeZero q] (k : ℤ) :
    ZMod.stdAddChar (k : ZMod q) = additivePhase ((k : ℝ) / q) := by
  rw [ZMod.stdAddChar_coe, additivePhase, circleMap_zero, Complex.ofReal_one, one_mul]
  push_cast
  congr 1
  ring

theorem ramanujan_as_unit_sum {q : ℕ} [NeZero q] (qLower : 1 < q) (k : ℤ) :
    ramanujan q k = ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((k : ZMod q) * (u : ZMod q)) := by
  classical
  rw [ramanujan, numSet_eq_coprime_filter qLower]
  apply sum_bij (s := (range q).filter (fun a => a.Coprime q)) (t := (univ : Finset (ZMod q)ˣ))
    (fun a aMember => ZMod.unitOfCoprime a (mem_filter.mp aMember).2)
  · simp
  · intro a aMember b bMember equality
    have residues := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q).val) equality
    simpa only [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp aMember).1),
      Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp bMember).1)] using residues
  · intro u _
    let a := (u : ZMod q).val
    have raw : (a : ZMod q) = (u : ZMod q) := ZMod.natCast_zmod_val _
    have unit : IsUnit (a : ZMod q) := by rw [raw]; exact u.isUnit
    have aCoprime := (ZMod.isUnit_iff_coprime a q).mp unit
    refine ⟨a, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), aCoprime⟩, ?_⟩
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    exact raw
  · intro a aMember
    rw [ZMod.coe_unitOfCoprime, phase_eq_additivePhase]
    have product : (k : ZMod q) * (a : ZMod q) = ((k * (a : ℤ) : ℤ) : ZMod q) := by push_cast; rfl
    rw [product, stdAddChar_int_fraction]
    push_cast
    rw [mul_div_assoc]

theorem stdAddChar_rescale {r q : ℕ} [NeZero r] [NeZero q] (g m : ℕ) (scale : q = g * r) :
    ZMod.stdAddChar ((g * m : ℕ) : ZMod q) = ZMod.stdAddChar (m : ZMod r) := by
  have gNonzero : g ≠ 0 := by
    intro zero
    exact NeZero.ne q (by rw [scale, zero, zero_mul])
  have gCastNonzero : (g : ℝ) ≠ 0 := by exact_mod_cast gNonzero
  have rCastNonzero : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
  rw [stdAddChar_nat_fraction, stdAddChar_nat_fraction]
  congr 1
  rw [scale]
  push_cast
  field_simp

theorem twistedRamanujan_eq_ramanujan {r q : ℕ} [NeZero r] [NeZero q]
    (g : ℕ) (scale : q = g * r) (qLower : 1 < q) (divides : r ∣ q) (n : ℤ)
    (a b : (ZMod r)ˣ) (aRep bRep : ℕ)
    (aEq : (a : ZMod r) = (aRep : ZMod r)) (bEq : (b : ZMod r) = (bRep : ZMod r)) :
    twistedRamanujan divides n a b = ramanujan q (((g * aRep * bRep : ℕ) : ℤ) - n) := by
  rw [ramanujan_as_unit_sum qLower]
  unfold twistedRamanujan
  refine sum_congr rfl fun u _ => ?_
  let z := (u : ZMod q).val
  have zQ : (z : ZMod q) = (u : ZMod q) := ZMod.natCast_zmod_val _
  have zR : (z : ZMod r) = (ZMod.unitsMap divides u : ZMod r) := by
    rw [ZMod.unitsMap_val, ← zQ, ZMod.cast_natCast divides]
  have productR : (a : ZMod r) * (b : ZMod r) * (ZMod.unitsMap divides u : ZMod r) =
      ((aRep * bRep * z : ℕ) : ZMod r) := by simp only [aEq, bEq, ← zR, Nat.cast_mul]
  have productQ : ((g * aRep * bRep : ℕ) : ZMod q) * (u : ZMod q) =
      ((g * (aRep * bRep * z) : ℕ) : ZMod q) := by rw [← zQ]; push_cast; ring
  rw [Int.cast_sub, Int.cast_natCast, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, ← neg_mul,
    productQ, productR, stdAddChar_rescale g (aRep * bRep * z) scale]

end
end DyadicMixedB4RamanujanUnits

end

section

open Finset DyadicMixedB4ImprimitiveBound DyadicMixedB4RamanujanCharacters

namespace DyadicMixedB4CharacterFactorBound

noncomputable section

theorem norm_dirichlet_gauss_induced {r q : ℕ} [NeZero r] [NeZero q] (rDivides : r ∣ q)
    (χ : DirichletCharacter ℂ r) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel rDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod q))‖ ≤
      Real.sqrt χ.conductor * ∑ f ∈ k.divisors.filter (fun f => χ.conductor * f ∣ q), (f : ℝ) := by
  have conductorNonzero : χ.conductor ≠ 0 := fun zero => NeZero.ne r
    (DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mp zero)
  letI : NeZero χ.conductor := ⟨conductorNonzero⟩
  have inductionBound := norm_induced_gauss_le (χ.conductor_dvd_level.trans rDivides)
    χ.primitiveCharacter_isPrimitive k kPositive
  rw [DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level rDivides,
    DirichletCharacter.changeLevel_primitiveCharacter] at inductionBound
  exact inductionBound

theorem norm_dirichlet_gauss_standard {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt χ.conductor := by
  have induced := norm_dirichlet_gauss_induced (dvd_refl r) χ 1 (by decide)
  have onlyOne : ((1 : ℕ).divisors.filter (fun f => χ.conductor * f ∣ r)) = {1} := by
    ext f
    simp only [Nat.divisors_one, mem_filter, mem_singleton]
    constructor
    · exact And.left
    · rintro rfl
      exact ⟨rfl, by simpa only [mul_one] using χ.conductor_dvd_level⟩
  rw [onlyOne] at induced
  simpa [DirichletCharacter.changeLevel_self, AddChar.mulShift_one] using induced

theorem norm_gauss_neg_shift_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-x))‖ ≤ ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ := by
  have equality : ZMod.stdAddChar.mulShift (-x) =
      (ZMod.stdAddChar.mulShift x).mulShift ((-1 : (ZMod q)ˣ) : ZMod q) := by
    ext y
    simp [AddChar.mulShift_apply, mul_assoc]
  rw [equality, gaussSum_mulShift_eq χ (ZMod.stdAddChar.mulShift x) (-1), norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)

theorem characterFactor_bound {r q : ℕ} [NeZero r] [NeZero q] (rDivides : r ∣ q)
    (χ : DirichletCharacter ℂ r) (n : ℕ) (nPositive : 0 < n) :
    ‖characterFactor rDivides (n : ℤ) χ‖ ≤ (χ.conductor : ℝ) / (r.totient : ℝ) *
      ∑ f ∈ n.divisors.filter (fun f => χ.conductor * f ∣ q), (f : ℝ) := by
  let mass := ∑ f ∈ n.divisors.filter (fun f => χ.conductor * f ∣ q), (f : ℝ)
  let lifted := DirichletCharacter.changeLevel rDivides χ
  have first := norm_dirichlet_gauss_standard χ⁻¹
  rw [DirichletCharacter.conductor_inv] at first
  have second : ‖gaussSum lifted (ZMod.stdAddChar.mulShift (-(n : ZMod q)))‖ ≤
      Real.sqrt χ.conductor * mass :=
    (norm_gauss_neg_shift_le lifted (n : ZMod q)).trans
      (norm_dirichlet_gauss_induced rDivides χ n nPositive)
  unfold characterFactor
  rw [norm_div, norm_mul, Complex.norm_natCast, Int.cast_natCast]
  have numerator : ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖gaussSum lifted (ZMod.stdAddChar.mulShift (-(n : ZMod q)))‖ ≤
      (χ.conductor : ℝ) * mass := by
    calc
      _ ≤ Real.sqrt χ.conductor * (Real.sqrt χ.conductor * mass) :=
        mul_le_mul first second (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [← mul_assoc, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact (div_le_div_of_nonneg_right numerator (Nat.cast_nonneg _)).trans_eq (by unfold mass; ring)

end
end DyadicMixedB4CharacterFactorBound

end

section

open Finset ArithmeticFunction

namespace DyadicMixedB4BadPrimeMass

/-- Adapted from BadPrimePowerCover.lean in kimihiro64/bombieri-vinogradov,
revision 7a1748306e026825ed6a5555516cc2f28989b2ac (Apache-2.0). -/
theorem primePower_badUnit_cover {r b Y : ℕ} (rNonzero : r ≠ 0) (bBound : b ≤ Y)
    (bad : ¬b.Coprime r) (primePower : IsPrimePow b) :
    ∃ p ∈ r.primeFactors, ∃ k ∈ Icc 1 (Nat.log 2 Y), b = p ^ k := by
  obtain ⟨k, upper, positive, p, _, equality, prime⟩ := (isPrimePow_nat_iff_bounded_log b).mp primePower
  have divides : p ∣ r := by
    by_contra notDivides
    have pCoprime := prime.coprime_iff_not_dvd.mpr notDivides
    exact bad (equality ▸ pCoprime.pow_left k)
  exact ⟨p, Nat.mem_primeFactors.mpr ⟨prime, divides, rNonzero⟩,
    k, mem_Icc.mpr ⟨positive, upper.trans (Nat.log_mono_right bBound)⟩, equality⟩

theorem badUnit_mangoldt_mass_le (r Y : ℕ) (rNonzero : r ≠ 0) (YPositive : 0 < Y) :
    (∑ b ∈ (Icc 1 Y).filter (fun b => ¬b.Coprime r), Λ b) ≤
      (r.divisors.card : ℝ) * (Nat.log 2 Y : ℝ) * Real.log Y := by
  classical
  let bad := (Icc 1 Y).filter (fun b => ¬b.Coprime r)
  let support := bad.filter (fun b => Λ b ≠ 0)
  let codes := r.primeFactors ×ˢ Icc 1 (Nat.log 2 Y)
  have supportSubset : support ⊆ codes.image (fun pair : ℕ × ℕ => pair.1 ^ pair.2) := by
    intro b bMember
    obtain ⟨badMember, nonzero⟩ := mem_filter.mp bMember
    obtain ⟨inRange, noncoprime⟩ := mem_filter.mp badMember
    obtain ⟨p, pMember, k, kMember, equality⟩ := primePower_badUnit_cover rNonzero (mem_Icc.mp inRange).2
      noncoprime (vonMangoldt_ne_zero_iff.mp nonzero)
    exact mem_image.mpr ⟨(p, k), mem_product.mpr ⟨pMember, kMember⟩, equality.symm⟩
  have primeCount : r.primeFactors.card ≤ r.divisors.card := by
    apply card_le_card
    intro p pMember
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors pMember, rNonzero⟩
  have supportCount : support.card ≤ r.divisors.card * Nat.log 2 Y := by
    calc
      _ ≤ (codes.image (fun pair : ℕ × ℕ => pair.1 ^ pair.2)).card := card_le_card supportSubset
      _ ≤ codes.card := card_image_le
      _ = r.primeFactors.card * Nat.log 2 Y := by simp [codes]
      _ ≤ _ := Nat.mul_le_mul_right _ primeCount
  have logNonnegative : 0 ≤ Real.log Y := Real.log_nonneg (by exact_mod_cast YPositive)
  change (∑ b ∈ bad, Λ b) ≤ _
  calc
    _ = ∑ b ∈ support, Λ b := by
      symm
      exact sum_subset (filter_subset _ _) fun b member notSupport => by
        by_contra nz
        exact notSupport (mem_filter.mpr ⟨member, nz⟩)
    _ ≤ ∑ _ ∈ support, Real.log Y := by
      refine sum_le_sum fun b member => ?_
      obtain ⟨positive, upper⟩ := mem_Icc.mp (mem_filter.mp (mem_filter.mp member).1).1
      exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast positive) (by exact_mod_cast upper))
    _ = (support.card : ℝ) * Real.log Y := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast supportCount) logNonnegative

end DyadicMixedB4BadPrimeMass

end

section

open Finset ArithmeticFunction DyadicMixedB4ArcCenters DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss
open DyadicMixedB4RamanujanUnits DyadicMixedB4RamanujanCharacters DyadicMixedB4CharacterFactorBound
open DyadicMixedB4BadPrimeMass BombieriVinogradov.LargeSieve

namespace DyadicMixedB4RamanujanError

noncomputable section

theorem norm_stdAddChar_eq_one {q : ℕ} [NeZero q] (z : ZMod q) : ‖ZMod.stdAddChar z‖ = 1 := by
  rw [← ZMod.natCast_zmod_val z, stdAddChar_nat_fraction, norm_additivePhase]

theorem norm_ramanujan_le_modulus {q : ℕ} [NeZero q] (qLower : 1 < q) (k : ℤ) :
    ‖ramanujan q k‖ ≤ q := by
  rw [ramanujan_as_unit_sum qLower]
  refine (norm_sum_le _ _).trans ?_
  simpa only [norm_stdAddChar_eq_one, sum_const, nsmul_eq_mul, mul_one, card_univ,
    ZMod.card_units_eq_totient] using (show (q.totient : ℝ) ≤ q by exact_mod_cast Nat.totient_le q)

theorem norm_characterFactor_sum_le {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q)
    (n : ℕ) (nPositive : 0 < n) :
    (∑ χ : DirichletCharacter ℂ r, ‖characterFactor divides (n : ℤ) χ‖) ≤ (q : ℝ) * n.divisors.card := by
  have divisorPositive : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos r)
  have individually (χ : DirichletCharacter ℂ r) : ‖characterFactor divides (n : ℤ) χ‖ ≤
      ((q : ℝ) * (n.divisors.card : ℝ)) / (r.totient : ℝ) := by
    refine (characterFactor_bound divides χ n nPositive).trans ?_
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ divisorPositive.le
    rw [mul_sum]
    calc
      _ ≤ ∑ _ ∈ n.divisors.filter (fun f => χ.conductor * f ∣ q), (q : ℝ) := by
        refine sum_le_sum fun f member => ?_
        exact_mod_cast Nat.le_of_dvd (NeZero.pos q) (mem_filter.mp member).2
      _ ≤ ∑ _ ∈ n.divisors, (q : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg q)
      _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]
  have card : Fintype.card (DirichletCharacter ℂ r) = r.totient := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  calc
    _ ≤ ∑ _ : DirichletCharacter ℂ r, ((q : ℝ) * (n.divisors.card : ℝ)) / (r.totient : ℝ) :=
      sum_le_sum fun χ _ => individually χ
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul, card]; field_simp

def primitiveMixtureValue {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (a b : ℕ) : ℂ := ∑ χ : DirichletCharacter ℂ r, characterFactor divides n χ *
      χ.primitiveCharacter (a : ZMod χ.conductor) * χ.primitiveCharacter (b : ZMod χ.conductor)

theorem primitiveCharacter_equal_on_coprime {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    {a : ℕ} (coprime : a.Coprime r) : χ.primitiveCharacter (a : ZMod χ.conductor) = χ (a : ZMod r) := by
  calc
    _ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ.primitiveCharacter (a : ZMod r) := by
      rw [changeLevel_nat_indicator, if_pos coprime, one_mul]
    _ = _ := by rw [DirichletCharacter.changeLevel_primitiveCharacter]

theorem norm_primitiveMixtureValue_le {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q)
    (n : ℕ) (nPositive : 0 < n) (a b : ℕ) :
    ‖primitiveMixtureValue divides (n : ℤ) a b‖ ≤ (q : ℝ) * n.divisors.card := by
  unfold primitiveMixtureValue
  refine (norm_sum_le _ _).trans ((sum_le_sum ?_).trans (norm_characterFactor_sum_le divides n nPositive))
  intro χ _
  simp only [norm_mul]
  exact (mul_le_of_le_one_right (by positivity) (DirichletCharacter.norm_le_one _ _)).trans
    (mul_le_of_le_one_right (norm_nonneg _) (DirichletCharacter.norm_le_one _ _))

theorem ramanujan_eq_primitiveMixture_of_coprime {r q : ℕ} [NeZero r] [NeZero q] (g : ℕ)
    (scale : q = g * r) (qLower : 1 < q) (divides : r ∣ q) (n : ℤ) {a b : ℕ}
    (aCoprime : a.Coprime r) (bCoprime : b.Coprime r) :
    ramanujan q (((g * a * b : ℕ) : ℤ) - n) = primitiveMixtureValue divides n a b := by
  rw [← twistedRamanujan_eq_ramanujan g scale qLower divides n (ZMod.unitOfCoprime a aCoprime)
      (ZMod.unitOfCoprime b bCoprime) a b (ZMod.coe_unitOfCoprime a aCoprime) (ZMod.coe_unitOfCoprime b bCoprime),
    twistedRamanujan_expansion]
  simp only [primitiveMixtureValue, ZMod.coe_unitOfCoprime,
    primitiveCharacter_equal_on_coprime _ aCoprime, primitiveCharacter_equal_on_coprime _ bCoprime]

theorem norm_ramanujan_primitiveMixture_difference {r q : ℕ} [NeZero r] [NeZero q] (g : ℕ)
    (scale : q = g * r) (qLower : 1 < q) (divides : r ∣ q) (n : ℕ) (nPositive : 0 < n)
    {a : ℕ} (aCoprime : a.Coprime r) (b : ℕ) :
    ‖ramanujan q (((g * a * b : ℕ) : ℤ) - (n : ℤ)) - primitiveMixtureValue divides (n : ℤ) a b‖ ≤
      if b.Coprime r then 0 else (q : ℝ) * (1 + (n.divisors.card : ℝ)) := by
  by_cases bCoprime : b.Coprime r
  · rw [ramanujan_eq_primitiveMixture_of_coprime g scale qLower divides _ aCoprime bCoprime,
      sub_self, norm_zero, if_pos bCoprime]
  · rw [if_neg bCoprime, mul_add, mul_one]
    exact (norm_sub_le _ _).trans (add_le_add (norm_ramanujan_le_modulus qLower _)
      (norm_primitiveMixtureValue_le divides n nPositive a b))

end
end DyadicMixedB4RamanujanError

end

section

open Finset ArithmeticFunction DyadicMixedB4RamanujanError DyadicMixedB4BadPrimeMass
open DyadicMixedB4ArcCenters

namespace DyadicMixedB4PrimitiveAt

noncomputable section

def reducedModulus (q a : ℕ) : ℕ := q / a.gcd q

theorem gcd_positive {q : ℕ} (qPositive : 0 < q) (a : ℕ) : 0 < a.gcd q :=
  Nat.gcd_pos_of_pos_right a qPositive

theorem reducedModulus_positive {q : ℕ} (qPositive : 0 < q) (a : ℕ) : 0 < reducedModulus q a :=
  Nat.div_pos (Nat.le_of_dvd qPositive (Nat.gcd_dvd_right a q)) (gcd_positive qPositive a)

theorem reducedModulus_dvd (q a : ℕ) : reducedModulus q a ∣ q :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a q)

def primitiveAt (q n a b : ℕ) : ℂ :=
  if h : 0 < q then
    letI : NeZero q := ⟨h.ne'⟩
    letI : NeZero (reducedModulus q a) := ⟨(reducedModulus_positive h a).ne'⟩
    primitiveMixtureValue (reducedModulus_dvd q a) (n : ℤ) (a / a.gcd q) b
  else 0

theorem norm_ramanujan_sub_primitiveAt {q n : ℕ} (qLower : 1 < q) (nPositive : 0 < n) (a b : ℕ) :
    ‖ramanujan q (((a * b : ℕ) : ℤ) - (n : ℤ)) - primitiveAt q n a b‖ ≤
      if b.Coprime (reducedModulus q a) then 0 else (q : ℝ) * (1 + (n.divisors.card : ℝ)) := by
  have qPositive : 0 < q := by omega
  letI : NeZero q := ⟨qPositive.ne'⟩
  letI : NeZero (reducedModulus q a) := ⟨(reducedModulus_positive qPositive a).ne'⟩
  have gPositive := gcd_positive qPositive a
  have scale : q = a.gcd q * reducedModulus q a := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a q)).symm
  have coprime : (a / a.gcd q).Coprime (reducedModulus q a) := Nat.coprime_div_gcd_div_gcd gPositive
  rw [primitiveAt, dif_pos qPositive]
  have bound := norm_ramanujan_primitiveMixture_difference (a.gcd q) scale qLower (reducedModulus_dvd q a)
    n nPositive coprime b
  rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_left a q)] at bound

theorem norm_mangoldt_replacement_le {q n : ℕ} (qLower : 1 < q) (nPositive : 0 < n)
    (a : ℕ) (s : Finset ℕ) (within : s ⊆ Icc 1 n) (K : ℕ → ℂ)
    {V : ℝ} (vNonnegative : 0 ≤ V) (KBound : ∀ b ∈ s, ‖K b‖ ≤ V) :
    ‖∑ b ∈ s, (Λ b : ℂ) * ((ramanujan q (((a * b : ℕ) : ℤ) - (n : ℤ)) - primitiveAt q n a b) * K b)‖ ≤
      (V * ((q : ℝ) * (1 + (n.divisors.card : ℝ)))) *
        (((reducedModulus q a).divisors.card : ℝ) * (Nat.log 2 n : ℝ) * Real.log n) := by
  let r := reducedModulus q a
  let C : ℝ := V * ((q : ℝ) * (1 + (n.divisors.card : ℝ)))
  let f (b : ℕ) := (Λ b : ℂ) * ((ramanujan q (((a * b : ℕ) : ℤ) - (n : ℤ)) - primitiveAt q n a b) * K b)
  have qPositive : 0 < q := by omega
  have rNonzero : r ≠ 0 := (reducedModulus_positive qPositive a).ne'
  have CNonnegative : 0 ≤ C := by unfold C; positivity
  change ‖∑ b ∈ s, f b‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ b ∈ s, if b.Coprime r then 0 else Λ b * C := by
      refine sum_le_sum fun b bMember => ?_
      have difference := norm_ramanujan_sub_primitiveAt qLower nPositive a b
      change _ ≤ if b.Coprime r then 0 else _ at difference
      by_cases coprime : b.Coprime r
      · rw [if_pos coprime] at difference ⊢
        have zero := norm_eq_zero.mp (le_antisymm difference (norm_nonneg _))
        unfold f
        rw [zero, zero_mul, mul_zero, norm_zero]
      · rw [if_neg coprime] at difference ⊢
        unfold f C
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
        rw [mul_comm V]
        exact mul_le_mul_of_nonneg_left (mul_le_mul difference (KBound b bMember) (norm_nonneg _) (by positivity))
          vonMangoldt_nonneg
    _ = ∑ b ∈ s.filter (fun b => ¬b.Coprime r), Λ b * C := by
      rw [sum_filter]
      exact sum_congr rfl fun b _ => by by_cases coprime : b.Coprime r <;> simp [coprime]
    _ ≤ ∑ b ∈ (Icc 1 n).filter (fun b => ¬b.Coprime r), Λ b * C :=
      sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ within) (fun _ _ _ => mul_nonneg vonMangoldt_nonneg CNonnegative)
    _ = C * ∑ b ∈ (Icc 1 n).filter (fun b => ¬b.Coprime r), Λ b := by rw [← sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (badUnit_mangoldt_mass_le r n rNonzero nPositive) CNonnegative

end
end DyadicMixedB4PrimitiveAt

end

section

open Finset BombieriVinogradov.LargeSieve

namespace DyadicMixedB4ConductorPartition

noncomputable section

theorem sum_at_conductor {A : Type*} [AddCommMonoid A] {r d : ℕ} [NeZero r] (divides : d ∣ r)
    (F : DirichletCharacter ℂ r → A) :
    (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ r => χ.conductor = d), F χ) =
      ∑ ψ ∈ primitiveCharacters d, F (DirichletCharacter.changeLevel divides ψ) := by
  classical
  symm
  apply sum_bij (s := primitiveCharacters d) (t := univ.filter (fun χ : DirichletCharacter ℂ r => χ.conductor = d))
    (fun ψ _ => DirichletCharacter.changeLevel divides ψ)
  · intro ψ membership
    have primitive : ψ.IsPrimitive := (mem_filter.mp membership).2
    exact mem_filter.mpr ⟨mem_univ _, (DirichletCharacter.conductor_changeLevel ψ divides).trans primitive⟩
  · intro χ _ ψ _ equality
    exact DirichletCharacter.changeLevel_injective divides equality
  · intro χ membership
    have equality := (mem_filter.mp membership).2
    subst d
    exact ⟨χ.primitiveCharacter, mem_filter.mpr ⟨mem_univ _, χ.primitiveCharacter_isPrimitive⟩,
      χ.changeLevel_primitiveCharacter⟩
  · intro ψ _
    rfl

theorem sum_conductor_partition {A : Type*} [AddCommMonoid A] {r : ℕ} [NeZero r]
    (F : DirichletCharacter ℂ r → A) :
    (∑ χ : DirichletCharacter ℂ r, F χ) =
      ∑ d ∈ r.divisors.attach, ∑ ψ ∈ primitiveCharacters d.1,
        F (DirichletCharacter.changeLevel (Nat.mem_divisors.mp d.2).1 ψ) := by
  classical
  have conductorMembership (χ : DirichletCharacter ℂ r) (_ : χ ∈ (univ : Finset (DirichletCharacter ℂ r))) :
      χ.conductor ∈ r.divisors := Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne r⟩
  calc
    _ = ∑ d ∈ r.divisors, ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ r => χ.conductor = d), F χ :=
      (sum_fiberwise_of_maps_to conductorMembership F).symm
    _ = ∑ d ∈ r.divisors.attach, ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ r => χ.conductor = d.1), F χ :=
      (sum_attach _ _).symm
    _ = _ := sum_congr rfl fun d _ => sum_at_conductor (Nat.mem_divisors.mp d.2).1 F

end
end DyadicMixedB4ConductorPartition

end

section

open Finset DyadicMixedB4PrimitiveAt DyadicMixedB4RamanujanError DyadicMixedB4RamanujanCharacters
open BombieriVinogradov.LargeSieve DyadicMixedB4ConductorPartition
open DyadicMixedB4CharacterFactorBound

namespace DyadicMixedB4PrimitiveExpansion

noncomputable section

theorem primitiveCharacter_of_primitive_at {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (primitive : χ.IsPrimitive) (b : ℕ) : χ.primitiveCharacter (b : ZMod χ.conductor) = χ (b : ZMod d) := by
  by_cases coprime : b.Coprime d
  · exact primitiveCharacter_equal_on_coprime χ coprime
  · have conductor : χ.conductor = d := primitive
    have inducedNonunit : ¬IsUnit (b : ZMod χ.conductor) := by
      intro unit
      have inducedCoprime := (ZMod.isUnit_iff_coprime b χ.conductor).mp unit
      exact coprime (by simpa only [conductor] using inducedCoprime)
    have nonunit : ¬IsUnit (b : ZMod d) := fun unit => coprime ((ZMod.isUnit_iff_coprime b d).mp unit)
    rw [MulChar.map_nonunit _ inducedNonunit, MulChar.map_nonunit _ nonunit]

theorem primitiveCharacter_of_lift_at {r d : ℕ} [NeZero r] [NeZero d] (divides : d ∣ r)
    {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) (b : ℕ) :
    (DirichletCharacter.changeLevel divides χ).primitiveCharacter
      (b : ZMod (DirichletCharacter.changeLevel divides χ).conductor) = χ (b : ZMod d) := by
  have transport := DirichletCharacter.primitiveCharacter_changeLevel_apply divides χ (b : ℤ)
  simp only [Int.cast_natCast] at transport
  exact transport.trans (primitiveCharacter_of_primitive_at primitive b)

theorem primitiveMixtureValue_expansion {r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q) (n : ℤ)
    (a b : ℕ) : primitiveMixtureValue divides n a b =
      ∑ d ∈ r.divisors.attach, ∑ χ ∈ primitiveCharacters d.1,
        characterFactor divides n (DirichletCharacter.changeLevel (Nat.mem_divisors.mp d.2).1 χ) *
          χ (a : ZMod d.1) * χ (b : ZMod d.1) := by
  classical
  unfold primitiveMixtureValue
  rw [sum_conductor_partition (F := fun χ : DirichletCharacter ℂ r => characterFactor divides n χ *
    χ.primitiveCharacter (a : ZMod χ.conductor) * χ.primitiveCharacter (b : ZMod χ.conductor))]
  refine sum_congr rfl fun d _ => sum_congr rfl fun χ χMember => ?_
  have primitive : χ.IsPrimitive := (mem_filter.mp χMember).2
  letI : NeZero d.1 := ⟨(Nat.pos_of_mem_divisors d.2).ne'⟩
  rw [primitiveCharacter_of_lift_at _ primitive a, primitiveCharacter_of_lift_at _ primitive b]

theorem lift_characterFactor_bound {d r q : ℕ} [NeZero r] [NeZero q] (divides : r ∣ q)
    (levelDivides : d ∣ r) (χ : DirichletCharacter ℂ d) (primitive : χ.IsPrimitive) (n : ℕ) (nPositive : 0 < n) :
    ‖characterFactor divides (n : ℤ) (DirichletCharacter.changeLevel levelDivides χ)‖ ≤
      (d : ℝ) / (r.totient : ℝ) * ∑ f ∈ n.divisors.filter (fun f => d * f ∣ q), (f : ℝ) := by
  have conductor : χ.conductor = d := primitive
  simpa only [DirichletCharacter.conductor_changeLevel, conductor] using
    characterFactor_bound divides (DirichletCharacter.changeLevel levelDivides χ) n nPositive

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

theorem gcd_reciprocal_sum_le (L : ℕ) (LPositive : 0 < L) :
    (∑ u ∈ Icc 1 L, ∑ v ∈ Icc 1 L, (u.gcd v : ℝ) / ((u : ℝ) * v)) ≤
      (1 + Real.log L) ^ 3 := by
  classical
  let support := Icc 1 L
  let row (d u : ℕ) : ℝ := if d ∣ u then (u : ℝ)⁻¹ else 0
  let H := 1 + Real.log (L : ℝ)
  have HNonnegative : 0 ≤ H := by
    have LReal : (1 : ℝ) ≤ L := by exact_mod_cast LPositive
    unfold H
    exact add_nonneg zero_le_one (Real.log_nonneg LReal)
  have rowNonnegative (d u : ℕ) : 0 ≤ row d u := by unfold row; split_ifs <;> positivity
  have pointwise (u v : ℕ) (uMember : u ∈ support) (vMember : v ∈ support) :
      (u.gcd v : ℝ) / ((u : ℝ) * v) ≤ ∑ d ∈ support, (d : ℝ) * row d u * row d v := by
    have uPositive := (mem_Icc.mp uMember).1
    have gPositive := Nat.gcd_pos_of_pos_left v uPositive
    have gMember : u.gcd v ∈ support := mem_Icc.mpr ⟨gPositive, (Nat.gcd_le_left v uPositive).trans (mem_Icc.mp uMember).2⟩
    calc
      _ = (u.gcd v : ℝ) * row (u.gcd v) u * row (u.gcd v) v := by
        have uNonzero : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt uPositive)
        have vNonzero : (v : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp vMember).1)
        simp only [row, if_pos (Nat.gcd_dvd_left u v), if_pos (Nat.gcd_dvd_right u v)]
        field_simp
      _ ≤ _ := single_le_sum (s := support) (f := fun (d : ℕ) => (d : ℝ) * row d u * row d v) (fun d _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (rowNonnegative d u)) (rowNonnegative d v)) gMember
  have rowBound (d : ℕ) (member : d ∈ support) : (∑ u ∈ support, row d u) ≤ (d : ℝ)⁻¹ * H := by
    have dPositive := (mem_Icc.mp member).1
    change (∑ u ∈ Icc 1 L, if d ∣ u then (u : ℝ)⁻¹ else 0) ≤ _
    rw [← sum_filter, sum_inverse_multiples d L dPositive]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self L d))
      (fun _ _ _ => by positivity)).trans ?_
    exact sum_inverse_Icc_le L
  calc
    _ ≤ ∑ u ∈ support, ∑ v ∈ support, ∑ d ∈ support, (d : ℝ) * row d u * row d v :=
      sum_le_sum fun u uMember => sum_le_sum fun v vMember => pointwise u v uMember vMember
    _ = ∑ d ∈ support, (d : ℝ) * (∑ u ∈ support, row d u) ^ 2 := by
      have swapped : (∑ u ∈ support, ∑ v ∈ support, ∑ d ∈ support, (d : ℝ) * row d u * row d v) =
          ∑ d ∈ support, ∑ u ∈ support, ∑ v ∈ support, (d : ℝ) * row d u * row d v := by
        calc
          _ = ∑ u ∈ support, ∑ d ∈ support, ∑ v ∈ support, (d : ℝ) * row d u * row d v :=
            sum_congr rfl fun _ _ => sum_comm
          _ = _ := sum_comm
      rw [swapped]
      refine sum_congr rfl fun d _ => ?_
      calc
        _ = ∑ u ∈ support, ((d : ℝ) * row d u) * (∑ v ∈ support, row d v) :=
          sum_congr rfl fun _ _ => (mul_sum _ _ _).symm
        _ = (∑ u ∈ support, (d : ℝ) * row d u) * (∑ v ∈ support, row d v) :=
          (sum_mul _ _ _).symm
        _ = _ := by rw [← mul_sum, mul_assoc, pow_two]
    _ ≤ ∑ d ∈ support, (d : ℝ)⁻¹ * H ^ 2 := by
      refine sum_le_sum fun d member => ?_
      have dRealPositive : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp member).1
      have energy := pow_le_pow_left₀ (sum_nonneg fun u _ => rowNonnegative d u) (rowBound d member) 2
      calc
        _ ≤ (d : ℝ) * ((d : ℝ)⁻¹ * H) ^ 2 := mul_le_mul_of_nonneg_left energy dRealPositive.le
        _ = _ := by field_simp
    _ = (∑ d ∈ support, (d : ℝ)⁻¹) * H ^ 2 := by rw [sum_mul]
    _ ≤ H ^ 3 := by
      calc
        _ ≤ H * H ^ 2 := mul_le_mul_of_nonneg_right (sum_inverse_Icc_le L) (sq_nonneg _)
        _ = _ := by ring

end DyadicMixedB4GcdHarmonic

end

section

open Finset DyadicMixedB4GcdHarmonic

namespace DyadicMixedB4WeightBudgets

theorem le_totient_mul_divisor_count (n : ℕ) (nPositive : 0 < n) :
    n ≤ n.totient * n.divisors.card := by
  let product : ℕ := ∏ p ∈ n.primeFactors, (p - 1)
  have productPositive : 0 < product := by
    unfold product
    exact prod_pos (s := n.primeFactors) (f := fun p : ℕ => p - 1)
      (fun p membership => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors membership).one_lt)
  have bound : (∏ p ∈ n.primeFactors, p) ≤ n.divisors.card * product := by
    calc
      _ ≤ ∏ p ∈ n.primeFactors, (n.factorization p + 1) * (p - 1) := by
        refine prod_le_prod' fun p membership => ?_
        have pLower := (Nat.prime_of_mem_primeFactors membership).two_le
        have exponent := Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization] : p ∈ n.factorization.support)
        calc
          p ≤ 2 * (p - 1) := by omega
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [prod_mul_distrib, Nat.card_divisors nPositive.ne']
  apply Nat.le_of_mul_le_mul_right _ productPositive
  calc
    n * product = n.totient * ∏ p ∈ n.primeFactors, p := (Nat.totient_mul_prod_primeFactors n).symm
    _ ≤ n.totient * (n.divisors.card * product) := Nat.mul_le_mul_left _ bound
    _ = _ := by ring

theorem inverse_totient_le_divisor_count (n : ℕ) (nPositive : 0 < n) :
    1 / (n.totient : ℝ) ≤ (n.divisors.card : ℝ) / (n : ℝ) := by
  have positive : (0 : ℝ) < n := by exact_mod_cast nPositive
  have phiPositive : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr nPositive
  exact (div_le_div_iff₀ phiPositive positive).mpr (by
    simpa only [one_mul, mul_one, mul_comm] using (show (n : ℝ) ≤ (n.totient : ℝ) * (n.divisors.card : ℝ) by
      exact_mod_cast le_totient_mul_divisor_count n nPositive))

theorem step_multiple_weight_le {ι : Type*} (items : Finset ι) (g : ι → ℕ) (w : ι → ℝ)
    (M q : ℕ) (qPositive : 0 < q) {W : ℝ} (WNonnegative : 0 ≤ W)
    (stepRange : ∀ i ∈ items, g i ∈ Icc 1 M)
    (weightBound : ∀ u ∈ Icc 1 M, (∑ i ∈ items.filter (fun i => g i = u), w i) ≤ W) :
    (∑ i ∈ items, if q ∣ g i then w i / (g i : ℝ) else 0) ≤
      W * (q : ℝ)⁻¹ * (1 + Real.log M) := by
  have fibre (u : ℕ) : (∑ i ∈ items.filter (fun i => g i = u), if q ∣ g i then w i / (g i : ℝ) else 0) =
      if q ∣ u then (∑ i ∈ items.filter (fun i => g i = u), w i) / (u : ℝ) else 0 := by
    by_cases divides : q ∣ u
    · rw [if_pos divides, sum_div]
      exact sum_congr rfl fun i member => by simp [(mem_filter.mp member).2, divides]
    · rw [if_neg divides]
      exact sum_eq_zero fun i member => by simp [(mem_filter.mp member).2, divides]
  calc
    _ = ∑ u ∈ Icc 1 M, ∑ i ∈ items.filter (fun i => g i = u), if q ∣ g i then w i / (g i : ℝ) else 0 :=
      (sum_fiberwise_of_maps_to stepRange _).symm
    _ = ∑ u ∈ Icc 1 M, if q ∣ u then (∑ i ∈ items.filter (fun i => g i = u), w i) / (u : ℝ) else 0 :=
      sum_congr rfl fun u _ => fibre u
    _ ≤ ∑ u ∈ Icc 1 M, if q ∣ u then W * (u : ℝ)⁻¹ else 0 := by
      refine sum_le_sum fun u member => ?_
      by_cases divides : q ∣ u
      · rw [if_pos divides, if_pos divides, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (weightBound u member) (by positivity)
      · simp [divides]
    _ = W * ((q : ℝ)⁻¹ * ∑ j ∈ Icc 1 (M / q), (j : ℝ)⁻¹) := by
      rw [← sum_filter, ← mul_sum, sum_inverse_multiples q M qPositive]
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self M q))
        (fun _ _ _ => by positivity)).trans (sum_inverse_Icc_le M)

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

def primitiveBlock (n M B H q step lo hi U : ℕ) (indices : Finset ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ a ∈ indices, w a * ∑ b ∈ Ioc U (n / a), (Λ b : ℂ) * (primitiveAt q n a b *
    (windowKernel n M B H q step lo hi (((a * b : ℕ) : ℤ) - (n : ℤ) : ℝ) : ℂ))

def conductorBlock {r q : ℕ} [NeZero r] [NeZero q] (qr : r ∣ q)
    (n M B H step lo hi U g : ℕ) (indices : Finset ℕ) (w : ℕ → ℂ) (d : r.divisors) : ℂ :=
  ∑ a ∈ indices, w a * ∑ j ∈ range (n / a), windowKernel n M B H q step lo hi
    ((a : ℝ) * ((j : ℝ) + 1) - n) • mixture (primitiveCharacters d.1) (mangoldtAbove U)
      (fun χ => characterFactor qr (n : ℤ) (DirichletCharacter.changeLevel (Nat.mem_divisors.mp d.2).1 χ))
      (a / g) j

theorem primitiveBlock_eq_sum_conductorBlock {q g : ℕ} [NeZero q] [NeZero (q / g)] (gq : g ∣ q)
    (n M B H step lo hi U : ℕ) (indices : Finset ℕ) (w : ℕ → ℂ)
    (gcdExact : ∀ a ∈ indices, a.gcd q = g) :
    primitiveBlock n M B H q step lo hi U indices w =
      ∑ d ∈ (q / g).divisors.attach, conductorBlock (Nat.div_dvd_of_dvd gq) n M B H step lo hi U g indices w d := by
  classical
  have qPositive : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let r := q / g
  let qr : r ∣ q := Nat.div_dvd_of_dvd gq
  let coeff (d : r.divisors) (χ : DirichletCharacter ℂ d.1) :=
    characterFactor qr (n : ℤ) (DirichletCharacter.changeLevel (Nat.mem_divisors.mp d.2).1 χ)
  have point (a : ℕ) (member : a ∈ indices) (b : ℕ) :
      primitiveAt q n a b = ∑ d ∈ r.divisors.attach,
        ∑ χ ∈ primitiveCharacters d.1, coeff d χ * χ ((a / g : ℕ) : ZMod d.1) * χ (b : ZMod d.1) := by
    have same := gcdExact a member
    subst g
    unfold primitiveAt
    rw [dif_pos qPositive]
    letI : NeZero (reducedModulus q a) := ⟨(reducedModulus_positive qPositive a).ne'⟩
    exact primitiveMixtureValue_expansion (reducedModulus_dvd q a) (n : ℤ) (a / a.gcd q) b
  unfold primitiveBlock conductorBlock
  rw [sum_comm]
  refine sum_congr rfl fun a member => ?_
  rw [← mul_sum, sum_Ioc_as_range_prefix, sum_comm]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  by_cases bLarge : U < j + 1
  · simp only [if_pos bLarge, point a member, Complex.real_smul, mixture, mangoldtAbove,
      Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [mul_sum, sum_mul]
    refine sum_congr rfl fun (d : r.divisors) _ => ?_
    refine sum_congr rfl fun (χ : DirichletCharacter ℂ d.1) _ => ?_
    unfold coeff
    ring
  · simp [bLarge, mixture, mangoldtAbove]

theorem norm_conductorBlock_le {q g : ℕ} [NeZero q] [NeZero (q / g)] (gq : g ∣ q)
    (n M B H step lo hi U A : ℕ) (nPositive : 0 < n) (APositive : 0 < A)
    (gPositive : 0 < g) (radiusUpper : radius M ≤ 1) (indices : Finset ℕ)
    (indexRange : indices ⊆ Ico A (2 * A)) (gcdExact : ∀ a ∈ indices, a.gcd q = g)
    (w : ℕ → ℂ) {T : ℝ} (TNonnegative : 0 ≤ T)
    (wBound : ∀ a ∈ indices, ‖w a‖ ≤ T) (dCount : (((q / g).divisors.card : ℕ) : ℝ) ≤ T)
    (d : (q / g).divisors) :
    ‖conductorBlock (Nat.div_dvd_of_dvd gq) n M B H step lo hi U g indices w d‖ ≤
      (T ^ 2 * (16 + 24 * Real.log ((n : ℝ) + 1)) / (step : ℝ)) *
        (∑ f ∈ n.divisors, if d.1 * f ∣ q then ((d.1 : ℝ) * g * f) / (q : ℝ) else 0) *
          blockEnergy n A U g d.1 := by
  classical
  let r := q / g
  let qr : r ∣ q := Nat.div_dvd_of_dvd gq
  let F := ∑ f ∈ n.divisors.filter (fun f => d.1 * f ∣ q), (f : ℝ)
  have FNonnegative : 0 ≤ F := sum_nonneg fun f _ => Nat.cast_nonneg f
  have CNonnegative : 0 ≤ (d.1 : ℝ) / (r.totient : ℝ) * F := by positivity
  letI : NeZero d.1 := ⟨(Nat.pos_of_mem_divisors d.2).ne'⟩
  have rPositive : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have weight (χ : DirichletCharacter ℂ d.1) (member : χ ∈ primitiveCharacters d.1) :
      ‖characterFactor qr (n : ℤ) (DirichletCharacter.changeLevel (Nat.mem_divisors.mp d.2).1 χ)‖ ≤
        (d.1 : ℝ) / (r.totient : ℝ) * F :=
    lift_characterFactor_bound qr _ χ (mem_filter.mp member).2 n nPositive
  have bound := fixed_conductor_block_le (d := d.1) n M B H q step lo hi A g U nPositive APositive
    gPositive radiusUpper indices indexRange (fun a member => gcdExact a member ▸ Nat.gcd_dvd_left a q)
    w TNonnegative CNonnegative wBound (primitiveCharacters d.1) _ weight
  dsimp only at bound
  simp only [finiteTwistedSum_eq_primitiveEnergy] at bound
  have rExact : (r : ℝ) * (g : ℝ) = (q : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel gq
  have rNonzero : (r : ℝ) ≠ 0 := by exact_mod_cast rPositive.ne'
  have gNonzero : (g : ℝ) ≠ 0 := by exact_mod_cast gPositive.ne'
  have phiBound : 1 / (r.totient : ℝ) ≤ T * g / (q : ℝ) := by
    calc
      _ ≤ (r.divisors.card : ℝ) / (r : ℝ) := inverse_totient_le_divisor_count r rPositive
      _ ≤ T / (r : ℝ) := div_le_div_of_nonneg_right dCount (Nat.cast_nonneg _)
      _ = _ := by rw [← rExact]; field_simp
  have coefBound : (d.1 : ℝ) / (r.totient : ℝ) * F ≤
      (d.1 : ℝ) * (T * g / (q : ℝ)) * F := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left phiBound (Nat.cast_nonneg _)) FNonnegative
  have factor : 0 ≤ (16 / (step : ℝ) + 24 / (step : ℝ) * Real.log ((n : ℝ) + 1)) :=
    (add_nonneg (by positivity) (mul_nonneg (by positivity)
      (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))))
  calc
    _ ≤ T * (16 / (step : ℝ) + 24 / (step : ℝ) * Real.log ((n : ℝ) + 1)) *
        ((d.1 : ℝ) / (r.totient : ℝ) * F) * blockEnergy n A U g d.1 := bound
    _ ≤ T * (16 / (step : ℝ) + 24 / (step : ℝ) * Real.log ((n : ℝ) + 1)) *
        ((d.1 : ℝ) * (T * g / (q : ℝ)) * F) * blockEnergy n A U g d.1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left coefBound (mul_nonneg TNonnegative factor))
        (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← sum_filter]
      simp_rw [mul_div_assoc (↑d.1 * (g : ℝ))]
      rw [← mul_sum, ← sum_div]
      unfold F
      ring

end
end DyadicMixedB4BilinearBlock

end

section

open Finset

namespace DyadicMixedB4ModulusTail

private theorem reciprocal_telescoping (A length : ℕ) :
    (∑ i ∈ range length, (1 / ((A + i : ℕ) : ℝ) - 1 / ((A + i + 1 : ℕ) : ℝ))) =
      1 / (A : ℝ) - 1 / ((A + length : ℕ) : ℝ) := by
  induction length with
  | zero => simp
  | succ length ih => rw [sum_range_succ, ih, ← add_assoc]; ring

theorem inverse_square_tail_Icc (A L : ℕ) (APositive : 0 < A) :
    (∑ k ∈ Icc A L, 1 / (k : ℝ) ^ 2) ≤ 2 / (A : ℝ) := by
  rw [show Icc A L = Ico A (L + 1) by ext k; simp only [mem_Icc, mem_Ico]; omega,
    sum_Ico_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ range (L + 1 - A), 2 * (1 / ((A + i : ℕ) : ℝ) - 1 / ((A + i + 1 : ℕ) : ℝ)) := by
      refine sum_le_sum fun i _ => ?_
      have lower : (1 : ℝ) ≤ ((A + i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ A + i by omega)
      let z : ℝ := ((A + i : ℕ) : ℝ)
      have zLower : 1 ≤ z := lower
      have positive : 0 < z := by linarith only [zLower]
      have nextPositive : 0 < z + 1 := by linarith only [zLower]
      rw [Nat.cast_add (A + i) 1, Nat.cast_one]
      change 1 / z ^ 2 ≤ 2 * (1 / z - 1 / (z + 1))
      field_simp
      nlinarith only [zLower, mul_nonneg (by linarith only [zLower] : 0 ≤ z - 1) positive.le]
    _ = 2 * (1 / (A : ℝ) - 1 / ((A + (L + 1 - A) : ℕ) : ℝ)) := by rw [← mul_sum, reciprocal_telescoping]
    _ ≤ _ := by
      have denomNonnegative : (0 : ℝ) ≤ 1 / ((A + (L + 1 - A) : ℕ) : ℝ) := by positivity
      calc
        _ ≤ 2 * (1 / (A : ℝ)) := mul_le_mul_of_nonneg_left (sub_le_self _ denomNonnegative) (by norm_num)
        _ = _ := by ring

theorem inverse_square_multiples_tail (D R L : ℕ) (DPositive : 0 < D) :
    (∑ q ∈ (Icc (R + 1) L).filter (fun q => D ∣ q), 1 / (q : ℝ) ^ 2) ≤
      2 / ((D : ℝ) * (max R D : ℕ)) := by
  let A := R / D + 1
  have APositive : 0 < A := Nat.zero_lt_succ _
  have DRealPositive : (0 : ℝ) < D := by exact_mod_cast DPositive
  have equality : (∑ q ∈ (Icc (R + 1) L).filter (fun q => D ∣ q), 1 / (q : ℝ) ^ 2) =
      (1 / (D : ℝ) ^ 2) * ∑ k ∈ Icc A (L / D), 1 / (k : ℝ) ^ 2 := by
    rw [mul_sum]
    symm
    apply sum_bij (s := Icc A (L / D)) (t := (Icc (R + 1) L).filter (fun q => D ∣ q))
      (fun k _ => D * k)
    · intro k membership
      obtain ⟨lower, upper⟩ := mem_Icc.mp membership
      have iLower : R / D < k := lower
      have lowerProd : R < k * D := (Nat.div_lt_iff_lt_mul DPositive).mp iLower
      have upperProd : k * D ≤ L := (Nat.le_div_iff_mul_le DPositive).mp upper
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by simpa only [Nat.mul_comm] using Nat.succ_le_of_lt lowerProd,
        by simpa only [Nat.mul_comm] using upperProd⟩, dvd_mul_right _ _⟩
    · intro k _ k' _ same
      exact Nat.eq_of_mul_eq_mul_left DPositive same
    · intro q membership
      obtain ⟨interval, k, identity⟩ := mem_filter.mp membership
      obtain ⟨lower, upper⟩ := mem_Icc.mp interval
      have lowerProd : R < k * D := by rw [Nat.mul_comm, ← identity]; omega
      have upperProd : k * D ≤ L := by rwa [Nat.mul_comm, ← identity]
      exact ⟨k, mem_Icc.mpr ⟨(Nat.div_lt_iff_lt_mul DPositive).mpr lowerProd,
        (Nat.le_div_iff_mul_le DPositive).mpr upperProd⟩, identity.symm⟩
    · intro k membership
      have kPositive : 0 < k := APositive.trans_le (mem_Icc.mp membership).1
      have kNonzero : (k : ℝ) ≠ 0 := by exact_mod_cast kPositive.ne'
      rw [Nat.cast_mul]
      field_simp
  rw [equality]
  have maxBound : max R D ≤ D * A := by
    apply max_le
    · calc
        R = D * (R / D) + R % D := (Nat.div_add_mod R D).symm
        _ ≤ D * (R / D) + D := Nat.add_le_add_left (Nat.mod_lt R DPositive).le _
        _ = D * A := by dsimp [A]; ring
    · exact Nat.le_mul_of_pos_right D APositive
  have denominatorPositive : 0 < (D : ℝ) * (max R D : ℕ) := by
    refine mul_pos DRealPositive ?_
    exact_mod_cast DPositive.trans_le (le_max_right R D)
  calc
    _ ≤ (1 / (D : ℝ) ^ 2) * (2 / (A : ℝ)) :=
      mul_le_mul_of_nonneg_left (inverse_square_tail_Icc A (L / D) APositive) (by positivity)
    _ = 2 / ((D : ℝ) * ((D : ℝ) * A)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) denominatorPositive
      (mul_le_mul_of_nonneg_left (by exact_mod_cast maxBound) DRealPositive.le)

theorem conductor_modulus_tail (g d f R L : ℕ) (gPositive : 0 < g) (dPositive : 0 < d) (fPositive : 0 < f) :
    (∑ q ∈ (Icc (R + 1) L).filter (fun q => d * g ∣ q ∧ d * f ∣ q),
      ((d : ℝ) * g * f) / (q : ℝ) ^ 2) ≤ 2 * (g.gcd f : ℝ) / (max R (d * g) : ℕ) := by
  let D := d * g.lcm f
  have lcmPositive : 0 < g.lcm f := Nat.lcm_pos gPositive fPositive
  have DPositive : 0 < D := Nat.mul_pos dPositive lcmPositive
  have DRealPositive : (0 : ℝ) < D := by exact_mod_cast DPositive
  have lcmEq : Nat.lcm (d * g) (d * f) = D := by
    change lcm (d * g) (d * f) = d * lcm g f
    rw [lcm_mul_left, normalize_eq]
  have supportEq : (Icc (R + 1) L).filter (fun q => d * g ∣ q ∧ d * f ∣ q) =
      (Icc (R + 1) L).filter (fun q => D ∣ q) := by
    ext q
    rw [mem_filter, mem_filter, ← lcmEq, Nat.lcm_dvd_iff]
  have numerator : (d : ℝ) * g * f = (D : ℝ) * (g.gcd f : ℝ) := by
    exact_mod_cast (show d * g * f = D * g.gcd f from calc
      _ = d * (g * f) := mul_assoc d g f
      _ = d * (g.gcd f * g.lcm f) := by rw [Nat.gcd_mul_lcm]
      _ = _ := by dsimp [D]; ring)
  have stepLower : d * g ≤ D := Nat.mul_le_mul_left _ (Nat.le_of_dvd lcmPositive (Nat.dvd_lcm_left g f))
  have maxLower : (0 : ℝ) < (max R (d * g) : ℕ) := by
    exact_mod_cast (Nat.mul_pos dPositive gPositive).trans_le (le_max_right R (d * g))
  have maxUpper : ((max R (d * g) : ℕ) : ℝ) ≤ (max R D : ℕ) := by
    exact_mod_cast max_le_max_left R stepLower
  rw [supportEq]
  calc
    _ = ((d : ℝ) * g * f) * ∑ q ∈ (Icc (R + 1) L).filter (fun q => D ∣ q), 1 / (q : ℝ) ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun q _ => (mul_one_div _ _).symm
    _ ≤ ((d : ℝ) * g * f) * (2 / ((D : ℝ) * (max R D : ℕ))) :=
      mul_le_mul_of_nonneg_left (inverse_square_multiples_tail D R L DPositive) (by positivity)
    _ = 2 * (g.gcd f : ℝ) / (max R D : ℕ) := by rw [numerator]; field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) maxLower maxUpper

end DyadicMixedB4ModulusTail

end

section

open Finset DyadicMixedB4ModulusTail DyadicMixedB4WeightBudgets

namespace DyadicMixedB4ModulusAggregate

noncomputable section

def conductorCost (G D F : Finset ℕ) (energy : ℕ → ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, if d * g ∣ q ∧ d * f ∣ q then
    ((d : ℝ) * g * f) / (q : ℝ) * energy g d else 0

theorem conductorCost_nonnegative (G D F : Finset ℕ) (energy : ℕ → ℕ → ℝ)
    (energyNonnegative : ∀ g ∈ G, ∀ d ∈ D, 0 ≤ energy g d) (q : ℕ) :
    0 ≤ conductorCost G D F energy q := by
  unfold conductorCost
  refine sum_nonneg fun g gMember => sum_nonneg fun d dMember => sum_nonneg fun f _ => ?_
  split_ifs
  · exact mul_nonneg (by positivity) (energyNonnegative g gMember d dMember)
  · exact le_rfl

theorem sum_modulus_cost_le (R M : ℕ) (G D F : Finset ℕ) (energy : ℕ → ℕ → ℝ)
    (gPositive : ∀ g ∈ G, 0 < g) (dPositive : ∀ d ∈ D, 0 < d) (fPositive : ∀ f ∈ F, 0 < f)
    (energyNonnegative : ∀ g ∈ G, ∀ d ∈ D, 0 ≤ energy g d) :
    (∑ q ∈ Icc (R + 1) M, (q : ℝ)⁻¹ * conductorCost G D F energy q) ≤
      ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, (2 * (g.gcd f : ℝ) / (max R (d * g) : ℕ)) * energy g d := by
  let Q := Icc (R + 1) M
  let term (q g d f : ℕ) := if d * g ∣ q ∧ d * f ∣ q then
    ((d : ℝ) * g * f) / (q : ℝ) ^ 2 * energy g d else 0
  have reorder : (∑ q ∈ Q, ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, term q g d f) =
      ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, ∑ q ∈ Q, term q g d f := by
    rw [sum_comm]
    refine sum_congr rfl fun g _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun d _ => sum_comm
  calc
    _ = ∑ q ∈ Q, ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, term q g d f := by
      refine sum_congr rfl fun q _ => ?_
      unfold conductorCost
      simp only [mul_sum]
      refine sum_congr rfl fun g _ => sum_congr rfl fun d _ => sum_congr rfl fun f _ => ?_
      unfold term
      split_ifs <;> ring
    _ = ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ F, ∑ q ∈ Q, term q g d f := reorder
    _ ≤ _ := by
      refine sum_le_sum fun g gMember => sum_le_sum fun d dMember => sum_le_sum fun f fMember => ?_
      have factor : (∑ q ∈ Q, term q g d f) =
          (∑ q ∈ Q.filter (fun q => d * g ∣ q ∧ d * f ∣ q), ((d : ℝ) * g * f) / (q : ℝ) ^ 2) * energy g d := by
        rw [sum_mul, sum_filter]
      rw [factor]
      exact mul_le_mul_of_nonneg_right (conductor_modulus_tail g d f R M (gPositive g gMember)
        (dPositive d dMember) (fPositive f fMember)) (energyNonnegative g gMember d dMember)

theorem sum_weighted_moduli_le {ι : Type*} (items : Finset ι) (g : ι → ℕ) (w : ι → ℝ)
    (R M : ℕ) (MPositive : 0 < M) {W : ℝ} (WNonnegative : 0 ≤ W)
    (stepRange : ∀ i ∈ items, g i ∈ Icc 1 M)
    (weightBound : ∀ u ∈ Icc 1 M, (∑ i ∈ items.filter (fun i => g i = u), w i) ≤ W)
    (G D F : Finset ℕ) (energy : ℕ → ℕ → ℝ)
    (gPositive : ∀ g ∈ G, 0 < g) (dPositive : ∀ d ∈ D, 0 < d) (fPositive : ∀ f ∈ F, 0 < f)
    (energyNonnegative : ∀ g ∈ G, ∀ d ∈ D, 0 ≤ energy g d) :
    (∑ i ∈ items, (w i / (g i : ℝ)) * ∑ q ∈ (g i).divisors.filter (fun q => R < q),
      conductorCost G D F energy q) ≤
      (W * (1 + Real.log M)) * (∑ u ∈ G, ∑ d ∈ D, ∑ f ∈ F,
        (2 * (u.gcd f : ℝ) / (max R (d * u) : ℕ)) * energy u d) := by
  let Q := Icc (R + 1) M
  let Ψ := conductorCost G D F energy
  let logarithm := 1 + Real.log (M : ℝ)
  have logNonnegative : 0 ≤ logarithm := add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast MPositive))
  have moduli (i : ι) (membership : i ∈ items) : (g i).divisors.filter (fun q => R < q) =
      Q.filter (fun q => q ∣ g i) := by
    ext q
    obtain ⟨iPositive, iBound⟩ := mem_Icc.mp (stepRange i membership)
    simp only [Q, mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨divides, _⟩, above⟩
      exact ⟨⟨Nat.succ_le_of_lt above, (Nat.le_of_dvd iPositive divides).trans iBound⟩, divides⟩
    · rintro ⟨⟨above, _⟩, divides⟩
      exact ⟨⟨divides, by omega⟩, above⟩
  calc
    _ = ∑ i ∈ items, ∑ q ∈ Q, if q ∣ g i then (w i / (g i : ℝ)) * Ψ q else 0 := by
      refine sum_congr rfl fun i membership => ?_
      rw [moduli i membership, mul_sum, sum_filter]
    _ = ∑ q ∈ Q, (∑ i ∈ items, if q ∣ g i then w i / (g i : ℝ) else 0) * Ψ q := by
      rw [sum_comm]
      refine sum_congr rfl fun q _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun i _ => by split_ifs <;> simp
    _ ≤ ∑ q ∈ Q, W * (q : ℝ)⁻¹ * logarithm * Ψ q := by
      refine sum_le_sum fun q qMember => ?_
      have qPositive : 0 < q := (Nat.zero_lt_succ R).trans_le (mem_Icc.mp qMember).1
      exact mul_le_mul_of_nonneg_right (step_multiple_weight_le items g w M q qPositive WNonnegative stepRange weightBound)
        (conductorCost_nonnegative G D F energy energyNonnegative q)
    _ = (W * logarithm) * ∑ q ∈ Q, (q : ℝ)⁻¹ * Ψ q := by
      rw [mul_sum]
      exact sum_congr rfl fun q _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_modulus_cost_le R M G D F energy gPositive dPositive fPositive energyNonnegative)
      (mul_nonneg WNonnegative logNonnegative)

end
end DyadicMixedB4ModulusAggregate

end

section

open Finset DyadicMixedB4ArcGeometry DyadicMixedB4BilinearBlock DyadicMixedB4BilinearEnergy
open DyadicMixedB4ModulusAggregate

namespace DyadicMixedB4BlockModulus

noncomputable section

theorem norm_primitiveBlock_le (n M B H q step lo hi U A : ℕ) (nPositive : 0 < n) (APositive : 0 < A)
    (qPositive : 0 < q) (qBound : q ≤ M) (stepBound : M ≤ n) (radiusUpper : radius M ≤ 1)
    (indices : Finset ℕ) (indexRange : indices ⊆ Ico A (2 * A)) (w : ℕ → ℂ)
    {T : ℝ} (TNonnegative : 0 ≤ T) (wBound : ∀ a ∈ indices, ‖w a‖ ≤ T)
    (divisorBound : ∀ b ≤ n, (b.divisors.card : ℝ) ≤ T) :
    ‖primitiveBlock n M B H q step lo hi U indices w‖ ≤
      (T ^ 2 * (16 + 24 * Real.log ((n : ℝ) + 1)) / (step : ℝ)) *
        conductorCost (Icc 1 (2 * A)) (Icc 1 M) n.divisors (blockEnergy n A U) q := by
  let G := Icc 1 (2 * A)
  let D := Icc 1 M
  let energy := blockEnergy n A U
  let K := T ^ 2 * (16 + 24 * Real.log ((n : ℝ) + 1)) / (step : ℝ)
  have KNonnegative : 0 ≤ K := by
    unfold K
    have : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    positivity
  let budget (g d : ℕ) :=
    ∑ f ∈ n.divisors, if d * g ∣ q ∧ d * f ∣ q then ((d : ℝ) * g * f) / (q : ℝ) * energy g d else 0
  have budgetNonnegative (g d : ℕ) : 0 ≤ budget g d := by
    unfold budget
    refine sum_nonneg fun f _ => ?_
    split_ifs
    · exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    · exact le_rfl
  let fibre (g : ℕ) := indices.filter (fun a => a.gcd q = g)
  have mapsTo (a : ℕ) (member : a ∈ indices) : a.gcd q ∈ G := by
    obtain ⟨lower, upper⟩ := mem_Ico.mp (indexRange member)
    have aPositive := APositive.trans_le lower
    exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left q aPositive, (Nat.gcd_le_left q aPositive).trans upper.le⟩
  have boundFibre (g : ℕ) (gMember : g ∈ G) :
      ‖primitiveBlock n M B H q step lo hi U (fibre g) w‖ ≤ K * ∑ d ∈ D, budget g d := by
    have gPositive : 0 < g := (mem_Icc.mp gMember).1
    have exactGcd (a : ℕ) (member : a ∈ fibre g) : a.gcd q = g := (mem_filter.mp member).2
    by_cases gq : g ∣ q
    · have rPositive : 0 < q / g := Nat.div_pos (Nat.le_of_dvd qPositive gq) gPositive
      letI : NeZero q := ⟨qPositive.ne'⟩
      letI : NeZero (q / g) := ⟨rPositive.ne'⟩
      let r := q / g
      let qr : r ∣ q := Nat.div_dvd_of_dvd gq
      have inclusion : r.divisors ⊆ D := by
        intro d member
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors member,
          (Nat.divisor_le member).trans ((Nat.div_le_self q g).trans qBound)⟩
      rw [primitiveBlock_eq_sum_conductorBlock gq n M B H step lo hi U (fibre g) w exactGcd]
      refine (norm_sum_le _ _).trans ?_
      calc
        _ ≤ ∑ d ∈ r.divisors.attach, K * budget g d.1 := by
          refine sum_le_sum fun d _ => ?_
          have estimate := norm_conductorBlock_le gq n M B H step lo hi U A nPositive APositive gPositive
            radiusUpper (fibre g) (fun _ member => indexRange (mem_filter.mp member).1)
            exactGcd w TNonnegative (fun a member => wBound a (mem_filter.mp member).1)
            (divisorBound r ((Nat.div_le_self q g).trans (qBound.trans stepBound))) d
          have divides : d.1 * g ∣ q := by
            rw [Nat.mul_comm]
            exact (Nat.dvd_div_iff_mul_dvd gq).mp (Nat.dvd_of_mem_divisors d.2)
          have factor : budget g d.1 =
              (∑ f ∈ n.divisors, if d.1 * f ∣ q then ((d.1 : ℝ) * g * f) / (q : ℝ) else 0) * energy g d.1 := by
            unfold budget
            rw [sum_mul]
            refine sum_congr rfl fun f _ => ?_
            simp only [divides, true_and]
            split_ifs <;> simp
          rw [factor, ← mul_assoc]
          exact estimate
        _ = K * ∑ d ∈ r.divisors, budget g d := by
          rw [mul_sum]
          exact sum_attach r.divisors (fun d => K * budget g d)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg inclusion (fun d _ _ => budgetNonnegative g d)) KNonnegative
    · have empty : fibre g = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro a member
        exact gq (exactGcd a member ▸ Nat.gcd_dvd_right a q)
      rw [empty, primitiveBlock, sum_empty, norm_zero]
      exact mul_nonneg KNonnegative (sum_nonneg fun d _ => budgetNonnegative g d)
  have split : primitiveBlock n M B H q step lo hi U indices w =
      ∑ g ∈ G, primitiveBlock n M B H q step lo hi U (fibre g) w := by
    unfold primitiveBlock
    exact (sum_fiberwise_of_maps_to mapsTo _).symm
  rw [split]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ g ∈ G, K * ∑ d ∈ D, budget g d := sum_le_sum boundFibre
    _ = _ := by rw [← mul_sum]; rfl

end
end DyadicMixedB4BlockModulus

end

section

namespace DyadicMixedB4DyadicCost

private theorem sqrt_prod_le_max {x y : ℝ} (xNonnegative : 0 ≤ x) :
    Real.sqrt x * Real.sqrt y ≤ max x y := by
  calc
    _ ≤ Real.sqrt (max x y) * Real.sqrt (max x y) :=
      mul_le_mul (Real.sqrt_le_sqrt (le_max_left _ _)) (Real.sqrt_le_sqrt (le_max_right _ _))
        (Real.sqrt_nonneg y) (Real.sqrt_nonneg _)
    _ = _ := by rw [← pow_two, Real.sq_sqrt (xNonnegative.trans (le_max_left _ _))]

private theorem sqrt_le_of_le_sq {x y : ℝ} (yNonnegative : 0 ≤ y) (bound : x ≤ y ^ 2) :
    Real.sqrt x ≤ y := (Real.sqrt_le_sqrt bound).trans_eq (Real.sqrt_sq yNonnegative)

theorem dyadic_cost_le (A G D Y R : ℝ) (aPositive : 0 < A) (gLower : 1 ≤ G)
    (dPositive : 0 < D) (yPositive : 0 < Y) (rPositive : 0 < R) (yLarge : A ≤ Real.sqrt Y) :
    Real.sqrt ((A / G) * D * (A / G + D) * (Y + D ^ 2) * Y) / max R (G * D) ≤
      (2 * A * Y) / (G * Real.sqrt G * Real.sqrt R) +
      (2 * Real.sqrt A * Y) / (G * Real.sqrt G) +
      (2 * Real.sqrt A * Real.sqrt Y * D) / (G * Real.sqrt G) := by
  let X := A / G
  let T := max R (G * D)
  let energy := X * D * (X + D) * (Y + D ^ 2) * Y
  let lowCost := (2 * A * Y) / (G * Real.sqrt G * Real.sqrt R)
  let midCost := (2 * Real.sqrt A * Y) / (G * Real.sqrt G)
  let highCost := (2 * Real.sqrt A * Real.sqrt Y * D) / (G * Real.sqrt G)
  have gPositive : 0 < G := zero_lt_one.trans_le gLower
  have xPositive : 0 < X := div_pos aPositive gPositive
  have tPositive : 0 < T := rPositive.trans_le (le_max_left _ _)
  have productPositive : 0 < G * D := mul_pos gPositive dPositive
  have productBound : G * D ≤ T := le_max_right _ _
  have xBound : X ≤ Real.sqrt Y := (div_le_self aPositive.le gLower).trans yLarge
  have lowNonnegative : 0 ≤ lowCost := by dsimp [lowCost]; positivity
  have midNonnegative : 0 ≤ midCost := by dsimp [midCost]; positivity
  have highNonnegative : 0 ≤ highCost := by dsimp [highCost]; positivity
  have addLow : lowCost ≤ lowCost + midCost + highCost := by linarith only [midNonnegative, highNonnegative]
  have addMid : midCost ≤ lowCost + midCost + highCost := by linarith only [lowNonnegative, highNonnegative]
  have addHigh : highCost ≤ lowCost + midCost + highCost := by linarith only [lowNonnegative, midNonnegative]
  have sqrtX : Real.sqrt X = Real.sqrt A / Real.sqrt G := Real.sqrt_div aPositive.le _
  have sqrtDPositive : 0 < Real.sqrt D := Real.sqrt_pos.mpr dPositive
  have sqrtGPositive : 0 < Real.sqrt G := Real.sqrt_pos.mpr gPositive
  have sqrtRPositive : 0 < Real.sqrt R := Real.sqrt_pos.mpr rPositive
  change Real.sqrt energy / T ≤ lowCost + midCost + highCost
  by_cases medium : D ≤ Real.sqrt Y
  · have Dsquare : D ^ 2 ≤ Y := by
      have bound := pow_le_pow_left₀ dPositive.le medium 2
      rwa [Real.sq_sqrt yPositive.le] at bound
    by_cases narrow : D ≤ X
    · have root : Real.sqrt energy ≤ 2 * X * Real.sqrt D * Y := by
        apply sqrt_le_of_le_sq (by positivity)
        calc
          _ ≤ X * D * (2 * X) * (2 * Y) * Y := by
            unfold energy
            gcongr <;> linarith only [narrow, Dsquare]
          _ = _ := by simp only [mul_pow, Real.sq_sqrt dPositive.le]; ring
      have geometric := sqrt_prod_le_max (y := G * D) rPositive.le
      rw [Real.sqrt_mul gPositive.le] at geometric
      have geometricPositive := mul_pos sqrtRPositive (mul_pos sqrtGPositive sqrtDPositive)
      refine le_trans ?_ addLow
      calc
        _ ≤ (2 * X * Real.sqrt D * Y) / T := div_le_div_of_nonneg_right root tPositive.le
        _ ≤ (2 * X * Real.sqrt D * Y) / (Real.sqrt R * (Real.sqrt G * Real.sqrt D)) :=
          div_le_div_of_nonneg_left (by positivity) geometricPositive geometric
        _ = _ := by
          unfold lowCost X
          field_simp [gPositive.ne', sqrtDPositive.ne', sqrtGPositive.ne', sqrtRPositive.ne']
    · have root : Real.sqrt energy ≤ 2 * Real.sqrt X * D * Y := by
        apply sqrt_le_of_le_sq (by positivity)
        calc
          _ ≤ X * D * (2 * D) * (2 * Y) * Y := by
            unfold energy
            gcongr <;> linarith only [lt_of_not_ge narrow, Dsquare]
          _ = _ := by simp only [mul_pow, Real.sq_sqrt xPositive.le]; ring
      refine le_trans ?_ addMid
      calc
        _ ≤ (2 * Real.sqrt X * D * Y) / T := div_le_div_of_nonneg_right root tPositive.le
        _ ≤ (2 * Real.sqrt X * D * Y) / (G * D) :=
          div_le_div_of_nonneg_left (by positivity) productPositive productBound
        _ = _ := by
          unfold midCost
          rw [sqrtX]
          field_simp [gPositive.ne', dPositive.ne', sqrtGPositive.ne']
  · have wide : X ≤ D := xBound.trans (lt_of_not_ge medium).le
    have ySquare : Y ≤ D ^ 2 := by
      have bound := pow_le_pow_left₀ (Real.sqrt_nonneg Y) (lt_of_not_ge medium).le 2
      rwa [Real.sq_sqrt yPositive.le] at bound
    have root : Real.sqrt energy ≤ 2 * Real.sqrt X * Real.sqrt Y * D ^ 2 := by
      apply sqrt_le_of_le_sq (by positivity)
      calc
        _ ≤ X * D * (2 * D) * (2 * D ^ 2) * Y := by
          unfold energy
          gcongr <;> linarith only [wide, ySquare]
        _ = _ := by simp only [mul_pow, Real.sq_sqrt xPositive.le, Real.sq_sqrt yPositive.le]; ring
    refine le_trans ?_ addHigh
    calc
      _ ≤ (2 * Real.sqrt X * Real.sqrt Y * D ^ 2) / T := div_le_div_of_nonneg_right root tPositive.le
      _ ≤ (2 * Real.sqrt X * Real.sqrt Y * D ^ 2) / (G * D) :=
        div_le_div_of_nonneg_left (by positivity) productPositive productBound
      _ = _ := by
        unfold highCost
        rw [sqrtX]
        field_simp [gPositive.ne', dPositive.ne', sqrtGPositive.ne']

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

def tailShape (n A M R : ℕ) : ℝ :=
  (n : ℝ) / Real.sqrt R + (n : ℝ) / Real.sqrt A + Real.sqrt n * (M : ℝ)

theorem tailShape_nonnegative (n A M R : ℕ) : 0 ≤ tailShape n A M R := by
  unfold tailShape
  positivity

def tailWeight (R g f d : ℕ) : ℝ := 2 * (g.gcd f : ℝ) / (max R (d * g) : ℕ)

theorem tailWeight_nonnegative (R g f d : ℕ) : 0 ≤ tailWeight R g f d := by
  unfold tailWeight
  positivity

theorem blockEnergy_nonnegative (n A U g d : ℕ) : 0 ≤ blockEnergy n A U g d := Real.sqrt_nonneg _

theorem energy_tail_in_dyad_le (n A U R M g f D : ℕ) (aPos : 0 < A) (gPos : 0 < g)
    (gUpper : g ≤ 2 * A) (dPos : 0 < D) (rPos : 0 < R) (dUpper : D ≤ M)
    (yLarge : (A : ℝ) ≤ Real.sqrt (n / A : ℕ)) :
    (∑ d ∈ Ico D (2 * D), tailWeight R g f d * blockEnergy n A U g d) ≤
      2048 * logBudget n ^ 2 * ((g.gcd f : ℝ) / ((g : ℝ) * Real.sqrt g)) * tailShape n A M R := by
  let Y := n / A
  let X := (2 * A) / g + 1
  let x := (A : ℝ) / g
  let Z := max (R : ℝ) ((g : ℝ) * D)
  let I := prefixMass Y
  let J d := integratedPrimitiveEnergy Y d (mangoldtExtension U)
  let L := Real.log ((Y : ℝ) + 2)
  let P := x * (x + D) * I
  let Q := (D : ℝ) * I * ((Y : ℝ) + (D : ℝ) ^ 2) * Y
  let V := x * D * (x + D) * ((Y : ℝ) + (D : ℝ) ^ 2) * Y
  have gReal : (0 : ℝ) < g := by exact_mod_cast gPos
  have aReal : (0 : ℝ) < A := by exact_mod_cast aPos
  have dReal : (0 : ℝ) < D := by exact_mod_cast dPos
  have rReal : (0 : ℝ) < R := by exact_mod_cast rPos
  have aSqrt : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos_of_pos aReal
  have yPos : 0 < (Y : ℝ) := by
    by_contra! hy
    rw [Real.sqrt_eq_zero_of_nonpos hy] at yLarge
    exact aReal.not_ge yLarge
  have ZPos : 0 < Z := rReal.trans_le (le_max_left _ _)
  have xPos : 0 < x := div_pos aReal gReal
  have I0 : 0 ≤ I := prefixMass_nonnegative _
  have L0 : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) Y])
  have P0 : 0 ≤ P := by unfold P; positivity
  have Q0 : 0 ≤ Q := by unfold Q; positivity
  have xBound : (X : ℝ) ≤ 4 * x := by
    have division : (((2 * A) / g : ℕ) : ℝ) * g ≤ 2 * (A : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (2 * A) g
    have oneBound : 1 ≤ 2 * x := by
      unfold x
      rw [← mul_div_assoc]
      exact (le_div_iff₀ gReal).mpr (by simpa using (show (g : ℝ) ≤ 2 * (A : ℝ) by exact_mod_cast gUpper))
    have half : (((2 * A) / g : ℕ) : ℝ) ≤ 2 * x := by
      unfold x
      rw [← mul_div_assoc]
      exact (le_div_iff₀ gReal).mpr division
    unfold X
    push_cast
    linarith only [oneBound, half]
  have weightBound (d : ℕ) (member : d ∈ Ico D (2 * D)) :
      tailWeight R g f d ≤ 2 * (g.gcd f : ℝ) / Z := by
    have dBound : (D : ℝ) ≤ d := by exact_mod_cast (mem_Ico.mp member).1
    unfold tailWeight
    push_cast
    apply div_le_div_of_nonneg_left (by positivity) ZPos
    unfold Z
    rw [mul_comm (d : ℝ)]
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left dBound gReal.le)
  have energyBound (d : ℕ) (member : d ∈ Ico D (2 * D)) :
      blockEnergy n A U g d ≤ (4 * Real.sqrt P) * Real.sqrt (J d) := by
    have dBound : (d : ℝ) ≤ 2 * (D : ℝ) := by exact_mod_cast (mem_Ico.mp member).2.le
    have second : (X : ℝ) + d ≤ 4 * (x + D) := by linarith only [xBound, dBound, dReal]
    have J0 : 0 ≤ J d := integratedPrimitiveEnergy_nonnegative _ _ _
    have within : (X : ℝ) * ((X : ℝ) + d) * I * J d ≤ 16 * P * J d := by
      calc
        _ ≤ ((4 * x) * (4 * (x + D))) * I * J d := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul xBound second (by positivity) (by positivity)) I0) J0
        _ = _ := by unfold P; ring
    calc
      _ ≤ Real.sqrt (16 * P * J d) := Real.sqrt_le_sqrt within
      _ = _ := by rw [Real.sqrt_mul (by positivity : 0 ≤ 16 * P), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]; norm_num
  have energySum := sum_sqrt_dyadic_energy_le Y U D dPos
  have sqrtFactor : Real.sqrt P * Real.sqrt Q = I * Real.sqrt V := by
    rw [← Real.sqrt_mul P0]
    have factor : P * Q = I ^ 2 * V := by unfold P Q V; ring
    rw [factor, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq I0]
  have cost := dyadic_cost_le (A : ℝ) (g : ℝ) (D : ℝ) (Y : ℝ) (R : ℝ) aReal
    (by exact_mod_cast gPos) dReal yPos rReal yLarge
  have nBound : (A : ℝ) * (Y : ℝ) ≤ n := by
    rw [mul_comm]
    exact_mod_cast Nat.div_mul_le_self n A
  have middle : Real.sqrt (A : ℝ) * (Y : ℝ) ≤ (n : ℝ) / Real.sqrt A := by
    apply (le_div_iff₀ aSqrt).mpr
    calc
      _ = (A : ℝ) * (Y : ℝ) := by
        calc
          _ = (Real.sqrt (A : ℝ)) ^ 2 * (Y : ℝ) := by ring
          _ = _ := by rw [Real.sq_sqrt aReal.le]
      _ ≤ _ := nBound
  have endTerm : Real.sqrt (A : ℝ) * Real.sqrt (Y : ℝ) * D ≤ Real.sqrt (n : ℝ) * M := by
    rw [← Real.sqrt_mul aReal.le]
    exact mul_le_mul (Real.sqrt_le_sqrt nBound) (by exact_mod_cast dUpper)
      (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have simplified : Real.sqrt V / Z ≤ (2 / ((g : ℝ) * Real.sqrt g)) * tailShape n A M R := by
    refine cost.trans ?_
    unfold tailShape
    have first : (A : ℝ) * (Y : ℝ) / Real.sqrt R ≤ (n : ℝ) / Real.sqrt R :=
      div_le_div_of_nonneg_right nBound (Real.sqrt_nonneg _)
    have combined := add_le_add (add_le_add first middle) endTerm
    calc
      _ = (2 / ((g : ℝ) * Real.sqrt g)) *
          ((A : ℝ) * (Y : ℝ) / Real.sqrt R + Real.sqrt (A : ℝ) * (Y : ℝ) +
            Real.sqrt (A : ℝ) * Real.sqrt (Y : ℝ) * D) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left combined (by positivity)
  have logBound : L ≤ logBudget n := by
    have yBound : (Y : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n A
    exact (Real.log_le_log (by positivity) (by linarith only [yBound])).trans
      (le_add_of_nonneg_left zero_le_one)
  have massBound : I ≤ 8 * logBudget n :=
    (integral_prefixMajorant_le Y).trans (mul_le_mul_of_nonneg_left logBound (by norm_num))
  calc
    _ ≤ ∑ d ∈ Ico D (2 * D), (2 * (g.gcd f : ℝ) / Z * (4 * Real.sqrt P)) * Real.sqrt (J d) := by
      refine sum_le_sum fun d member => ?_
      rw [mul_assoc]
      exact mul_le_mul (weightBound d member) (energyBound d member)
        (blockEnergy_nonnegative n A U g d) (by positivity)
    _ ≤ (2 * (g.gcd f : ℝ) / Z * (4 * Real.sqrt P)) * (16 * L * Real.sqrt Q) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left energySum (by positivity)
    _ = 128 * L * I * (g.gcd f : ℝ) * (Real.sqrt V / Z) := by
      calc
        _ = 128 * L * (g.gcd f : ℝ) / Z * (Real.sqrt P * Real.sqrt Q) := by ring
        _ = _ := by rw [sqrtFactor]; ring
    _ ≤ 128 * logBudget n * (8 * logBudget n) * (g.gcd f : ℝ) *
        ((2 / ((g : ℝ) * Real.sqrt g)) * tailShape n A M R) := by
      have bNonnegative : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left logBound (by norm_num)) massBound I0 (by positivity))
            (Nat.cast_nonneg _))
        simplified (div_nonneg (Real.sqrt_nonneg _) ZPos.le) (by positivity)
    _ = _ := by ring

end
end DyadicMixedB4EnergyTail

end

section

open Filter Topology DyadicMixedB4ArcGeometry

namespace DyadicMixedB4Scale

noncomputable section

def cutoffU (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊
def cutoffB (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
def cutoffR (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 9 : ℝ)⌋₊
def cofactorCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (111 / 256 : ℝ)⌋₊
def maximumStep (n : ℕ) : ℕ := cutoffU n * cofactorCap n
def cutoffH (n : ℕ) : ℕ := 256 * cutoffB n * (Nat.log 2 (n + 2)) ^ 2

theorem maximumStep_le_power (n : ℕ) (nPositive : 0 < n) :
    (maximumStep n : ℝ) ≤ (n : ℝ) ^ (127 / 256 : ℝ) := by
  have u : (cutoffU n : ℝ) ≤ (n : ℝ) ^ (1 / 16 : ℝ) := Nat.floor_le (by positivity)
  have b : (cofactorCap n : ℝ) ≤ (n : ℝ) ^ (111 / 256 : ℝ) := Nat.floor_le (by positivity)
  unfold maximumStep
  push_cast
  calc
    _ ≤ (n : ℝ) ^ (1 / 16 : ℝ) * (n : ℝ) ^ (111 / 256 : ℝ) := by gcongr
    _ = _ := by rw [← Real.rpow_add (by positivity)]; norm_num

theorem floor_half_le {x : ℝ} (xLower : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  by_cases small : x ≤ 2
  · have floorLower : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.le_floor (n := 1) (by simpa using xLower))
    linarith only [small, floorLower]
  · have floorBound := Nat.lt_floor_add_one x
    linarith only [floorBound, lt_of_not_ge small]

theorem cutoffs_ordered (n : ℕ) (nPositive : 0 < n) :
    1 ≤ cutoffR n ∧ cutoffR n ≤ cutoffB n ∧ cutoffB n ≤ maximumStep n ∧ maximumStep n ≤ n := by
  have nReal : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have Upositive : 1 ≤ cutoffU n := Nat.le_floor (Real.one_le_rpow nReal (by norm_num))
  refine ⟨Nat.le_floor (Real.one_le_rpow nReal (by norm_num)), ?_, ?_, ?_⟩
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nReal (by norm_num))
  · have cap : cutoffB n ≤ cofactorCap n :=
      Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nReal (by norm_num))
    exact cap.trans (Nat.le_mul_of_pos_left (cofactorCap n) Upositive)
  · exact_mod_cast (maximumStep_le_power n nPositive).trans ((Real.rpow_le_rpow_of_exponent_le nReal
      (by norm_num : (127 / 256 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))

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

theorem cutoffR_covered (n : ℕ) (nPositive : 0 < n) :
    (cutoffR n : ℝ) * n * radius (maximumStep n) ≤ cutoffH n := by
  have nReal : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have nRealPositive : (0 : ℝ) < n := by exact_mod_cast nPositive
  have uLower : (n : ℝ) ^ (1 / 16 : ℝ) / 2 ≤ cutoffU n := floor_half_le (Real.one_le_rpow nReal (by norm_num))
  have bLower : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ cutoffB n := floor_half_le (Real.one_le_rpow nReal (by norm_num))
  have logLower : (1 : ℝ) ≤ Nat.log 2 (n + 2) := by
    exact_mod_cast Nat.log_pos (by decide : 1 < 2) (by omega : 2 ≤ n + 2)
  have rUpper : (cutoffR n : ℝ) ≤ (n : ℝ) ^ (1 / 9 : ℝ) := Nat.floor_le (by positivity)
  have MPositive : 0 < maximumStep n := by have := cutoffs_ordered n nPositive; omega
  have coverLower : (64 : ℝ) * (n : ℝ) ^ (9 / 8 : ℝ) ≤ 8 * (maximumStep n : ℝ) ^ 2 * (cutoffH n : ℝ) := by
    have uPower : ((n : ℝ) ^ (1 / 16 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul nRealPositive.le]
      norm_num
    have bPower : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul nRealPositive.le]
      norm_num
    calc
      _ = 2048 * ((n : ℝ) ^ (1 / 16 : ℝ) / 2) ^ 2 * ((n : ℝ) ^ (1 / 3 : ℝ) / 2) ^ 3 := by
        rw [div_pow, div_pow, uPower, bPower]
        have exponent : (n : ℝ) ^ (9 / 8 : ℝ) = (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) := by
          calc
            _ = (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [← Real.rpow_add nRealPositive]; norm_num
            _ = _ := by rw [Real.rpow_one]
        rw [exponent]
        ring
      _ ≤ 2048 * (cutoffU n : ℝ) ^ 2 * (cutoffB n : ℝ) ^ 3 := by gcongr
      _ ≤ 2048 * (cutoffU n : ℝ) ^ 2 * (cutoffB n : ℝ) ^ 3 * (Nat.log 2 (n + 2) : ℝ) ^ 2 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ logLower)
      _ = 8 * ((cutoffU n : ℝ) * (cutoffB n : ℝ)) ^ 2 * (cutoffH n : ℝ) := by
        unfold cutoffH
        push_cast
        ring
      _ ≤ _ := by
        have cap : cutoffB n ≤ cofactorCap n :=
          Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nReal (by norm_num))
        have capReal : (cutoffB n : ℝ) ≤ cofactorCap n := by exact_mod_cast cap
        unfold maximumStep
        push_cast
        gcongr
  have coverUpper : (cutoffR n : ℝ) * n ≤ (n : ℝ) ^ (9 / 8 : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 9 : ℝ) * n := mul_le_mul_of_nonneg_right rUpper nRealPositive.le
      _ = (n : ℝ) ^ (10 / 9 : ℝ) := by
        calc
          _ = (n : ℝ) ^ (1 / 9 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add nRealPositive]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le nReal (by norm_num)
  unfold radius
  rw [mul_one_div]
  apply (div_le_iff₀ (show 0 < 8 * (maximumStep n : ℝ) ^ 2 by positivity)).mpr
  exact coverUpper.trans ((le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ) ≤ 64)).trans
    (by simpa only [mul_comm (cutoffH n : ℝ)] using coverLower))

theorem eventually_small_width : ∀ᶠ n : ℕ in atTop, 4 * cutoffH n * maximumStep n ≤ n := by
  have limit : Tendsto (fun n : ℕ => (Real.log n) ^ 2 / (n : ℝ) ^ (131 / 768 : ℝ)) atTop (𝓝 0) := by
    have asymptotic := (isLittleO_log_rpow_rpow_atTop (2 : ℕ) (show (0 : ℝ) < 131 / 768 by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, Function.comp_def] using asymptotic.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2, limit.eventually_lt_const (show (0 : ℝ) < 1 / 16384 by norm_num)] with n hn small
  have nPositive : 0 < n := by omega
  have nRealPositive : (0 : ℝ) < n := by exact_mod_cast nPositive
  have bUpper : (cutoffB n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
  have stepUpper := maximumStep_le_power n nPositive
  have logUpper := log2_le_four_log n hn
  have asReal : (4 : ℝ) * (cutoffH n : ℝ) * maximumStep n ≤ n := by
    calc
      _ = 1024 * (cutoffB n : ℝ) * (Nat.log 2 (n + 2) : ℝ) ^ 2 * (maximumStep n : ℝ) := by
        unfold cutoffH
        push_cast
        ring
      _ ≤ 1024 * ((n : ℝ) ^ (1 / 3 : ℝ)) * (4 * Real.log n) ^ 2 * ((n : ℝ) ^ (127 / 256 : ℝ)) := by gcongr
      _ = (n : ℝ) ^ (637 / 768 : ℝ) * (16384 * (Real.log n) ^ 2) := by
        have exponent : (n : ℝ) ^ (637 / 768 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (127 / 256 : ℝ) := by
          rw [← Real.rpow_add nRealPositive]
          norm_num
        rw [exponent]
        ring
      _ ≤ (n : ℝ) ^ (637 / 768 : ℝ) * (n : ℝ) ^ (131 / 768 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have absorbed := (div_lt_iff₀ (show 0 < (n : ℝ) ^ (131 / 768 : ℝ) by positivity)).mp small
        linarith only [absorbed]
      _ = _ := by rw [← Real.rpow_add nRealPositive]; norm_num
  exact_mod_cast asReal

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

theorem one_add_log_step_le (n : ℕ) (nPositive : 0 < n) :
    1 + Real.log (maximumStep n : ℝ) ≤ logBudget n := by
  obtain ⟨rPositive, rBound, bBound, mBound⟩ := cutoffs_ordered n nPositive
  have mPositive := rPositive.trans (rBound.trans bBound)
  have positive : (0 : ℝ) < maximumStep n := by exact_mod_cast mPositive
  have upper : (maximumStep n : ℝ) ≤ n := by exact_mod_cast mBound
  exact add_le_add_right (Real.log_le_log positive (by linarith only [upper])) 1

theorem maximumStep_divisor_lower (n : ℕ) (nPositive : 0 < n) :
    (n : ℝ) ^ (127 / 256 : ℝ) / 4 ≤ (maximumStep n : ℝ) := by
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have u : (n : ℝ) ^ (1 / 16 : ℝ) / 2 ≤ cutoffU n :=
    floor_half_le (Real.one_le_rpow nLower (by norm_num))
  have b : (n : ℝ) ^ (111 / 256 : ℝ) / 2 ≤ cofactorCap n :=
    floor_half_le (Real.one_le_rpow nLower (by norm_num))
  calc
    _ = ((n : ℝ) ^ (1 / 16 : ℝ) / 2) * ((n : ℝ) ^ (111 / 256 : ℝ) / 2) := by
      rw [div_mul_div_comm, ← Real.rpow_add nReal]; norm_num
    _ ≤ _ := by unfold maximumStep; push_cast; gcongr

theorem sqrt_mul_maximumStep_le (n : ℕ) (nPositive : 0 < n) :
    Real.sqrt (n : ℝ) * (maximumStep n : ℝ) ≤ (n : ℝ) ^ (255 / 256 : ℝ) := by
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  calc
    _ ≤ Real.sqrt (n : ℝ) * (n : ℝ) ^ (127 / 256 : ℝ) :=
      mul_le_mul_of_nonneg_left (maximumStep_le_power n nPositive) (Real.sqrt_nonneg _)
    _ ≤ _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add nReal]
      exact Real.rpow_le_rpow_of_exponent_le nLower (by norm_num)

theorem short_dyad_yLarge {n A : ℕ} (aPositive : 0 < A)
    (aUpper : A ≤ ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊) :
    (A : ℝ) ≤ Real.sqrt (n / A : ℕ) := by
  have aLower : (1 : ℝ) ≤ A := by exact_mod_cast aPositive
  have aRealUpper := (show (A : ℝ) ≤ (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℝ) by exact_mod_cast aUpper).trans
    (Nat.floor_le (by positivity))
  have fourth : (A : ℝ) ^ 4 ≤ (n : ℝ) := by
    refine (pow_le_pow_left₀ (Nat.cast_nonneg _) aRealUpper 4).trans_eq ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have cube : (A : ℝ) ^ 3 ≤ (n : ℝ) := (pow_le_pow_right₀ aLower (by decide : 3 ≤ 4)).trans fourth
  have div : A ^ 2 ≤ n / A := by
    apply (Nat.le_div_iff_mul_le aPositive).mpr
    rw [← pow_succ]
    exact_mod_cast cube
  have rdiv : (A : ℝ) ^ 2 ≤ (n / A : ℕ) := by exact_mod_cast div
  exact (Real.sqrt_sq (Nat.cast_nonneg _)).symm.trans_le (Real.sqrt_le_sqrt rdiv)

private theorem div_sqrt_le_power (n b : ℕ) (nPositive : 0 < n) (bPositive : 0 < b)
    (a : ℝ) (lower : (n : ℝ) ^ (2 * a) / 4 ≤ b) :
    (n : ℝ) / Real.sqrt b ≤ 2 * (n : ℝ) ^ (1 - a) := by
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have bReal : (0 : ℝ) < b := by exact_mod_cast bPositive
  have rootLower : (n : ℝ) ^ a / 2 ≤ Real.sqrt b := by
    calc
      _ = Real.sqrt (((n : ℝ) ^ a / 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := by
        apply Real.sqrt_le_sqrt
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul nReal.le, mul_comm a, show (↑(2 : ℕ) : ℝ) = 2 by norm_cast]
        norm_num
        exact lower
  apply (div_le_iff₀ (Real.sqrt_pos_of_pos bReal)).mpr
  calc
    _ = 2 * (n : ℝ) ^ (1 - a) * ((n : ℝ) ^ a / 2) := by
      have product := (Real.rpow_add nReal (1 - a) a).symm
      rw [sub_add_cancel, Real.rpow_one] at product
      calc
        _ = (n : ℝ) ^ (1 - a) * (n : ℝ) ^ a := product.symm
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left rootLower (by positivity)

theorem tailShape_scale_le {n A : ℕ} (nPositive : 0 < n) (aPositive : 0 < A)
    (uLower : cutoffU n < 2 * A) :
    tailShape n A (maximumStep n) (cutoffR n) ≤ 5 * (n : ℝ) ^ (255 / 256 : ℝ) := by
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have uReal : (cutoffU n : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast uLower.le
  have lowerU : (n : ℝ) ^ (1 / 16 : ℝ) / 2 ≤ cutoffU n :=
    floor_half_le (Real.one_le_rpow nLower (by norm_num))
  have lowerR : (n : ℝ) ^ (1 / 9 : ℝ) / 2 ≤ cutoffR n :=
    floor_half_le (Real.one_le_rpow nLower (by norm_num))
  have rPos := (cutoffs_ordered n nPositive).1
  have first : (n : ℝ) / Real.sqrt (cutoffR n) ≤ 2 * (n : ℝ) ^ (255 / 256 : ℝ) := by
    refine (div_sqrt_le_power n (cutoffR n) nPositive rPos (1 / 18) ?_).trans ?_
    · rw [show (2 : ℝ) * (1 / 18) = 1 / 9 by norm_num]
      linarith only [lowerR, Real.rpow_nonneg nReal.le (1 / 9 : ℝ)]
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le nLower (by norm_num)) (by norm_num)
  have second : (n : ℝ) / Real.sqrt (A : ℝ) ≤ 2 * (n : ℝ) ^ (255 / 256 : ℝ) := by
    refine (div_sqrt_le_power n A nPositive aPositive (1 / 32) ?_).trans ?_
    · rw [show (2 : ℝ) * (1 / 32) = 1 / 16 by norm_num]
      linarith only [uReal, lowerU]
    · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le nLower (by norm_num)) (by norm_num)
  have third : Real.sqrt (n : ℝ) * (maximumStep n : ℝ) ≤ (n : ℝ) ^ (255 / 256 : ℝ) := by
    calc
      _ ≤ Real.sqrt (n : ℝ) * (n : ℝ) ^ (127 / 256 : ℝ) :=
        mul_le_mul_of_nonneg_left (maximumStep_le_power n nPositive) (Real.sqrt_nonneg _)
      _ ≤ _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add nReal]
        exact Real.rpow_le_rpow_of_exponent_le nLower (by norm_num)
  unfold tailShape
  linarith only [first, second, third]

end
end DyadicMixedB4TailScale

end

section

open Finset

namespace DyadicMixedB4GcdSeries

noncomputable section

def gcdSeriesConstant : ℝ := ∑' j : ℕ, (j : ℝ) ^ (-3 / 2 : ℝ)

theorem gcdSeriesConstant_nonnegative : 0 ≤ gcdSeriesConstant :=
  tsum_nonneg (fun j => Real.rpow_nonneg (Nat.cast_nonneg j) _)

theorem inverse_sqrt_product_eq_rpow {g : ℕ} (gPositive : 0 < g) :
    ((g : ℝ) * Real.sqrt g)⁻¹ = (g : ℝ) ^ (-3 / 2 : ℝ) := by
  have nonnegative : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have positive : (0 : ℝ) < g := by exact_mod_cast gPositive
  rw [Real.sqrt_eq_rpow]
  nth_rw 1 [← Real.rpow_one (g : ℝ)]
  rw [← Real.rpow_add positive, ← Real.rpow_neg nonnegative]
  norm_num

theorem sum_rpow_multiples (h G : ℕ) (hPositive : 0 < h) :
    (∑ g ∈ (Icc 1 G).filter (fun g => h ∣ g), (g : ℝ) ^ (-3 / 2 : ℝ)) =
      (h : ℝ) ^ (-3 / 2 : ℝ) * ∑ k ∈ Icc 1 (G / h), (k : ℝ) ^ (-3 / 2 : ℝ) := by
  rw [mul_sum]
  symm
  apply sum_bij (fun k _ => h * k)
  · intro k member
    obtain ⟨lower, upper⟩ := mem_Icc.mp member
    have productUpper : k * h ≤ G := (Nat.le_div_iff_mul_le hPositive).mp upper
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hPositive lower, by simpa [mul_comm] using productUpper⟩,
      dvd_mul_right h k⟩
  · intro k _ k' _ same
    exact Nat.eq_of_mul_eq_mul_left hPositive same
  · intro g member
    obtain ⟨inIcc, k, identity⟩ := mem_filter.mp member
    obtain ⟨lower, upper⟩ := mem_Icc.mp inIcc
    have productLower : 0 < h * k := identity ▸ lower
    have productUpper : k * h ≤ G := by simpa [identity, Nat.mul_comm] using upper
    exact ⟨k, mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left productLower,
      (Nat.le_div_iff_mul_le hPositive).mpr productUpper⟩, identity.symm⟩
  · intro k _
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

theorem gcd_sqrt_reciprocal_sum_le (f G : ℕ) (fPositive : 0 < f) :
    (∑ g ∈ Icc 1 G, (g.gcd f : ℝ) / ((g : ℝ) * Real.sqrt g)) ≤
      gcdSeriesConstant * (f.divisors.card : ℝ) := by
  let series (g : ℕ) := (g : ℝ) ^ (-3 / 2 : ℝ)
  have sNonnegative (g : ℕ) : 0 ≤ series g := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have summable : Summable series := Real.summable_nat_rpow.mpr (by norm_num)
  calc
    _ ≤ ∑ g ∈ Icc 1 G, ∑ h ∈ f.divisors, if h ∣ g then (h : ℝ) * series g else 0 := by
      refine sum_le_sum fun g member => ?_
      have gPositive := (mem_Icc.mp member).1
      have gcdMember : g.gcd f ∈ f.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right g f, fPositive.ne'⟩
      rw [div_eq_mul_inv, inverse_sqrt_product_eq_rpow gPositive]
      have term := single_le_sum (s := f.divisors)
        (f := fun h => if h ∣ g then (h : ℝ) * series g else 0)
        (fun h _ => by
          split_ifs
          · exact mul_nonneg (Nat.cast_nonneg _) (sNonnegative g)
          · exact le_rfl) gcdMember
      simpa only [if_pos (Nat.gcd_dvd_left g f), series] using term
    _ = ∑ h ∈ f.divisors, (h : ℝ) * ∑ g ∈ (Icc 1 G).filter (fun g => h ∣ g), series g := by
      rw [sum_comm]
      refine sum_congr rfl fun h _ => ?_
      rw [mul_sum, sum_filter]
    _ ≤ ∑ _ ∈ f.divisors, gcdSeriesConstant := by
      refine sum_le_sum fun h member => ?_
      have hPositive := Nat.pos_of_mem_divisors member
      have hReal : (1 : ℝ) ≤ h := by exact_mod_cast hPositive
      have coeff : (h : ℝ) * (h : ℝ) ^ (-3 / 2 : ℝ) ≤ 1 := by
        have positive : (0 : ℝ) < h := by positivity
        nth_rw 1 [← Real.rpow_one (h : ℝ)]
        rw [← Real.rpow_add positive]
        exact (Real.rpow_le_rpow_of_exponent_le hReal (by norm_num : (1 + -3 / 2 : ℝ) ≤ 0)).trans_eq
          (Real.rpow_zero _)
      unfold series
      rw [sum_rpow_multiples h G hPositive, ← mul_assoc]
      exact (mul_le_of_le_one_left (sum_nonneg fun k _ => sNonnegative k) coeff).trans
        (summable.sum_le_tsum _ fun k _ => sNonnegative k)
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]

end
end DyadicMixedB4GcdSeries

end

section

open Finset

namespace DyadicMixedB4DyadicPartition

def dyadicIndices (N : ℕ) : Finset ℕ := range (Nat.log 2 N + 1)

def dyadicBase (k : ℕ) : ℕ := 2 ^ k

theorem dyadicBase_positive (k : ℕ) : 0 < dyadicBase k :=
  Nat.pow_pos (by decide)

theorem dyadicBase_le {k N : ℕ} (nPositive : 0 < N) (membership : k ∈ dyadicIndices N) :
    dyadicBase k ≤ N := by
  have exponent : k ≤ Nat.log 2 N := Nat.le_of_lt_succ (mem_range.mp membership)
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) exponent).trans (Nat.pow_log_le_self 2 nPositive.ne')

theorem mem_dyadicInterval {a k : ℕ} (aPositive : 0 < a) (logExact : Nat.log 2 a = k) :
    a ∈ Ico (dyadicBase k) (2 * dyadicBase k) := by
  subst k
  refine mem_Ico.mpr ⟨Nat.pow_log_le_self 2 aPositive.ne', ?_⟩
  unfold dyadicBase
  rw [← Nat.pow_succ']
  exact Nat.lt_pow_succ_log_self (by decide) _

theorem dyadic_sum_partition {R : Type*} [AddCommMonoid R] (s : Finset ℕ) (N : ℕ)
    (upper : ∀ a ∈ s, a ≤ N) (term : ℕ → R) :
    (∑ a ∈ s, term a) = ∑ k ∈ dyadicIndices N, ∑ a ∈ s.filter (fun a => Nat.log 2 a = k), term a :=
  (sum_fiberwise_of_maps_to (fun a member => mem_range.mpr
    (Nat.lt_succ_of_le (Nat.log_mono_right (upper a member)))) term).symm

end DyadicMixedB4DyadicPartition

end

section

open Finset DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open DyadicMixedB4DyadicPartition DyadicMixedB4GcdSeries DyadicMixedB4BilinearEnergy

namespace DyadicMixedB4TailAggregate

noncomputable section

theorem sum_energy_tails_le {n A : ℕ} (nLower : 2 ≤ n) (aPositive : 0 < A)
    (aUpper : A ≤ ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊) (uLower : cutoffU n < 2 * A)
    {T : ℝ} (TNonnegative : 0 ≤ T) (tBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    (∑ g ∈ Icc 1 (2 * A), ∑ d ∈ Icc 1 (maximumStep n), ∑ f ∈ n.divisors,
      tailWeight (cutoffR n) g f d * blockEnergy n A (cutoffU n) g d) ≤
      51200 * gcdSeriesConstant * T ^ 2 * logBudget n ^ 3 * (n : ℝ) ^ (255 / 256 : ℝ) := by
  let M := maximumStep n
  let R := cutoffR n
  let term (g f d : ℕ) := tailWeight R g f d * blockEnergy n A (cutoffU n) g d
  let C := 2048 * logBudget n ^ 2
  let F (g f : ℕ) := (g.gcd f : ℝ) / ((g : ℝ) * Real.sqrt g)
  let H := tailShape n A M R
  let C' := C * (5 * logBudget n) * H
  have nPositive : 0 < n := by omega
  have MBound : M ≤ n := (cutoffs_ordered n nPositive).2.2.2
  have RPositive : 0 < R := (cutoffs_ordered n nPositive).1
  have MPositive : 0 < M := RPositive.trans_le
    ((cutoffs_ordered n nPositive).2.1.trans (cutoffs_ordered n nPositive).2.2.1)
  have C0 : 0 ≤ C := by unfold C; positivity
  have B0 : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
  have H0 : 0 ≤ H := tailShape_nonnegative _ _ _ _
  have C'0 : 0 ≤ C' := by unfold C'; positivity
  have F0 (g f : ℕ) : 0 ≤ F g f := by unfold F; positivity
  have term0 (g f d : ℕ) : 0 ≤ term g f d :=
    mul_nonneg (tailWeight_nonnegative _ _ _ _) (blockEnergy_nonnegative _ _ _ _ _)
  have row (g f : ℕ) (gMem : g ∈ Icc 1 (2 * A)) :
      (∑ d ∈ Icc 1 M, term g f d) ≤ C' * F g f := by
    have each (k : ℕ) (kMem : k ∈ dyadicIndices M) :
        (∑ d ∈ (Icc 1 M).filter (fun d => Nat.log 2 d = k), term g f d) ≤ C * F g f * H := by
      let D := dyadicBase k
      have anyMem : (Icc 1 M).filter (fun d => Nat.log 2 d = k) ⊆ Ico D (2 * D) := by
        intro d member
        obtain ⟨dRange, logExact⟩ := mem_filter.mp member
        exact mem_dyadicInterval (mem_Icc.mp dRange).1 logExact
      exact (sum_le_sum_of_subset_of_nonneg anyMem (fun d _ _ => term0 g f d)).trans
        (energy_tail_in_dyad_le n A (cutoffU n) R M g f D aPositive (mem_Icc.mp gMem).1
          (mem_Icc.mp gMem).2 (dyadicBase_positive k) RPositive (dyadicBase_le MPositive kMem)
          (short_dyad_yLarge aPositive aUpper))
    rw [dyadic_sum_partition _ M (fun d member => (mem_Icc.mp member).2)]
    calc
      _ ≤ ∑ _ ∈ dyadicIndices M, C * F g f * H := sum_le_sum each
      _ = ((Nat.log 2 M : ℝ) + 1) * (C * F g f * H) := by
        simp [dyadicIndices, nsmul_eq_mul]
      _ ≤ (5 * logBudget n) * (C * F g f * H) :=
        mul_le_mul_of_nonneg_right (natLog_succ_le nLower MBound) (by positivity)
      _ = _ := by unfold C'; ring
  have divSum : (∑ f ∈ n.divisors, ∑ g ∈ Icc 1 (2 * A), F g f) ≤ gcdSeriesConstant * T ^ 2 := by
    calc
      _ ≤ ∑ f ∈ n.divisors, gcdSeriesConstant * (f.divisors.card : ℝ) :=
        sum_le_sum fun f member => gcd_sqrt_reciprocal_sum_le f (2 * A) (Nat.pos_of_mem_divisors member)
      _ ≤ ∑ _ ∈ n.divisors, gcdSeriesConstant * T :=
        sum_le_sum fun f member => mul_le_mul_of_nonneg_left (tBound _ (Nat.divisor_le member))
          gcdSeriesConstant_nonnegative
      _ ≤ T * (gcdSeriesConstant * T) := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (tBound n le_rfl) (mul_nonneg gcdSeriesConstant_nonnegative TNonnegative)
      _ = _ := by ring
  change (∑ g ∈ Icc 1 (2 * A), ∑ d ∈ Icc 1 M, ∑ f ∈ n.divisors, term g f d) ≤ _
  calc
    _ = ∑ g ∈ Icc 1 (2 * A), ∑ f ∈ n.divisors, ∑ d ∈ Icc 1 M, term g f d :=
      sum_congr rfl fun _ _ => sum_comm
    _ ≤ ∑ g ∈ Icc 1 (2 * A), ∑ f ∈ n.divisors, C' * F g f :=
      sum_le_sum fun g member => sum_le_sum fun f _ => row g f member
    _ = C' * ∑ f ∈ n.divisors, ∑ g ∈ Icc 1 (2 * A), F g f := by
      simp only [mul_sum]
      exact sum_comm
    _ ≤ C' * (gcdSeriesConstant * T ^ 2) := mul_le_mul_of_nonneg_left divSum C'0
    _ = (C * (5 * logBudget n) * (gcdSeriesConstant * T ^ 2)) * H := by unfold C'; ring
    _ ≤ (C * (5 * logBudget n) * (gcdSeriesConstant * T ^ 2)) * (5 * (n : ℝ) ^ (255 / 256 : ℝ)) :=
      mul_le_mul_of_nonneg_left (tailShape_scale_le nPositive aPositive uLower)
        (mul_nonneg (by positivity) (mul_nonneg gcdSeriesConstant_nonnegative (sq_nonneg _)))
    _ = _ := by unfold C; ring

end
end DyadicMixedB4TailAggregate

end

section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace DyadicMixedB4Arithmetic

theorem finite_divisor_hyperbola {R : Type*} [AddCommMonoid R] (limit : ℕ)
    (term : ℕ → ℕ → R) :
    (∑ m ∈ Icc 1 limit, ∑ a ∈ m.divisors, term a (m / a)) =
      ∑ a ∈ Icc 1 limit, ∑ b ∈ Icc 1 (limit / a), term a b := by
  classical
  have divisorFilter (m : ℕ) (membership : m ∈ Icc 1 limit) :
      m.divisors = (Icc 1 limit).filter (fun a => a ∣ m) := by
    obtain ⟨positive, bounded⟩ := mem_Icc.mp membership
    ext a
    rw [mem_filter, mem_Icc]
    constructor
    · intro divisor
      have divides := Nat.dvd_of_mem_divisors divisor
      exact ⟨⟨Nat.pos_of_mem_divisors divisor, (Nat.le_of_dvd positive divides).trans bounded⟩,
        divides⟩
    · rintro ⟨_, divides⟩
      exact Nat.mem_divisors.mpr ⟨divides, (show 0 < m from positive).ne'⟩
  calc
    _ = ∑ m ∈ Icc 1 limit, ∑ a ∈ Icc 1 limit, if a ∣ m then term a (m / a) else 0 := by
      refine sum_congr rfl fun m membership => ?_
      rw [divisorFilter m membership, sum_filter]
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun a membership => ?_
      have aPositive : 0 < a := (mem_Icc.mp membership).1
      let multiply : ℕ ↪ ℕ := ⟨fun b => a * b,
        fun _ _ equal => mul_left_cancel₀ aPositive.ne' equal⟩
      have multiples : (Icc 1 limit).filter (fun m => a ∣ m) =
          (Icc 1 (limit / a)).map multiply := by
        ext m
        simp only [mem_filter, mem_map]
        constructor
        · rintro ⟨inInterval, divides⟩
          obtain ⟨b, rfl⟩ := divides
          obtain ⟨mPositive, mBounded⟩ := mem_Icc.mp inInterval
          have bPositive : 0 < b := by
            by_contra! bZero
            have bEqualsZero : b = 0 := Nat.eq_zero_of_le_zero bZero
            simp [bEqualsZero] at mPositive
          have bBounded : b ≤ limit / a :=
            (Nat.le_div_iff_mul_le aPositive).mpr (by simpa only [mul_comm] using mBounded)
          exact ⟨b, mem_Icc.mpr ⟨bPositive, bBounded⟩, rfl⟩
        · rintro ⟨b, bInInterval, rfl⟩
          obtain ⟨bPositive, bBounded⟩ := mem_Icc.mp bInInterval
          change a * b ∈ Icc 1 limit ∧ a ∣ a * b
          have mBounded : a * b ≤ limit := by
            simpa only [mul_comm] using (Nat.le_div_iff_mul_le aPositive).mp bBounded
          exact ⟨mem_Icc.mpr ⟨Nat.mul_pos aPositive bPositive, mBounded⟩, dvd_mul_right a b⟩
      rw [← sum_filter, multiples, sum_map]
      refine sum_congr rfl fun b _ => ?_
      change term a ((a * b) / a) = term a b
      rw [Nat.mul_div_cancel_left _ aPositive]

theorem finite_divisor_triples {R : Type*} [AddCommMonoid R]
    (limit cutoff lower cofactorCap : ℕ) (cofactorCapLe : cofactorCap ≤ limit)
    (cofactorBound : ∀ a b : ℕ, lower < a → a * b ≤ limit → b ≤ cofactorCap)
    (term : ℕ → ℕ → ℕ → R) :
    (∑ m ∈ Icc 1 limit, ∑ a ∈ m.divisors,
      if lower < a ∧ cutoff < m / a then
        ∑ d ∈ a.divisors, if d ≤ cutoff then term d (m / a) (a / d) else 0
      else 0) =
      ∑ b ∈ Ioc cutoff cofactorCap, ∑ d ∈ Icc 1 (min cutoff (limit / b)),
        ∑ k ∈ Ioc (lower / d) (limit / (d * b)), term d b k := by
  classical
  let summand (b a : ℕ) : R :=
    if lower < a ∧ cutoff < b then
      ∑ d ∈ a.divisors, if d ≤ cutoff then term d b (a / d) else 0
    else 0
  have cofactorSubset : Ioc cutoff cofactorCap ⊆ Icc 1 limit := by
    intro b member
    obtain ⟨above, bounded⟩ := mem_Ioc.mp member
    exact mem_Icc.mpr ⟨(Nat.zero_le cutoff).trans_lt above, bounded.trans cofactorCapLe⟩
  have cofactorRestrict :
      (∑ b ∈ Icc 1 limit, ∑ a ∈ Icc 1 (limit / b), summand b a) =
        ∑ b ∈ Ioc cutoff cofactorCap, ∑ a ∈ Icc 1 (limit / b), summand b a := by
    symm
    refine sum_subset cofactorSubset fun b inOriginal outside => ?_
    refine sum_eq_zero fun a inRange => ?_
    apply ite_eq_right
    rintro ⟨above, bAbove⟩
    have bPositive : 0 < b := (mem_Icc.mp inOriginal).1
    have productBound := (Nat.le_div_iff_mul_le bPositive).mp (mem_Icc.mp inRange).2
    exact outside (mem_Ioc.mpr ⟨bAbove, cofactorBound a b above productBound⟩)
  calc
    _ = ∑ m ∈ Icc 1 limit, ∑ b ∈ m.divisors, summand b (m / b) := by
      refine sum_congr rfl fun m _ => ?_
      change (∑ a ∈ m.divisors, summand (m / a) a) = _
      rw [← Nat.sum_divisorsAntidiagonal (fun a b => summand b a),
        Nat.sum_divisorsAntidiagonal' (fun a b => summand b a)]
    _ = ∑ b ∈ Icc 1 limit, ∑ a ∈ Icc 1 (limit / b), summand b a :=
      finite_divisor_hyperbola limit summand
    _ = ∑ b ∈ Ioc cutoff cofactorCap, ∑ a ∈ Icc 1 (limit / b), summand b a := cofactorRestrict
    _ = _ := by
      refine sum_congr rfl fun b bMember => ?_
      have bAbove := (mem_Ioc.mp bMember).1
      let expanded (d k : ℕ) : R :=
        if d ≤ cutoff ∧ lower < d * k then term d b k else 0
      have row (a : ℕ) : summand b a = ∑ d ∈ a.divisors, expanded d (a / d) := by
        by_cases above : lower < a
        · simp only [summand, above, bAbove, and_self, ite_true]
          refine sum_congr rfl fun d divisor => ?_
          simp [expanded, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors divisor), above]
        · simp only [summand, above, false_and, ite_false]
          symm
          refine sum_eq_zero fun d divisor => ?_
          simp [expanded, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors divisor), above]
      have dFilter : (Icc 1 (limit / b)).filter (fun d => d ≤ cutoff) =
          Icc 1 (min cutoff (limit / b)) := by
        ext d
        simp only [mem_filter, mem_Icc, le_min_iff]
        tauto
      calc
        _ = ∑ a ∈ Icc 1 (limit / b), ∑ d ∈ a.divisors, expanded d (a / d) :=
          sum_congr rfl fun a _ => row a
        _ = ∑ d ∈ Icc 1 (limit / b), ∑ k ∈ Icc 1 ((limit / b) / d), expanded d k :=
          finite_divisor_hyperbola (limit / b) expanded
        _ = ∑ d ∈ Icc 1 (min cutoff (limit / b)),
            ∑ k ∈ Icc 1 ((limit / b) / d), if lower < d * k then term d b k else 0 := by
          rw [← dFilter, sum_filter]
          refine sum_congr rfl fun d _ => ?_
          by_cases small : d ≤ cutoff <;> simp [expanded, small]
        _ = _ := by
          refine sum_congr rfl fun d dMember => ?_
          have dPositive : 0 < d := (mem_Icc.mp dMember).1
          have kFilter : (Icc 1 ((limit / b) / d)).filter (fun k => lower < d * k) =
              Ioc (lower / d) (limit / (d * b)) := by
            ext k
            simp only [mem_filter, mem_Icc, mem_Ioc]
            rw [Nat.div_div_eq_div_mul, mul_comm b d]
            have lowerIff : lower < d * k ↔ lower / d < k := by
              rw [Nat.div_lt_iff_lt_mul dPositive, mul_comm k d]
            constructor
            · rintro ⟨⟨_, upper⟩, lowerBound⟩
              exact ⟨lowerIff.mp lowerBound, upper⟩
            · rintro ⟨lowerBound, upper⟩
              exact ⟨⟨(Nat.zero_le (lower / d)).trans_lt lowerBound, upper⟩,
                lowerIff.mpr lowerBound⟩
          rw [← sum_filter, kFilter]

def upperBandWeight {R : Type*} [Ring R] (cutoff lower : ℕ)
    (divisorWeight cofactorWeight : ℕ → R) (m : ℕ) : R :=
  ∑ a ∈ m.divisors.filter (fun a => lower < a ∧ cutoff < m / a),
    (∑ d ∈ a.divisors.filter (fun d => cutoff < d), divisorWeight d) * cofactorWeight (m / a)

theorem upper_band_progressions {R : Type*} [CommRing R]
    (limit cutoff lower cofactorCap : ℕ) (cofactorCapLe : cofactorCap ≤ limit)
    (cofactorBound : ∀ a b : ℕ, lower < a → a * b ≤ limit → b ≤ cofactorCap)
    (divisorWeight cofactorWeight phase : ℕ → R)
    (cancellation : ∀ a : ℕ, lower < a → (∑ d ∈ a.divisors, divisorWeight d) = 0) :
    (∑ m ∈ range (limit + 1), upperBandWeight cutoff lower divisorWeight cofactorWeight m * phase m) =
      ∑ b ∈ Ioc cutoff cofactorCap, ∑ d ∈ Icc 1 (min cutoff (limit / b)),
        (-divisorWeight d) * cofactorWeight b *
          ∑ k ∈ Ioc (lower / d) (limit / (d * b)), phase (d * b * k) := by
  classical
  let term (d b k : ℕ) : R := (-divisorWeight d) * cofactorWeight b * phase (d * b * k)
  have removeZero :
      (∑ m ∈ range (limit + 1), upperBandWeight cutoff lower divisorWeight cofactorWeight m * phase m) =
        ∑ m ∈ Icc 1 limit, upperBandWeight cutoff lower divisorWeight cofactorWeight m * phase m := by
    symm
    refine sum_subset (fun m member => mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp member).2)) ?_
    intro m member outside
    have upper := Nat.lt_succ_iff.mp (mem_range.mp member)
    have zero : m = 0 := by
      by_contra nonzero
      exact outside (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr nonzero, upper⟩)
    simp [zero, upperBandWeight]
  calc
    _ = ∑ m ∈ Icc 1 limit, upperBandWeight cutoff lower divisorWeight cofactorWeight m * phase m :=
      removeZero
    _ = ∑ m ∈ Icc 1 limit, ∑ a ∈ m.divisors,
        if lower < a ∧ cutoff < m / a then
          ∑ d ∈ a.divisors, if d ≤ cutoff then term d (m / a) (a / d) else 0
        else 0 := by
      refine sum_congr rfl fun m _ => ?_
      rw [upperBandWeight, sum_filter, sum_mul]
      refine sum_congr rfl fun a divisor => ?_
      by_cases inBand : lower < a ∧ cutoff < m / a
      · have split :
            (∑ d ∈ a.divisors.filter (fun d => cutoff < d), divisorWeight d) =
              -(∑ d ∈ a.divisors.filter (fun d => d ≤ cutoff), divisorWeight d) := by
          apply eq_neg_iff_add_eq_zero.mpr
          rw [← cancellation a inBand.1]
          simpa only [not_lt] using
            sum_filter_add_sum_filter_not a.divisors (fun d => cutoff < d) divisorWeight
        simp only [inBand, and_self, ite_true]
        rw [split, ← sum_neg_distrib, sum_mul, sum_mul, sum_filter]
        refine sum_congr rfl fun d dDivisor => ?_
        by_cases small : d ≤ cutoff
        · have product : d * (m / a) * (a / d) = m := by
            calc
              _ = (d * (a / d)) * (m / a) := by ac_rfl
              _ = _ := by rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors dDivisor),
                Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors divisor)]
          simp only [small, ite_true, term, product]
        · simp [small]
      · simp [inBand]
    _ = ∑ b ∈ Ioc cutoff cofactorCap, ∑ d ∈ Icc 1 (min cutoff (limit / b)),
        ∑ k ∈ Ioc (lower / d) (limit / (d * b)), term d b k :=
      finite_divisor_triples limit cutoff lower cofactorCap cofactorCapLe cofactorBound term
    _ = _ := by
      refine sum_congr rfl fun b _ => sum_congr rfl fun d _ => ?_
      rw [mul_sum]

theorem cofactor_of_high_divisor {n a b : ℕ} (nPositive : 0 < n)
    (aLarge : ⌊(n : ℝ) ^ (7 / 12 : ℝ)⌋₊ < a) (product : a * b ≤ n) :
    b ≤ ⌊(n : ℝ) ^ (5 / 12 : ℝ)⌋₊ := by
  have realPositive : 0 < (n : ℝ) := Nat.cast_pos.mpr nPositive
  have aAbove : (n : ℝ) ^ (7 / 12 : ℝ) < (a : ℝ) := Nat.lt_of_floor_lt aLarge
  have aPositive : 0 < (a : ℝ) := (Real.rpow_pos_of_pos realPositive _).trans aAbove
  have productLe : (a : ℝ) * (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast product
  apply Nat.le_floor
  by_contra! bAbove
  have productLt : (n : ℝ) < (a : ℝ) * (b : ℝ) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (7 / 12 : ℝ) * (n : ℝ) ^ (5 / 12 : ℝ) := by
        rw [← Real.rpow_add realPositive]
        norm_num
      _ < (a : ℝ) * (n : ℝ) ^ (5 / 12 : ℝ) :=
        mul_lt_mul_of_pos_right aAbove (Real.rpow_pos_of_pos realPositive _)
      _ < _ := mul_lt_mul_of_pos_left bAbove aPositive
  exact (not_lt_of_ge productLe) productLt

end DyadicMixedB4Arithmetic

end

section

open Finset MeasureTheory DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters

namespace DyadicMixedB4ArcDecomposition

noncomputable section

/-- Adapted from the major-arc measurability proof in goldbach-proofs PR #2468,
revision 3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/
theorem wide_measurable (n B H : ℕ) : MeasurableSet (wide n B H) := by
  unfold wide
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases condition : 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q
  · obtain ⟨qPositive, qBound, aBound, coprime⟩ := condition
    simp only [qPositive, qBound, aBound, true_and]
    have equality : {x : ℝ | a.Coprime q ∧ |x - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)} =
        {x : ℝ | |x - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)} := by
      ext x
      exact ⟨And.right, And.intro coprime⟩
    rw [equality]
    exact measurableSet_le (f := fun t : ℝ => |t - (a : ℝ) / q|)
      (g := fun _ : ℝ => (H : ℝ) / ((q : ℝ) * n)) (by fun_prop) measurable_const
  · have empty : {t : ℝ | 1 ≤ q ∧ q ≤ B ∧ a ≤ q ∧ a.Coprime q ∧
        |t - (a : ℝ) / q| ≤ (H : ℝ) / ((q : ℝ) * n)} = ∅ := by
      ext t
      simp
      tauto
    rw [empty]
    exact MeasurableSet.empty

theorem indicator_intervalIntegrable {f : ℝ → ℂ} {s : Set ℝ} (continuous : Continuous f)
    (measurable : MeasurableSet s) : IntervalIntegrable (s.indicator f) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact (continuous.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator measurable

def plainPolynomial (n : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ range (n + 1), a m * phase ((m : ℝ) * t)

def shiftedPolynomial (n : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ range (n + 1), a m * phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)

theorem shiftedPolynomial_eq (n : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    shiftedPolynomial n a t = plainPolynomial n a t * phase (-(n : ℝ) * t) := by
  rw [shiftedPolynomial, plainPolynomial, sum_mul]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_assoc, ← phase_add, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  congr 2
  ring

theorem shiftedPolynomial_continuous (n : ℕ) (a : ℕ → ℂ) : Continuous (shiftedPolynomial n a) := by
  unfold shiftedPolynomial phase
  fun_prop

theorem norm_shiftedPolynomial_eq (n : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖shiftedPolynomial n a t‖ = ‖plainPolynomial n a t‖ := by
  rw [shiftedPolynomial_eq, norm_mul, norm_phase', mul_one]

theorem shiftedPolynomial_parseval (n : ℕ) (a : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖shiftedPolynomial n a t‖ ^ 2) = ∑ m ∈ range (n + 1), ‖a m‖ ^ 2 := by
  have exactMode (m : ℕ) (t : ℝ) : phase ((m : ℝ) * t) = DyadicMixedB4Fourier.mode (m : ℤ) t := by
    rw [BombieriVinogradov.LargeSieve.mode_nat_additivePhase]
    simp only [phase, BombieriVinogradov.LargeSieve.additivePhase, circleMap_zero, Complex.ofReal_one, one_mul]
  simp only [norm_shiftedPolynomial_eq, plainPolynomial, exactMode]
  exact DyadicMixedB4Fourier.parseval_real (n + 1) a

theorem split_shifted_wave (n M B H R g l r : ℕ) (a : ℕ → ℂ)
    (nPositive : 0 < n) (gPositive : 0 < g) (gBound : g ≤ M) (Bbound : B ≤ M)
    (width : 4 * H * M ≤ n) (Rpositive : 1 ≤ R) (Rbound : R ≤ B)
    (cover : (R : ℝ) * n * radius M ≤ H) :
    (∫ t in (0 : ℝ)..1, (wide n B H)ᶜ.indicator (fun x => shiftedPolynomial n a x * wave g l r x) t) =
      (∫ t in (0 : ℝ)..1, (wide n B H)ᶜ.indicator
        (fun x => shiftedPolynomial n a x * offWave (radius M) g l r x) t) +
      ∑ q ∈ g.divisors.filter (fun q => R < q), ∑ m ∈ range (n + 1), a m * ramanujan q ((m : ℤ) - n) *
        ∫ t in window n M B H q, phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) * wave g l r t := by
  classical
  let near := gridNear (radius M) g
  let outside := (wide n B H)ᶜ
  let f (t : ℝ) := shiftedPolynomial n a t * wave g l r t
  let off (t : ℝ) := shiftedPolynomial n a t * offWave (radius M) g l r t
  let v (m : ℕ) (t : ℝ) := phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) * wave g l r t
  have waveContinuous : Continuous (wave g l r) := by unfold wave phase; fun_prop
  have fContinuous : Continuous f := (shiftedPolynomial_continuous n a).mul waveContinuous
  have nearMeasurable : MeasurableSet near := gridNear_measurable (radius M) g
  have outsideMeasurable : MeasurableSet outside := (wide_measurable n B H).compl
  have offEqual : outside.indicator off = (outside ∩ nearᶜ).indicator f := by
    funext t
    by_cases nearMem : t ∈ near <;> by_cases outsideMem : t ∈ outside <;>
      simp_all only [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, Set.mem_compl_iff,
        not_true_eq_false, not_false_eq_true, and_true, and_false, false_and, true_and, mul_zero, off, near, offWave, f]
  have offInt : IntervalIntegrable (outside.indicator off) volume 0 1 := by
    rw [offEqual]
    exact indicator_intervalIntegrable fContinuous (outsideMeasurable.inter nearMeasurable.compl)
  have nearInt : IntervalIntegrable ((near ∩ outside).indicator f) volume 0 1 :=
    indicator_intervalIntegrable fContinuous (nearMeasurable.inter outsideMeasurable)
  have split (t : ℝ) : outside.indicator f t = outside.indicator off t + (near ∩ outside).indicator f t := by
    rw [offEqual]
    by_cases nearMem : t ∈ near <;> by_cases outsideMem : t ∈ outside <;> simp [nearMem, outsideMem]
  have expandNear (t : ℝ) : (near ∩ outside).indicator f t =
      ∑ m ∈ range (n + 1), a m * (near ∩ outside).indicator (v m) t := by
    by_cases membership : t ∈ near ∩ outside
    · simp only [Set.indicator_of_mem membership, f, shiftedPolynomial, sum_mul, v, mul_assoc]
    · simp [membership]
  have termInt (m : ℕ) : IntervalIntegrable (fun t => a m * (near ∩ outside).indicator (v m) t) volume 0 1 := by
    have continuousMode : Continuous (fun t : ℝ => phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)) := by
      unfold phase
      fun_prop
    exact (indicator_intervalIntegrable (continuousMode.mul waveContinuous)
      (nearMeasurable.inter outsideMeasurable)).const_mul (a m)
  change (∫ t in (0 : ℝ)..1, outside.indicator f t) = (∫ t in (0 : ℝ)..1, outside.indicator off t) + _
  calc
    _ = ∫ t in (0 : ℝ)..1, outside.indicator off t + (near ∩ outside).indicator f t :=
      intervalIntegral.integral_congr fun t _ => split t
    _ = (∫ t in (0 : ℝ)..1, outside.indicator off t) + ∫ t in (0 : ℝ)..1, (near ∩ outside).indicator f t :=
      intervalIntegral.integral_add offInt nearInt
    _ = _ := by
      congr 1
      simp_rw [expandNear]
      rw [intervalIntegral.integral_finsetSum (fun m _ => termInt m)]
      simp_rw [intervalIntegral.integral_const_mul]
      have identify (m : ℕ) : (∫ t in (0 : ℝ)..1, (near ∩ outside).indicator (v m) t) =
          ∑ q ∈ g.divisors.filter (fun q => R < q), ramanujan q ((m : ℤ) - n) *
            ∫ t in window n M B H q, v m t :=
        centered_deep_wave_integral n M B H R g l r ((m : ℤ) - n)
          nPositive gPositive gBound Bbound width Rpositive Rbound cover
      simp_rw [identify, mul_sum]
      rw [sum_comm]
      simp only [v, mul_assoc]

end
end DyadicMixedB4ArcDecomposition

end

section

open Finset ArithmeticFunction DyadicMixedB4Arithmetic DyadicMixedB4Scale
open DyadicMixedB4ArcDecomposition DyadicMixedB4Geometric DyadicMixedB4MoebiusGauss
open scoped ArithmeticFunction.Moebius

namespace DyadicMixedB4HighAtoms

noncomputable section

def atomStep (atom : ℕ × ℕ) : ℕ := atom.1 * atom.2
def atomLower (threshold : ℕ) (atom : ℕ × ℕ) : ℕ := threshold / atom.1
def atomUpper (n : ℕ) (atom : ℕ × ℕ) : ℕ := n / atomStep atom

end
end DyadicMixedB4HighAtoms

end

section

open Finset ArithmeticFunction DyadicMixedB4Arithmetic
open scoped ArithmeticFunction.Moebius

namespace DyadicMixedB4LowBand

noncomputable section

def lowMoebiusWeight (U a : ℕ) : ℝ := ∑ d ∈ a.divisors.filter (fun d => U < d), (μ d : ℝ)

def lowBandCoefficient (U B m : ℕ) : ℝ :=
  ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a), lowMoebiusWeight U a * Λ (m / a)

theorem abs_lowMoebiusWeight_le (U a : ℕ) : |lowMoebiusWeight U a| ≤ (a.divisors.card : ℝ) := by
  have bound : ‖lowMoebiusWeight U a‖ ≤ (a.divisors.card : ℝ) := by
    unfold lowMoebiusWeight
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ d ∈ a.divisors.filter (fun d => U < d), (1 : ℝ) := by
        refine sum_le_sum fun d _ => ?_
        rw [Real.norm_eq_abs]
        exact_mod_cast (abs_moebius_le_one (n := d))
      _ ≤ ∑ d ∈ a.divisors, (1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => zero_le_one)
      _ = _ := by simp
  simpa only [Real.norm_eq_abs] using bound

theorem abs_lowBandCoefficient_le (U B m n : ℕ) (mBound : m ≤ n) (nPositive : 0 < n) :
    |lowBandCoefficient U B m| ≤ (m.divisors.card : ℝ) ^ 2 * Real.log n := by
  have nRealLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have logNonnegative : 0 ≤ Real.log n := Real.log_nonneg nRealLower
  have logLambda (a : ℕ) (member : a ∈ m.divisors) : Λ (m / a) ≤ Real.log n := by
    have aDivides := Nat.dvd_of_mem_divisors member
    have mPositive : 0 < m := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors member)
    have aPositive := Nat.pos_of_mem_divisors member
    have quotientPositive := Nat.div_pos (Nat.le_of_dvd mPositive aDivides) aPositive
    refine vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast quotientPositive) ?_)
    exact_mod_cast (Nat.div_le_self m a).trans mBound
  have tau (a : ℕ) (member : a ∈ m.divisors) : (a.divisors.card : ℝ) ≤ m.divisors.card := by
    apply Nat.cast_le.mpr
    apply card_le_card
    intro d dMember
    exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors dMember).trans (Nat.dvd_of_mem_divisors member),
      Nat.ne_zero_of_mem_divisors member⟩
  rw [← Real.norm_eq_abs, lowBandCoefficient]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a), (m.divisors.card : ℝ) * Real.log n := by
      refine sum_le_sum fun a membership => ?_
      have divisor := (mem_filter.mp membership).1
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_mul ((abs_lowMoebiusWeight_le U a).trans (tau a divisor)) (logLambda a divisor)
        vonMangoldt_nonneg (Nat.cast_nonneg _)
    _ ≤ ∑ _ ∈ m.divisors, (m.divisors.card : ℝ) * Real.log n :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) logNonnegative)
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

theorem low_band_hyperbola (n U B : ℕ) (Bbound : B ≤ n) (f : ℕ → ℂ) :
    (∑ m ∈ range (n + 1), (lowBandCoefficient U B m : ℂ) * f m) =
      ∑ a ∈ Ioc U B, (lowMoebiusWeight U a : ℂ) *
        ∑ b ∈ Ioc U (n / a), (Λ b : ℂ) * f (a * b) := by
  let term (a b : ℕ) : ℂ := (lowMoebiusWeight U a : ℂ) * ((Λ b : ℂ) * f (a * b))
  let supported (a b : ℕ) : ℂ := if U < a ∧ a ≤ B ∧ U < b then term a b else 0
  have partition : range (n + 1) = insert 0 (Icc 1 n) := by ext m; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [partition, sum_insert (by simp)]
  simp only [lowBandCoefficient, Nat.divisors_zero, filter_empty, sum_empty, Complex.ofReal_zero, zero_mul, zero_add]
  calc
    _ = ∑ m ∈ Icc 1 n, ∑ a ∈ m.divisors, supported a (m / a) := by
      refine sum_congr rfl fun m _ => ?_
      rw [Complex.ofReal_sum, sum_mul, sum_filter]
      refine sum_congr rfl fun a aMember => ?_
      by_cases cond : U < a ∧ a ≤ B ∧ U < m / a
      · simp only [supported, term, if_pos cond, Complex.ofReal_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors aMember)]
        ring
      · simp [supported, cond]
    _ = ∑ a ∈ Icc 1 n, ∑ b ∈ Icc 1 (n / a), supported a b := finite_divisor_hyperbola n supported
    _ = ∑ a ∈ (Icc 1 n).filter (fun a => U < a ∧ a ≤ B),
        ∑ b ∈ (Icc 1 (n / a)).filter (fun b => U < b), term a b := by
      rw [sum_filter]
      refine sum_congr rfl fun a _ => ?_
      by_cases cond : U < a ∧ a ≤ B
      · rw [if_pos cond, sum_filter]
        exact sum_congr rfl fun b _ => by simp [supported, cond.1, cond.2]
      · rw [if_neg cond]
        exact sum_eq_zero fun b _ => if_neg (fun h => cond ⟨h.1, h.2.1⟩)
    _ = _ := by
      have intervalA : (Icc 1 n).filter (fun a => U < a ∧ a ≤ B) = Ioc U B := by
        ext a
        simp only [mem_filter, mem_Icc, mem_Ioc]
        omega
      have intervalB (a : ℕ) : (Icc 1 (n / a)).filter (fun b => U < b) = Ioc U (n / a) := by
        ext b
        simp only [mem_filter, mem_Icc, mem_Ioc]
        omega
      simp_rw [intervalA, intervalB, term, ← mul_sum]

end
end DyadicMixedB4LowBand

end

section

open Finset MeasureTheory DyadicMixedB4Geometric

namespace DyadicMixedB4OffWaveMoment

noncomputable section

theorem wave_continuous (g l r : ℕ) : Continuous (wave g l r) := by unfold wave phase; fun_prop

theorem offWave_measurable (b : ℝ) (g l r : ℕ) : Measurable (offWave b g l r) :=
  (wave_continuous g l r).measurable.indicator (gridNear_measurable b g).compl

theorem norm_offWave_le (b : ℝ) (g l r : ℕ) (t : ℝ) : ‖offWave b g l r t‖ ≤ r := by
  unfold offWave
  by_cases outside : t ∈ (gridNear b g)ᶜ
  · rw [Set.indicator_of_mem outside]
    exact wave_cap g l r t
  · rw [Set.indicator_of_notMem outside, norm_zero]
    exact Nat.cast_nonneg _

theorem intervalIntegrable_offWave_norm_sq {ι : Type*} (items : Finset ι) (b : ℝ)
    (g l r : ι → ℕ) (c : ι → ℂ) :
    IntervalIntegrable (fun t => ‖∑ i ∈ items, c i * offWave b (g i) (l i) (r i) t‖ ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have measurable : Measurable (fun t => ∑ i ∈ items, c i * offWave b (g i) (l i) (r i) t) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (offWave_measurable b (g i) (l i) (r i)))
  apply Integrable.of_bound (measurable.norm.pow_const 2).aestronglyMeasurable
    ((∑ i ∈ items, ‖c i‖ * (r i : ℝ)) ^ 2)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  refine (norm_sum_le _ _).trans (sum_le_sum (fun i _ => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_offWave_le b (g i) (l i) (r i) t) (norm_nonneg _)

theorem offWave_mass_le_pairwise {ι : Type*} (items : Finset ι) (n : ℕ) (b : ℝ)
    (bPositive : 0 < b) (g l r : ι → ℕ) (c : ι → ℂ)
    (gRange : ∀ i ∈ items, 0 < g i ∧ g i ≤ n) (rRange : ∀ i ∈ items, r i ≤ n / g i) :
    (∫ t in (0 : ℝ)..1, ‖∑ i ∈ items, c i * offWave b (g i) (l i) (r i) t‖ ^ 2) ≤
      ∑ i ∈ items, ∑ j ∈ items, (‖c i‖ * ‖c j‖) * (128 * ((1 + Real.log ((n : ℝ) + 2)) ^ 2 +
        ((g i).gcd (g j) : ℝ) / ((g i : ℝ) * (g j : ℝ) * b))) := by
  let H (i j : ι) : ℝ → ℝ := (gridNear b ((g i).gcd (g j)))ᶜ.indicator
    (fun t => ‖wave (g i) (l i) (r i) t * wave (g j) (l j) (r j) t‖)
  let P (i j : ι) (t : ℝ) : ℝ := (‖c i‖ * ‖c j‖) * H i j t
  let f (t : ℝ) : ℝ := ‖∑ i ∈ items, c i * offWave b (g i) (l i) (r i) t‖ ^ 2
  have fIntegrable : IntervalIntegrable f volume 0 1 := intervalIntegrable_offWave_norm_sq items b g l r c
  have HIntegrable (i j : ι) : IntervalIntegrable (H i j) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have continuous : Continuous (fun t => ‖wave (g i) (l i) (r i) t * wave (g j) (l j) (r j) t‖) :=
      ((wave_continuous _ _ _).mul (wave_continuous _ _ _)).norm
    exact (continuous.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
      (gridNear_measurable b ((g i).gcd (g j))).compl
  have pairIntegrable (i j : ι) : IntervalIntegrable (P i j) volume 0 1 :=
    (HIntegrable i j).const_mul (‖c i‖ * ‖c j‖)
  have rowIntegrable (i : ι) : IntervalIntegrable (fun t => ∑ j ∈ items, P i j t) volume 0 1 := by
    have integrated := IntervalIntegrable.sum items (fun j _ => pairIntegrable i j)
    convert integrated using 1
    funext t
    simp only [Finset.sum_apply]
  have sumIntegrable : IntervalIntegrable (fun t => ∑ i ∈ items, ∑ j ∈ items, P i j t) volume 0 1 := by
    have integrated := IntervalIntegrable.sum items (fun i _ => rowIntegrable i)
    convert integrated using 1
    funext t
    simp only [Finset.sum_apply]
  have pointwise (t : ℝ) : f t ≤ ∑ i ∈ items, ∑ j ∈ items, P i j t := by
    calc
      _ ≤ (∑ i ∈ items, ‖c i * offWave b (g i) (l i) (r i) t‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ = ∑ i ∈ items, ∑ j ∈ items, (‖c i‖ * ‖c j‖) *
          ‖offWave b (g i) (l i) (r i) t * offWave b (g j) (l j) (r j) t‖ := by
        rw [pow_two, sum_mul_sum]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        simp only [norm_mul]
        ring
      _ ≤ _ := by
        refine sum_le_sum fun i iMember => sum_le_sum fun j jMember => ?_
        exact mul_le_mul_of_nonneg_left
          (norm_offWave_mul_le b (gRange i iMember).1 (gRange j jMember).1 _ _ _ _ t)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  change (∫ t in (0 : ℝ)..1, f t) ≤ _
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, ∑ i ∈ items, ∑ j ∈ items, P i j t :=
      intervalIntegral.integral_mono_on zero_le_one fIntegrable sumIntegrable (fun t _ => pointwise t)
    _ = ∑ i ∈ items, ∑ j ∈ items, (‖c i‖ * ‖c j‖) * ∫ t in (0 : ℝ)..1, H i j t := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => rowIntegrable i)]
      refine sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finsetSum (fun j _ => pairIntegrable i j)]
      exact sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      refine sum_le_sum fun i iMember => sum_le_sum fun j jMember => ?_
      exact mul_le_mul_of_nonneg_left (awayBound n (g i) (g j) (l i) (r i) (l j) (r j) b bPositive
        (gRange i iMember).1 (gRange j jMember).1 (gRange i iMember).2 (gRange j jMember).2
        (rRange i iMember) (rRange j jMember)) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem sum_step_pairs {ι : Type*} (items : Finset ι) (steps : Finset ℕ)
    (g : ι → ℕ) (weight : ι → ℝ) (F : ℕ → ℕ → ℝ) (mapsInto : ∀ i ∈ items, g i ∈ steps) :
    (∑ i ∈ items, ∑ j ∈ items, weight i * weight j * F (g i) (g j)) =
      ∑ u ∈ steps, ∑ v ∈ steps, (∑ i ∈ items.filter (fun i => g i = u), weight i) *
        (∑ j ∈ items.filter (fun j => g j = v), weight j) * F u v := by
  calc
    _ = ∑ u ∈ steps, ∑ i ∈ items.filter (fun i => g i = u), ∑ j ∈ items, weight i * weight j * F (g i) (g j) :=
      (sum_fiberwise_of_maps_to mapsInto _).symm
    _ = ∑ u ∈ steps, ∑ v ∈ steps, ∑ i ∈ items.filter (fun i => g i = u),
        ∑ j ∈ items.filter (fun j => g j = v), weight i * weight j * F (g i) (g j) := by
      refine sum_congr rfl fun u _ => ?_
      have inner (i : ι) : (∑ j ∈ items, weight i * weight j * F (g i) (g j)) =
          ∑ v ∈ steps, ∑ j ∈ items.filter (fun j => g j = v), weight i * weight j * F (g i) (g j) :=
        (sum_fiberwise_of_maps_to mapsInto _).symm
      simp_rw [inner]
      exact sum_comm
    _ = _ := by
      refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
      rw [sum_mul_sum, sum_mul]
      refine sum_congr rfl fun i iMember => ?_
      rw [sum_mul]
      refine sum_congr rfl fun j jMember => ?_
      rw [(mem_filter.mp iMember).2, (mem_filter.mp jMember).2]

theorem offWave_mass_le_weighted {ι : Type*} (items : Finset ι) (n M : ℕ) (b W : ℝ)
    (MPositive : 0 < M) (MBound : M ≤ n) (bPositive : 0 < b) (WNonnegative : 0 ≤ W)
    (g l r : ι → ℕ) (c : ι → ℂ) (gRange : ∀ i ∈ items, 0 < g i ∧ g i ≤ M)
    (rRange : ∀ i ∈ items, r i ≤ n / g i)
    (weightBound : ∀ u ∈ Icc 1 M, (∑ i ∈ items.filter (fun i => g i = u), ‖c i‖) ≤ W) :
    (∫ t in (0 : ℝ)..1, ‖∑ i ∈ items, c i * offWave b (g i) (l i) (r i) t‖ ^ 2) ≤
      128 * W ^ 2 * ((M : ℝ) ^ 2 * (1 + Real.log ((n : ℝ) + 2)) ^ 2 +
        b⁻¹ * (1 + Real.log (M : ℝ)) ^ 3) := by
  let J := (1 + Real.log ((n : ℝ) + 2)) ^ 2
  let F (u v : ℕ) : ℝ := 128 * (J + (u.gcd v : ℝ) / ((u : ℝ) * (v : ℝ) * b))
  have mapsInto (i : ι) (member : i ∈ items) : g i ∈ Icc 1 M := mem_Icc.mpr (gRange i member)
  have first := offWave_mass_le_pairwise items n b bPositive g l r c
    (fun i member => ⟨(gRange i member).1, (gRange i member).2.trans MBound⟩) rRange
  change _ ≤ ∑ i ∈ items, ∑ j ∈ items, ‖c i‖ * ‖c j‖ * F (g i) (g j) at first
  rw [sum_step_pairs items (Icc 1 M) g (fun i => ‖c i‖) F mapsInto] at first
  have positiveF (u v : ℕ) : 0 ≤ F u v := by unfold F J; positivity
  have pairBound : (∑ u ∈ Icc 1 M, ∑ v ∈ Icc 1 M,
      (∑ i ∈ items.filter (fun i => g i = u), ‖c i‖) *
        (∑ j ∈ items.filter (fun j => g j = v), ‖c j‖) * F u v) ≤
      ∑ u ∈ Icc 1 M, ∑ v ∈ Icc 1 M, W ^ 2 * F u v := by
    refine sum_le_sum fun u uMember => sum_le_sum fun v vMember => ?_
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (weightBound u uMember) (weightBound v vMember)
        (sum_nonneg (fun _ _ => norm_nonneg _)) WNonnegative) (positiveF u v)
  refine (first.trans pairBound).trans ?_
  have expand (u v : ℕ) : W ^ 2 * F u v =
      128 * W ^ 2 * (J + b⁻¹ * ((u.gcd v : ℝ) / ((u : ℝ) * (v : ℝ)))) := by
    unfold F
    ring
  simp_rw [expand, ← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have cardinality : (Icc 1 M).card = M := by simp
  simp only [sum_add_distrib, sum_const, cardinality, nsmul_eq_mul, ← mul_sum]
  have gcdBound := DyadicMixedB4GcdHarmonic.gcd_reciprocal_sum_le M MPositive
  have constantTerm : (M : ℝ) * ((M : ℝ) * J) = (M : ℝ) ^ 2 * J := by ring
  rw [constantTerm]
  exact add_le_add_right (mul_le_mul_of_nonneg_left gcdBound (by positivity)) _

end
end DyadicMixedB4OffWaveMoment

end

section

open MeasureTheory

namespace DyadicMixedB4YoungIntegral

theorem scaled_young {s x y : ℝ} (sPositive : 0 < s) :
    x * y ≤ (1 / 2) * (s * x ^ 2 + s⁻¹ * y ^ 2) := by
  have multiplied : (2 * x * y - s * x ^ 2) * s ≤ y ^ 2 := by
    nlinarith only [sq_nonneg (s * x - y)]
  have divided := (le_div_iff₀ sPositive).mpr multiplied
  rw [inv_mul_eq_div]
  linarith only [divided]

theorem norm_indicator_product_le {f g : ℝ → ℂ} {s : Set ℝ} {scale : ℝ}
    (scalePositive : 0 < scale) (sMeasurable : MeasurableSet s) (fMeasurable : Measurable f)
    (gMeasurable : Measurable g)
    (fSquareIntegrable : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 1)
    (gSquareIntegrable : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume 0 1) :
    ‖∫ t in (0 : ℝ)..1, s.indicator (fun x => f x * g x) t‖ ≤
      (1 / 2) * (scale * (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) +
        scale⁻¹ * (∫ t in (0 : ℝ)..1, ‖g t‖ ^ 2)) := by
  let product := s.indicator (fun t => f t * g t)
  let bound (t : ℝ) := (1 / 2) * (scale * ‖f t‖ ^ 2 + scale⁻¹ * ‖g t‖ ^ 2)
  have productMeasurable : Measurable product := (fMeasurable.mul gMeasurable).indicator sMeasurable
  have firstIntegrable : IntervalIntegrable (fun t => scale * ‖f t‖ ^ 2) volume 0 1 :=
    fSquareIntegrable.const_mul scale
  have secondIntegrable : IntervalIntegrable (fun t => scale⁻¹ * ‖g t‖ ^ 2) volume 0 1 :=
    gSquareIntegrable.const_mul scale⁻¹
  have sumIntegrable : IntervalIntegrable (fun t => scale * ‖f t‖ ^ 2 + scale⁻¹ * ‖g t‖ ^ 2) volume 0 1 :=
    firstIntegrable.add secondIntegrable
  have boundIntegrable : IntervalIntegrable bound volume 0 1 := sumIntegrable.const_mul (1 / 2)
  have pointwise (t : ℝ) : ‖product t‖ ≤ bound t := by
    unfold product bound
    by_cases member : t ∈ s
    · rw [Set.indicator_of_mem member, norm_mul]
      exact scaled_young scalePositive
    · rw [Set.indicator_of_notMem member, norm_zero]
      positivity
  have productIntegrable : IntervalIntegrable product volume 0 1 := boundIntegrable.mono_fun'
    productMeasurable.aestronglyMeasurable (Filter.Eventually.of_forall pointwise)
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, ‖product t‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, bound t := intervalIntegral.integral_mono_on zero_le_one productIntegrable.norm
      boundIntegrable (fun t _ => pointwise t)
    _ = _ := by
      unfold bound
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add firstIntegrable secondIntegrable,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end DyadicMixedB4YoungIntegral

end

section

open Finset MeasureTheory DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4ArcDecomposition

namespace DyadicMixedB4PairIntegral

noncomputable section

def lowCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

def lowCoefficients (n m : ℕ) : ℂ := (lowBandCoefficient (cutoffU n) (lowCut n) m : ℂ)

def secondPolynomialIntegral (n : ℕ) (g : ℝ → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator
    (fun x => plainPolynomial n (lowCoefficients n) x * g x * phase (-(n : ℝ) * x)) t

def exactNearAtom (n threshold : ℕ) (i : ℕ × ℕ) (q : ℕ) : ℂ :=
  ∑ m ∈ range (n + 1), lowCoefficients n m * ramanujan q ((m : ℤ) - n) *
    ∫ t in window n (maximumStep n) (cutoffB n) (cutoffH n) q,
      phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) * wave (atomStep i) (atomLower threshold i) (atomUpper n i) t

end
end DyadicMixedB4PairIntegral

end

section

open Finset MeasureTheory DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4ProgressionApprox DyadicMixedB4WindowKernel DyadicMixedB4KernelControl DyadicMixedB4Ramanujan

namespace DyadicMixedB4NearReplacement

noncomputable section

theorem norm_windowKernel_difference_le (n M B H q g l r : ℕ) (s : ℝ)
    (gPositive : 0 < g) (radiusBound : (g : ℝ) * radius M ≤ 1 / 2) :
    ‖(∫ t in window n M B H q, phase (s * t) * wave g l r t) -
      (windowKernel n M B H q g l r s : ℂ)‖ ≤ 2 * Real.pi * (2 * radius M) := by
  have phaseContinuous : Continuous (fun t => phase (s * t)) := by unfold phase; fun_prop
  have waveContinuous : Continuous (wave g l r) := by unfold wave phase; fun_prop
  have waveIntegrable : IntegrableOn (fun t => phase (s * t) * wave g l r t) (window n M B H q) :=
    ((phaseContinuous.mul waveContinuous).continuousOn.integrableOn_Icc).mono_set (window_subset_interval n M B H q)
  have averageIntegrable : IntegrableOn (fun t => phase (s * t) * progressionAverage g l r t) (window n M B H q) :=
    ((phaseContinuous.mul (progressionAverage_continuous g l r)).continuousOn.integrableOn_Icc).mono_set
      (window_subset_interval n M B H q)
  change ‖(∫ t in window n M B H q, phase (s * t) * wave g l r t) -
    Complex.ofReal (scalarKernel g l r (radius M) s -
      if q ≤ B then scalarKernel g l r (innerRadius n M H q) s else 0)‖ ≤ _
  rw [← integral_progression_window, ← integral_sub waveIntegrable averageIntegrable]
  simp only [← mul_sub]
  exact norm_window_replacement_le n M B H q g l r s gPositive radiusBound

theorem norm_sum_windowKernel_difference_le (n M B H q g l r : ℕ) [NeZero q] (a : ℕ → ℂ)
    (qLower : 1 < q) (gPositive : 0 < g) (radiusBound : (g : ℝ) * radius M ≤ 1 / 2)
    {A : ℝ} (aBound : ∀ m ∈ range (n + 1), ‖a m‖ ≤ A) (ANonnegative : 0 ≤ A) :
    ‖(∑ m ∈ range (n + 1), a m * ramanujan q ((m : ℤ) - n) *
        ∫ t in window n M B H q, phase ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) * wave g l r t) -
      ∑ m ∈ range (n + 1), a m * ramanujan q ((m : ℤ) - n) *
        (windowKernel n M B H q g l r (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) : ℂ)‖ ≤
      (A * (2 * Real.pi * (2 * radius M))) * ((q.divisors.card : ℝ) * ((n : ℝ) + q)) := by
  let C := 2 * Real.pi * (2 * radius M)
  rw [← sum_sub_distrib]
  simp only [← mul_sub]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ m ∈ range (n + 1), (A * C) * ‖ramanujan q ((m : ℤ) - n)‖ := by
      refine sum_le_sum fun m membership => ?_
      simp only [norm_mul]
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (aBound m membership)
          (norm_windowKernel_difference_le n M B H q g l r (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) gPositive radiusBound)
          (norm_nonneg _) ANonnegative) (norm_nonneg _)
    _ = (A * C) * ∑ m ∈ range (n + 1), ‖ramanujan q ((m : ℤ) - n)‖ := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_norm_shifted_ramanujan_le qLower n)
      (mul_nonneg ANonnegative (by dsimp [C]; exact mul_nonneg (by positivity) (mul_nonneg (by norm_num) (radius_nonnegative M))))

end
end DyadicMixedB4NearReplacement

end

section

open Finset ArithmeticFunction DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4PairIntegral
open DyadicMixedB4KernelControl DyadicMixedB4NearReplacement

namespace DyadicMixedB4NearPair

noncomputable section

def smoothKernelFactor (n threshold : ℕ) (i : ℕ × ℕ) (q m : ℕ) : ℂ :=
  ramanujan q ((m : ℤ) - n) *
    (windowKernel n (maximumStep n) (cutoffB n) (cutoffH n) q (atomStep i) (atomLower threshold i) (atomUpper n i)
      (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) : ℂ)

def smoothedNearAtom (n threshold : ℕ) (i : ℕ × ℕ) (q : ℕ) : ℂ :=
  ∑ m ∈ range (n + 1), lowCoefficients n m * smoothKernelFactor n threshold i q m

theorem smoothedNearAtom_hyperbola (n threshold : ℕ) (i : ℕ × ℕ) (q : ℕ) (nPositive : 0 < n) :
    smoothedNearAtom n threshold i q = ∑ a ∈ Ioc (cutoffU n) (lowCut n), (lowMoebiusWeight (cutoffU n) a : ℂ) *
      ∑ b ∈ Ioc (cutoffU n) (n / a), (Λ b : ℂ) * smoothKernelFactor n threshold i q (a * b) := by
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have Bbound : lowCut n ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nLower (by norm_num))
  exact low_band_hyperbola n (cutoffU n) (lowCut n) Bbound (smoothKernelFactor n threshold i q)

end
end DyadicMixedB4NearPair

end

section

open Finset ArithmeticFunction DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Geometric
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4PairIntegral
open DyadicMixedB4KernelControl DyadicMixedB4NearPair DyadicMixedB4PrimitiveAt

namespace DyadicMixedB4PrimitiveNearPair

noncomputable section

def primitiveNearAtom (n threshold : ℕ) (i : ℕ × ℕ) (q : ℕ) : ℂ := ∑ a ∈ Ioc (cutoffU n) (lowCut n),
  (lowMoebiusWeight (cutoffU n) a : ℂ) *
    ∑ b ∈ Ioc (cutoffU n) (n / a), (Λ b : ℂ) * (primitiveAt q n a b *
      (windowKernel n (maximumStep n) (cutoffB n) (cutoffH n) q (atomStep i) (atomLower threshold i) (atomUpper n i)
        (((((a * b : ℕ) : ℤ) - (n : ℤ)) : ℝ)) : ℂ))

set_option maxHeartbeats 800000 in
theorem norm_smoothedNearAtom_sub_primitive_le (n threshold : ℕ) (i : ℕ × ℕ) (q : ℕ) (nPositive : 0 < n)
    (qLower : 1 < q) (qBound : q ≤ n) {T : ℝ} (TNonnegative : 0 ≤ T)
    (tBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖smoothedNearAtom n threshold i q - primitiveNearAtom n threshold i q‖ ≤
      (16 * (lowCut n : ℝ) * T ^ 2 * (1 + T) * (Nat.log 2 n : ℝ) * Real.log n) / (atomStep i : ℝ) * q := by
  let V : ℝ := 16 / (atomStep i : ℝ)
  let E : ℝ := (V * ((q : ℝ) * (1 + T))) * (T * (Nat.log 2 n : ℝ) * Real.log n)
  have logNonnegative : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast nPositive)
  have VNonnegative : 0 ≤ V := by unfold V; positivity
  have ENonnegative : 0 ≤ E := by unfold E; positivity
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have lowBound : lowCut n ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nLower (by norm_num))
  let K (a b : ℕ) := (windowKernel n (maximumStep n) (cutoffB n) (cutoffH n) q
    (atomStep i) (atomLower threshold i) (atomUpper n i) (((((a * b : ℕ) : ℤ) - (n : ℤ)) : ℝ)) : ℂ)
  have boundAt (a : ℕ) : ‖∑ b ∈ Ioc (cutoffU n) (n / a), (Λ b : ℂ) *
      ((ramanujan q (((a * b : ℕ) : ℤ) - (n : ℤ)) - primitiveAt q n a b) * K a b)‖ ≤ E := by
    have within : Ioc (cutoffU n) (n / a) ⊆ Icc 1 n := by
      intro b member
      obtain ⟨lower, upper⟩ := mem_Ioc.mp member
      exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt lower, upper.trans (Nat.div_le_self n a)⟩
    have kernelBound (b : ℕ) (_ : b ∈ Ioc (cutoffU n) (n / a)) : ‖K a b‖ ≤ V := by
      unfold K V
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_windowKernel_le _ _ _ _ _ _ _ _ _
    have estimate := norm_mangoldt_replacement_le qLower nPositive a _ within (K a) VNonnegative kernelBound
    refine estimate.trans ?_
    unfold E
    have rBound : reducedModulus q a ≤ n := (Nat.div_le_self q (a.gcd q)).trans qBound
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add_right (tBound n le_rfl) 1) (Nat.cast_nonneg _)) VNonnegative
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (tBound _ rBound) (Nat.cast_nonneg _)) logNonnegative
    · positivity
    · positivity
  rw [smoothedNearAtom_hyperbola n threshold i q nPositive]
  unfold primitiveNearAtom smoothKernelFactor
  rw [← sum_sub_distrib]
  simp only [← mul_sub, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ Ioc (cutoffU n) (lowCut n), T * E := by
      refine sum_le_sum fun a member => ?_
      have within := (mem_Ioc.mp member).2.trans lowBound
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul ((abs_lowMoebiusWeight_le (cutoffU n) a).trans (tBound a within))
        (by simpa only [Int.cast_sub, sub_mul, K] using boundAt a) (norm_nonneg _) TNonnegative
    _ ≤ ∑ _ ∈ Icc 1 (lowCut n), T * E := by
      refine sum_le_sum_of_subset_of_nonneg (fun a member => ?_) (fun _ _ _ => mul_nonneg TNonnegative ENonnegative)
      obtain ⟨lower, upper⟩ := mem_Ioc.mp member
      exact mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt lower, upper⟩
    _ = _ := by unfold E V; rw [sum_const, nsmul_eq_mul]; simp; ring

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

def shortIndices (n k : ℕ) : Finset ℕ :=
  (Ioc (cutoffU n) (lowCut n)).filter (fun a => Nat.log 2 a = k)

theorem lowCut_le (n : ℕ) (nPositive : 0 < n) : lowCut n ≤ n :=
  Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast nPositive) (by norm_num))

end
end DyadicMixedB4NearMain

end

section

open DyadicMixedB4Scale DyadicMixedB4ArcGeometry DyadicMixedB4EnergyTail
open DyadicMixedB4PairIntegral DyadicMixedB4TailScale

namespace DyadicMixedB4NumericBudgets

noncomputable section

def finalScale (n : ℕ) (T : ℝ) : ℝ :=
  T ^ 5 * logBudget n ^ 7 * (n : ℝ) ^ (255 / 256 : ℝ)

def outsideScale (n : ℕ) : ℝ := (maximumStep n : ℝ) / Real.sqrt n

theorem maximumStep_real_positive (n : ℕ) (nPositive : 0 < n) : (0 : ℝ) < maximumStep n := by
  obtain ⟨rPositive, rB, bM, _⟩ := cutoffs_ordered n nPositive
  exact_mod_cast rPositive.trans (rB.trans bM)

theorem outsideScale_positive (n : ℕ) (nPositive : 0 < n) : 0 < outsideScale n :=
  div_pos (maximumStep_real_positive n nPositive) (Real.sqrt_pos_of_pos (by exact_mod_cast nPositive))

theorem outside_budget_le (n : ℕ) (nPositive : 0 < n) {T : ℝ} (TLower : 1 ≤ T) :
    let A := T ^ 2 * logBudget n
    let W := T * logBudget n
    (1 / 2) * (outsideScale n * (((n : ℝ) + 1) * A ^ 2) +
      (outsideScale n)⁻¹ * (128 * W ^ 2 * ((maximumStep n : ℝ) ^ 2 * logBudget n ^ 2 +
        (radius (maximumStep n))⁻¹ * (1 + Real.log (maximumStep n : ℝ)) ^ 3))) ≤ 600 * finalScale n T := by
  dsimp only
  let A := T ^ 2 * logBudget n
  let W := T * logBudget n
  let B := logBudget n
  let M := (maximumStep n : ℝ)
  let S := outsideScale n
  have mPositive : 0 < M := maximumStep_real_positive n nPositive
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have root : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos nReal
  have SPositive : 0 < S := outsideScale_positive n nPositive
  have BLower : 1 ≤ B := one_le_logBudget n
  have BNonnegative : 0 ≤ B := zero_le_one.trans BLower
  have TNonnegative : 0 ≤ T := zero_le_one.trans TLower
  have HNonnegative : 0 ≤ 1 + Real.log M := add_nonneg zero_le_one (Real.log_nonneg (by
    obtain ⟨rPositive, rB, bM, _⟩ := cutoffs_ordered n nPositive
    unfold M
    exact_mod_cast rPositive.trans (rB.trans bM)))
  have radiusInv : (radius (maximumStep n))⁻¹ = 8 * M ^ 2 := by unfold radius M; rw [one_div, inv_inv]
  have nDivSqrt : (n : ℝ) / Real.sqrt n = Real.sqrt n := by
    apply (div_eq_iff root.ne').mpr
    rw [← pow_two, Real.sq_sqrt nReal.le]
  have first : S * (((n : ℝ) + 1) * A ^ 2) ≤ 2 * Real.sqrt n * M * A ^ 2 := by
    calc
      _ ≤ S * ((2 * (n : ℝ)) * A ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith only [nLower]) (sq_nonneg _)) SPositive.le
      _ = _ := by
        change (M / Real.sqrt n) * ((2 * (n : ℝ)) * A ^ 2) = _
        calc
          _ = 2 * ((n : ℝ) / Real.sqrt n) * M * A ^ 2 := by ring
          _ = _ := by rw [nDivSqrt]
  have inner : M ^ 2 * B ^ 2 + (radius (maximumStep n))⁻¹ * (1 + Real.log M) ^ 3 ≤ 9 * M ^ 2 * B ^ 3 := by
    rw [radiusInv]
    calc
      _ ≤ M ^ 2 * B ^ 3 + (8 * M ^ 2) * B ^ 3 :=
        (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ BLower (by decide : 2 ≤ 3)) (sq_nonneg _))
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ HNonnegative (one_add_log_step_le n nPositive) 3) (by positivity)))
      _ = _ := by ring
  have second : S⁻¹ * (128 * W ^ 2 * (M ^ 2 * B ^ 2 + (radius (maximumStep n))⁻¹ * (1 + Real.log M) ^ 3)) ≤
      1152 * Real.sqrt n * M * (W ^ 2 * B ^ 3) := by
    calc
      _ ≤ S⁻¹ * (128 * W ^ 2 * (9 * M ^ 2 * B ^ 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left inner (by positivity)) (by positivity)
      _ = _ := by
        change (M / Real.sqrt n)⁻¹ * _ = _
        rw [inv_div]
        field_simp
        ring
  have aBound : A ^ 2 ≤ T ^ 5 * B ^ 7 := by
    unfold A
    rw [mul_pow, ← pow_mul]
    exact mul_le_mul (pow_le_pow_right₀ TLower (by decide : 2 * 2 ≤ 5))
      (pow_le_pow_right₀ BLower (by decide : 2 ≤ 7)) (sq_nonneg _) (by positivity)
  have wBound : W ^ 2 * B ^ 3 ≤ T ^ 5 * B ^ 7 := by
    unfold W
    rw [mul_pow, mul_assoc, ← pow_add]
    exact mul_le_mul (pow_le_pow_right₀ TLower (by decide : 2 ≤ 5))
      (pow_le_pow_right₀ BLower (by decide : 2 + 3 ≤ 7)) (by positivity) (by positivity)
  change (1 / 2) * (S * (((n : ℝ) + 1) * A ^ 2) +
    S⁻¹ * (128 * W ^ 2 * (M ^ 2 * B ^ 2 + (radius (maximumStep n))⁻¹ * (1 + Real.log M) ^ 3))) ≤ _
  calc
    _ ≤ (1 / 2) * (2 * Real.sqrt n * M * A ^ 2 + 1152 * Real.sqrt n * M * (W ^ 2 * B ^ 3)) :=
      mul_le_mul_of_nonneg_left (add_le_add first second) (by norm_num)
    _ = (Real.sqrt n * M) * (A ^ 2 + 576 * (W ^ 2 * B ^ 3)) := by ring
    _ ≤ (n : ℝ) ^ (255 / 256 : ℝ) * (T ^ 5 * B ^ 7 + 576 * (T ^ 5 * B ^ 7)) :=
      mul_le_mul (sqrt_mul_maximumStep_le n nPositive)
        (add_le_add aBound (mul_le_mul_of_nonneg_left wBound (by norm_num))) (by positivity) (by positivity)
    _ = 577 * finalScale n T := by unfold finalScale B; ring
    _ ≤ _ := by apply mul_le_mul_of_nonneg_right (by norm_num); unfold finalScale; positivity

theorem smoothing_budget_le (n : ℕ) (nPositive : 0 < n) {T : ℝ} (TLower : 1 ≤ T) :
    ((T ^ 2 * logBudget n) * (2 * Real.pi * (2 * radius (maximumStep n))) * T ^ 2 * (2 * (n : ℝ))) *
      ((maximumStep n : ℝ) * (T * logBudget n)) ≤ 16 * finalScale n T := by
  let M := (maximumStep n : ℝ)
  let B := logBudget n
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have nLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have mPositive : 0 < M := maximumStep_real_positive n nPositive
  have TNonnegative : 0 ≤ T := zero_le_one.trans TLower
  have BLower : 1 ≤ B := one_le_logBudget n
  have BNonnegative : 0 ≤ B := zero_le_one.trans BLower
  have nDiv : (n : ℝ) / M ≤ 4 * (n : ℝ) ^ (255 / 256 : ℝ) := by
    have smaller : (n : ℝ) / M ≤ 4 * (n : ℝ) ^ (129 / 256 : ℝ) := by
      apply (div_le_iff₀ mPositive).mpr
      calc
        _ = (4 * (n : ℝ) ^ (129 / 256 : ℝ)) * ((n : ℝ) ^ (127 / 256 : ℝ) / 4) := by
          calc
            _ = (n : ℝ) ^ (129 / 256 : ℝ) * (n : ℝ) ^ (127 / 256 : ℝ) := by
              rw [← Real.rpow_add nReal]
              norm_num
            _ = _ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (maximumStep_divisor_lower n nPositive) (by positivity)
    exact smaller.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le nLower (by norm_num)) (by norm_num))
  calc
    _ = Real.pi * T ^ 5 * B ^ 2 * ((n : ℝ) / M) := by
      unfold radius
      change (T ^ 2 * B * (2 * Real.pi * (2 * (1 / (8 * M ^ 2)))) * T ^ 2 * (2 * (n : ℝ))) *
        (M * (T * B)) = _
      field_simp
      <;> ring
    _ ≤ (4 * T ^ 5 * B ^ 7) * (4 * (n : ℝ) ^ (255 / 256 : ℝ)) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right Real.pi_lt_four.le (by positivity))
        (pow_le_pow_right₀ BLower (by decide : 2 ≤ 7)) (by positivity) (by positivity)) nDiv (by positivity) (by positivity)
    _ = _ := by unfold finalScale B; ring

theorem primitive_replacement_budget_le (n : ℕ) (nLower : 2 ≤ n) {T : ℝ} (TLower : 1 ≤ T) :
    (16 * (lowCut n : ℝ) * T ^ 3 * (1 + T) * (Nat.log 2 n : ℝ) * Real.log n) *
      ((maximumStep n : ℝ) * (T * logBudget n)) ≤ 160 * finalScale n T := by
  let B := logBudget n
  have nPositive : 0 < n := by omega
  have nReal : (0 : ℝ) < n := by exact_mod_cast nPositive
  have nRealLower : (1 : ℝ) ≤ n := by exact_mod_cast nPositive
  have BLower : 1 ≤ B := one_le_logBudget n
  have BNonnegative : 0 ≤ B := zero_le_one.trans BLower
  have TNonnegative : 0 ≤ T := zero_le_one.trans TLower
  have logNonnegative : 0 ≤ Real.log n := Real.log_nonneg nRealLower
  have length : (lowCut n : ℝ) * (maximumStep n : ℝ) ≤ (n : ℝ) ^ (255 / 256 : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (127 / 256 : ℝ) :=
        mul_le_mul (Nat.floor_le (by positivity)) (maximumStep_le_power n nPositive) (Nat.cast_nonneg _) (by positivity)
      _ ≤ _ := by
        rw [← Real.rpow_add nReal]
        exact Real.rpow_le_rpow_of_exponent_le nRealLower (by norm_num)
  have tPow : T ^ 4 * (1 + T) ≤ 2 * T ^ 5 := by
    calc
      _ ≤ T ^ 4 * (2 * T) := mul_le_mul_of_nonneg_left (by linarith only [TLower]) (by positivity)
      _ = _ := by ring
  have lPow : (Nat.log 2 n : ℝ) * Real.log n * B ≤ 5 * B ^ 7 := by
    have h : (Nat.log 2 n : ℝ) ≤ 5 * B := by linarith only [natLog_succ_le nLower (le_refl n)]
    calc
      _ ≤ (5 * B) * B * B := mul_le_mul_of_nonneg_right
        (mul_le_mul h (log_le_logBudget nPositive le_rfl) logNonnegative (by positivity)) BNonnegative
      _ = 5 * B ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ BLower (by decide : 3 ≤ 7)) (by norm_num)
  calc
    _ = 16 * ((lowCut n : ℝ) * (maximumStep n : ℝ)) * (T ^ 4 * (1 + T)) *
        ((Nat.log 2 n : ℝ) * Real.log n * B) := by unfold B; ring
    _ ≤ 16 * (n : ℝ) ^ (255 / 256 : ℝ) * (2 * T ^ 5) * (5 * B ^ 7) := by
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left length (by norm_num)) tPow
        (by positivity) (by positivity)) lPow (by positivity) (by positivity)
    _ = _ := by unfold finalScale B; ring

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

private theorem divisor_envelope_at (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
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

theorem divisor_envelope : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
    (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / 1024 : ℝ) := divisor_envelope_at 1024 (by decide)

private theorem eventually_log_budget_le_at (p : ℝ) (hp : 0 < p) :
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

theorem eventually_log_budget_le :
    ∀ᶠ n : ℕ in atTop, logBudget n ≤ (n : ℝ) ^ (1 / 1024 : ℝ) :=
  eventually_log_budget_le_at (1 / 1024) (by norm_num)

theorem eventually_finalScale_le {C e : ℝ} (CNonnegative : 0 ≤ C) (ePositive : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∃ T : ℝ, 1 ≤ T ∧ (∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) ∧
      C * finalScale n T ≤ e * (n : ℝ) := by
  obtain ⟨D, DLower, estimate⟩ := divisor_envelope_at 4096 (by decide)
  let P := C * D ^ 5
  have DNonnegative : 0 ≤ D := zero_le_one.trans DLower
  have limit : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 1024) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 1024)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaledLimit : Tendsto (fun n : ℕ => P * (n : ℝ) ^ (-(1 / 1024) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le_at (1 / 4096) (by norm_num), scaledLimit.eventually_lt_const ePositive]
    with n nLower logBound small
  let X := (n : ℝ) ^ (1 / 4096 : ℝ)
  let T := D * X
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast nLower
  have nPositive : (0 : ℝ) < n := zero_lt_one.trans_le nOne
  have XLower : 1 ≤ X := Real.one_le_rpow nOne (by norm_num)
  have TLower : 1 ≤ T := one_le_mul_of_one_le_of_one_le DLower XLower
  refine ⟨T, TLower, fun m upper => estimate n m upper, ?_⟩
  calc
    _ ≤ C * (T ^ 5 * X ^ 7 * (n : ℝ) ^ (255 / 256 : ℝ)) := by
      unfold finalScale
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (one_le_logBudget n)) logBound 7)
          (by positivity)) (by positivity)) CNonnegative
    _ = P * (X ^ 12 * (n : ℝ) ^ (255 / 256 : ℝ)) := by unfold T P; ring
    _ = P * (n : ℝ) ^ (1023 / 1024 : ℝ) := by
      unfold X
      rw [← Real.rpow_natCast, ← Real.rpow_mul nPositive.le, ← Real.rpow_add nPositive]
      norm_num
    _ = (P * (n : ℝ) ^ (-(1 / 1024) : ℝ)) * (n : ℝ) := by
      calc
        _ = P * ((n : ℝ) ^ (-(1 / 1024) : ℝ) * (n : ℝ) ^ (1 : ℝ)) := by
          rw [← Real.rpow_add nPositive]
          norm_num
        _ = _ := by rw [Real.rpow_one]; unfold P; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right small.le nPositive.le

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

def totalConstant : ℝ := 776 + 10240000 * gcdSeriesConstant

theorem totalConstant_nonnegative : 0 ≤ totalConstant :=
  (add_nonneg (by norm_num) (mul_nonneg (by norm_num) gcdSeriesConstant_nonnegative))

end
end DyadicMixedB4Finish

end

end
end
end
end B13NondividingResidueReductionProof

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Arithmetic DyadicMixedB4Scale DyadicMixedB4HighAtoms
open DyadicMixedB4PairIntegral DyadicMixedB4Finish

noncomputable section

def upperCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊

def splitCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (7 / 12 : ℝ)⌋₊

theorem cuts_ordered (n : ℕ) (hn : 0 < n) :
    1 ≤ cutoffB n ∧ cutoffB n ≤ splitCut n ∧ splitCut n ≤ upperCut n := by
  have lower : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨Nat.le_floor (Real.one_le_rpow lower (by norm_num)),
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le lower (by norm_num : (1 / 3 : ℝ) ≤ 7 / 12)),
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le lower (by norm_num : (7 / 12 : ℝ) ≤ 2 / 3))⟩

def bandCoefficient (n lo hi : ℕ) (weight : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ a ∈ m.divisors.filter (fun a => lo < a ∧ a ≤ hi ∧ cutoffU n < m / a),
    (∑ d ∈ a.divisors.filter (fun d => cutoffU n < d), (μ d : ℝ)) * weight (m / a)

private theorem weightedBand_as_tails (n lo hi m : ℕ) (weight : ℕ → ℝ) (ordered : lo ≤ hi) :
    bandCoefficient n lo hi weight m =
      upperBandWeight (cutoffU n) lo (fun d => (μ d : ℝ)) weight m -
      upperBandWeight (cutoffU n) hi (fun d => (μ d : ℝ)) weight m := by
  classical
  unfold bandCoefficient upperBandWeight
  simp only [sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun a _ => ?_
  by_cases hl : lo < a
  · by_cases hh : a ≤ hi
    · simp [hl, hh, not_lt_of_ge hh]
    · simp [hl, hh, lt_of_not_ge hh]
  · have nh : ¬ hi < a := fun h => hl (ordered.trans_lt h)
    simp [hl, nh]

def mixedIntegral (n : ℕ) (v : ℕ → ℝ) : ℂ :=
  secondPolynomialIntegral n (plainPolynomial n (fun m => (v m : ℂ)))

def saving (f : ℕ → ℂ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖f n‖ ≤ e * (n : ℝ)

def frozenGoal : Prop :=
  let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
  let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
  let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
  let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  let H := fun n : ℕ => 256 * Q₁ n * Q n
  let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
  let lambdaWeight := ArithmeticFunction.vonMangoldt
  let moebiusWeight := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
  let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊
  let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊
  let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
  let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊
  let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), moebiusWeight d) * lambdaWeight (m / a)
  let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), moebiusWeight d) * lambdaWeight (m / a)
  let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume
  ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₃ n)‖ ≤ e * (n : ℝ)

end

end B13NondividingResidueReductionProof

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4LowBand
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open DyadicMixedB4YoungIntegral DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth

noncomputable section

end

end B13NondividingResidueReductionProof

namespace B13NondividingResidueReductionProof

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Arithmetic DyadicMixedB4Scale DyadicMixedB4ArcDecomposition DyadicMixedB4Geometric

noncomputable section

private theorem interval_sum_sub {lo hi limit : ℕ} (h : lo ≤ hi) (f : ℕ → ℂ) :
    (∑ k ∈ Ioc lo limit, f k) - (∑ k ∈ Ioc hi limit, f k) =
      ∑ k ∈ Ioc lo (min hi limit), f k := by
  have left : (Ioc lo limit).filter (· ≤ hi) = Ioc lo (min hi limit) := by
    ext k
    simp only [mem_filter, mem_Ioc, le_min_iff]
    tauto
  have right : (Ioc lo limit).filter (fun k => ¬ k ≤ hi) = Ioc hi limit := by
    ext k
    simp only [mem_filter, mem_Ioc, not_le]
    omega
  have split := sum_filter_add_sum_filter_not (Ioc lo limit) (· ≤ hi) f
  rw [left, right] at split
  exact (eq_sub_of_add_eq split).symm

/-- The band polynomial expanded along the progression with step equal to the
product of the cofactor and a short Möbius divisor. -/
theorem remainder_series (n : ℕ) (hn : 0 < n) (t : ℝ) (weight : ℕ → ℝ) :
    plainPolynomial n
      (fun m => (bandCoefficient n (cutoffB n) (splitCut n) weight m : ℂ)) t =
    ∑ b ∈ Ioc (cutoffU n) n, ∑ d ∈ Icc 1 (min (cutoffU n) (n / b)),
      (-(μ d : ℂ)) * (weight b : ℂ) *
        ∑ k ∈ Ioc (cutoffB n / d) (min (splitCut n / d) (n / (d * b))),
          phase (((d * b * k : ℕ) : ℝ) * t) := by
  let w (b : ℕ) : ℂ := weight b
  let f (m : ℕ) : ℂ := phase ((m : ℝ) * t)
  let U := cutoffU n
  let L := cutoffB n
  let V := splitCut n
  have ⟨lower, ordered, _⟩ := cuts_ordered n hn
  have cast (lo m : ℕ) :
      (↑(upperBandWeight (R := ℝ) (cutoffU n) lo (fun d => (μ d : ℝ)) weight m) : ℂ) =
        upperBandWeight (R := ℂ) U lo (fun d => (μ d : ℂ)) w m := by
    unfold upperBandWeight w
    push_cast
    rfl
  have tail (lo : ℕ) (loPos : 1 ≤ lo) :
      (∑ m ∈ range (n + 1), upperBandWeight U lo (fun d => (μ d : ℂ)) w m * f m) =
        ∑ b ∈ Ioc U n, ∑ d ∈ Icc 1 (min U (n / b)),
          (-(μ d : ℂ)) * w b * ∑ k ∈ Ioc (lo / d) (n / (d * b)), f (d * b * k) := by
    refine upper_band_progressions n U lo n le_rfl ?_ _ _ _ ?_
    · intro a b larger prod
      exact (Nat.le_mul_of_pos_left b (by omega)).trans prod
    · intro a larger
      have nonunit : a ≠ 1 := by omega
      have integer : (∑ d ∈ a.divisors, μ d) = 0 := by
        rw [← coe_mul_zeta_apply (f := μ), moebius_mul_coe_zeta, one_apply_ne nonunit]
      exact_mod_cast integer
  unfold plainPolynomial
  change (∑ m ∈ range (n + 1), (bandCoefficient n L V weight m : ℂ) * f m) = _
  simp only [weightedBand_as_tails n L V _ weight ordered, Complex.ofReal_sub,
    cast, sub_mul, sum_sub_distrib]
  rw [tail L lower, tail V (lower.trans ordered)]
  simp only [← sum_sub_distrib, ← mul_sub]
  refine sum_congr rfl fun b _ => sum_congr rfl fun d _ => ?_
  rw [interval_sum_sub (Nat.div_le_div_right ordered)]

end

end B13NondividingResidueReductionProof

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4PairIntegral DyadicMixedB4Finish

noncomputable section

end

end B13NondividingResidueReductionProof

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Fourier
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4PairIntegral

noncomputable section

end

end B13NondividingResidueReductionProof

namespace B13NondividingResidueReductionProof

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

theorem interval_sq_bound_of_uniform {g : ℝ → ℂ} (mg : Measurable g)
    {K : ℝ} (supremum : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖g t‖ ≤ K) :
    IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume 0 1 ∧
      (∫ t in (0 : ℝ)..1, ‖g t‖ ^ 2) ≤ K ^ 2 := by
  have squareInt : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have bound : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1), ‖(‖g t‖ ^ 2 : ℝ)‖ ≤ K ^ 2 := by
      apply (ae_restrict_iff' measurableSet_Ioc).2
      exact Filter.Eventually.of_forall (fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (supremum t (Set.Ioc_subset_Icc_self ht)) _)
    exact Integrable.of_bound (mg.norm.pow_const 2).aestronglyMeasurable _ bound
  refine ⟨squareInt, ?_⟩
  have mono := intervalIntegral.integral_mono_on zero_le_one squareInt intervalIntegrable_const
    (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (supremum t ht) 2)
  simpa using mono

end

end B13NondividingResidueReductionProof

end

/- Right cofactor -/
section

namespace B13NondividingResidueReductionProof

open Finset Filter
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4ArcDecomposition DyadicMixedB4TailScale
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def rightLargeCofactorCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (33 / 64 : ℝ)⌋₊

def rightVaughanCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 256 : ℝ)⌋₊

def rightVaughanFactorCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 128 : ℝ)⌋₊

def shortRightBandIndices (n K d : ℕ) : Finset ℕ :=
  Ioc (cutoffB n / d) (min (splitCut n / d) (n / (K + 1) / d))

/-- Isolate the right cofactor, with the Möbius divisor left in the outer sum. -/
theorem right_band_large_cofactor_polynomial {n K : ℕ} (hn : 0 < n) (KU : cutoffU n ≤ K)
    (w : ℕ → ℝ) (t : ℝ) :
    plainPolynomial n (fun m => (bandCoefficient n (cutoffB n) (splitCut n)
      (fun b => if K < b then w b else 0) m : ℂ)) t =
      ∑ d ∈ Icc 1 (cutoffU n), (-(μ d : ℂ)) *
        ∑ k ∈ shortRightBandIndices n K d, ∑ b ∈ Ioc K (n / (d * k)),
          (w b : ℂ) * phase (((d * k * b : ℕ) : ℝ) * t) := by
  let U := cutoffU n
  let L := cutoffB n
  let V := splitCut n
  let bs := Ioc K n
  let ds := Icc 1 U
  let numerator (d b : ℕ) := -(μ d : ℂ) * (w b : ℂ) *
    ∑ k ∈ Ioc (L / d) (min (V / d) (n / (d * b))), phase (((d * b * k : ℕ) : ℝ) * t)
  have extend (b : ℕ) (hb : b ∈ bs) :
      (∑ d ∈ Icc 1 (min U (n / b)), numerator d b) = ∑ d ∈ ds, numerator d b := by
    refine sum_subset (fun d hd => mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans (min_le_left ..)⟩) ?_
    intro d hd outside
    have bPos : 0 < b := (Nat.zero_le K).trans_lt (mem_Ioc.mp hb).1
    have dBig : n / b < d := by
      exact lt_of_not_ge fun upper => outside
        (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, le_min (mem_Icc.mp hd).2 upper⟩)
    have qZero : n / (d * b) = 0 := Nat.div_eq_of_lt (Nat.div_lt_iff_lt_mul bPos |>.mp dBig)
    simp [numerator, qZero]
  have selectCofactors :
      plainPolynomial n (fun m => (bandCoefficient n (cutoffB n) (splitCut n)
        (fun b => if K < b then w b else 0) m : ℂ)) t =
        ∑ b ∈ bs, ∑ d ∈ ds, numerator d b := by
    rw [remainder_series n hn t]
    symm
    calc
      _ = ∑ b ∈ bs, ∑ d ∈ Icc 1 (min U (n / b)), numerator d b :=
        sum_congr rfl fun b hb => (extend b hb).symm
      _ = ∑ b ∈ bs, ∑ d ∈ Icc 1 (min U (n / b)),
          (-(μ d : ℂ)) * ((if K < b then w b else 0 : ℝ) : ℂ) *
            ∑ k ∈ Ioc (L / d) (min (V / d) (n / (d * b))), phase (((d * b * k : ℕ) : ℝ) * t) := by
        refine sum_congr rfl fun b hb => sum_congr rfl fun d _ => ?_
        have above : K < b := (mem_Ioc.mp hb).1
        simp only [above, if_true, numerator]
      _ = _ := by
        refine sum_subset (fun b hb => mem_Ioc.mpr ⟨KU.trans_lt (mem_Ioc.mp hb).1, (mem_Ioc.mp hb).2⟩) ?_
        intro b hb outside
        have small : ¬ K < b := fun more => outside (mem_Ioc.mpr ⟨more, (mem_Ioc.mp hb).2⟩)
        simp [small]
  have exchange (d : ℕ) (hd : d ∈ ds) :
      (∑ b ∈ bs, numerator d b) = -(μ d : ℂ) *
        ∑ k ∈ shortRightBandIndices n K d, ∑ b ∈ Ioc K (n / (d * k)),
            (w b : ℂ) * phase (((d * k * b : ℕ) : ℝ) * t) := by
    let ks := Ioc (L / d) (V / d)
    let entry (b k : ℕ) := (w b : ℂ) * phase (((d * k * b : ℕ) : ℝ) * t)
    let inside (b k : ℕ) : Prop := d * k * b ≤ n
    have dPos : 0 < d := (mem_Icc.mp hd).1
    have sameKS (b : ℕ) (hb : b ∈ bs) :
        ks.filter (inside b) = Ioc (L / d) (min (V / d) (n / (d * b))) := by
      have dbPos : 0 < d * b := Nat.mul_pos dPos ((Nat.zero_le K).trans_lt (mem_Ioc.mp hb).1)
      ext k
      simp only [ks, inside, mem_filter, mem_Ioc, le_min_iff, Nat.le_div_iff_mul_le dbPos]
      rw [show k * (d * b) = d * k * b by ac_rfl]
      tauto
    have sameBS (k : ℕ) (hk : k ∈ ks) :
        bs.filter (fun b => inside b k) = Ioc K (n / (d * k)) := by
      have dkPos : 0 < d * k := Nat.mul_pos dPos ((Nat.zero_le (L / d)).trans_lt (mem_Ioc.mp hk).1)
      ext b
      simp only [bs, inside, mem_filter, mem_Ioc, Nat.le_div_iff_mul_le dkPos]
      rw [show b * (d * k) = d * k * b by ac_rfl]
      have bBound : d * k * b ≤ n → b ≤ n :=
        fun h => (Nat.le_mul_of_pos_left b dkPos).trans h
      exact ⟨fun h => ⟨h.1.1,h.2⟩, fun h => ⟨⟨h.1,bBound h.2⟩,h.2⟩⟩
    have restrict :
        (∑ k ∈ ks, ∑ b ∈ Ioc K (n / (d * k)), entry b k) =
          ∑ k ∈ shortRightBandIndices n K d, ∑ b ∈ Ioc K (n / (d * k)), entry b k := by
      symm
      refine sum_subset (fun k hk => mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1, (mem_Ioc.mp hk).2.trans (min_le_left ..)⟩) ?_
      intro k hk outside
      have kLarge : n / (K + 1) / d < k := by
        exact lt_of_not_ge fun upper => outside
          (mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1, le_min (mem_Ioc.mp hk).2 upper⟩)
      have prod : n < d * k * (K + 1) := by
        have h := (Nat.div_lt_iff_lt_mul dPos).mp kLarge
        have h' := (Nat.div_lt_iff_lt_mul (Nat.succ_pos K)).mp h
        simpa only [Nat.mul_comm d k] using h'
      have upper : n / (d * k) ≤ K := by
        have dkPos : 0 < d*k := Nat.mul_pos dPos ((Nat.zero_le (L / d)).trans_lt (mem_Ioc.mp hk).1)
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul dkPos).mpr (by simpa [Nat.mul_comm (d*k)] using prod))
      exact sum_eq_zero fun b hb => False.elim ((not_lt_of_ge upper) ((mem_Ioc.mp hb).1.trans_le (mem_Ioc.mp hb).2))
    calc
      _ = -(μ d : ℂ) *
          ∑ b ∈ bs, ∑ k ∈ ks, if inside b k then entry b k else 0 := by
        rw [mul_sum]
        refine sum_congr rfl fun b hb => ?_
        dsimp only [numerator]
        rw [mul_assoc, ← sum_filter, sameKS b hb]
        apply congrArg (fun z : ℂ => -(μ d : ℂ) * z)
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        simp only [entry, show d*b*k = d*k*b by ac_rfl]
      _ = -(μ d : ℂ) * ∑ k ∈ ks, ∑ b ∈ bs, if inside b k then entry b k else 0 := by rw [sum_comm]
      _ = -(μ d : ℂ) * ∑ k ∈ ks, ∑ b ∈ Ioc K (n / (d * k)), entry b k := by
        congr 1
        refine sum_congr rfl fun k hk => ?_
        rw [← sum_filter, sameBS k hk]
      _ = _ := congrArg (-(μ d : ℂ) * ·) restrict
  rw [selectCofactors, sum_comm]
  exact sum_congr rfl exchange

theorem cutoffU_le_rightLargeCofactorCut {n : ℕ} (hn : 0 < n) :
    cutoffU n ≤ rightLargeCofactorCut n :=
  Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))

theorem right_cap_product {n : ℕ} (hn : 0 < n) :
    rightVaughanCut n * rightVaughanCut n ≤ rightVaughanFactorCap n := by
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have h : (rightVaughanCut n : ℝ) ≤ (n : ℝ) ^ (1 / 256 : ℝ) := Nat.floor_le (by positivity)
  apply Nat.le_floor
  push_cast
  calc
    _ ≤ (n : ℝ) ^ (1 / 256 : ℝ) * (n : ℝ) ^ (1 / 256 : ℝ) :=
      mul_le_mul h h (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add nr]; norm_num

theorem right_short_step_eventually : ∀ᶠ n : ℕ in atTop,
    ∀ d ∈ Icc 1 (cutoffU n), ∀ k ∈ shortRightBandIndices n (rightLargeCofactorCut n) d,
      ∀ s ∈ Icc 1 (rightVaughanFactorCap n), 0 < d * k * s ∧ d * k * s ≤ maximumStep n := by
  have grow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 256 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 256)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1, grow.eventually_ge_atTop 4] with n hn big d hd k hk s hs
  have nPos : 0 < n := by omega
  have nr : (0 : ℝ) < n := by exact_mod_cast nPos
  have dPos : 0 < d := (mem_Icc.mp hd).1
  have kPos : 0 < k := (Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1
  have sPos : 0 < s := (mem_Icc.mp hs).1
  refine ⟨Nat.mul_pos (Nat.mul_pos dPos kPos) sPos, ?_⟩
  have natural : (d * k) * (rightLargeCofactorCut n + 1) ≤ n := by
    have first := (Nat.le_div_iff_mul_le dPos).mp ((mem_Ioc.mp hk).2.trans (min_le_right ..))
    have second := (Nat.le_div_iff_mul_le (Nat.succ_pos (rightLargeCofactorCut n))).mp first
    simpa only [Nat.mul_comm d k] using second
  have base : (n : ℝ) ^ (33 / 64 : ℝ) ≤ (rightLargeCofactorCut n : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  have dBound : ((d * k : ℕ) : ℝ) ≤ (n : ℝ) ^ (31 / 64 : ℝ) := by
    apply (le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos nr (33 / 64)))
    calc
      _ ≤ ((d*k : ℕ) : ℝ) * ((rightLargeCofactorCut n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left base (Nat.cast_nonneg _)
      _ ≤ n := by exact_mod_cast natural
      _ = _ := by rw [← Real.rpow_add nr]; norm_num
  have sBound : (s : ℝ) ≤ (n : ℝ) ^ (1 / 128 : ℝ) :=
    (show (s : ℝ) ≤ rightVaughanFactorCap n by exact_mod_cast (mem_Icc.mp hs).2).trans
      (Nat.floor_le (by positivity))
  have productBound : ((d*k*s : ℕ) : ℝ) ≤ (n : ℝ) ^ (126 / 256 : ℝ) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (n : ℝ) ^ (31 / 64 : ℝ) * (n : ℝ) ^ (1 / 128 : ℝ) :=
        mul_le_mul dBound sBound (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← Real.rpow_add nr]; norm_num
  exact_mod_cast (calc
    ((d*k*s : ℕ) : ℝ) ≤ (n : ℝ) ^ (126 / 256 : ℝ) := productBound
    _ ≤ (n : ℝ) ^ (127 / 256 : ℝ) / 4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
      calc
        _ ≤ (n : ℝ) ^ (126 / 256 : ℝ) * (n : ℝ) ^ (1 / 256 : ℝ) :=
          mul_le_mul_of_nonneg_left big (by positivity)
        _ = _ := by rw [← Real.rpow_add nr]; norm_num
    _ ≤ (maximumStep n : ℝ) := maximumStep_divisor_lower n nPos)

end

end B13NondividingResidueReductionProof

end

/- Short suffixes -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4LowBand DyadicMixedB4PairIntegral
open DyadicMixedB4Fourier DyadicMixedB4NearPair DyadicMixedB4NearReplacement
open DyadicMixedB4PrimitiveNearPair DyadicMixedB4NearMain DyadicMixedB4Ramanujan
open DyadicMixedB4OffWaveMoment DyadicMixedB4YoungIntegral DyadicMixedB4WindowKernel
open DyadicMixedB4BilinearEnergy DyadicMixedB4BilinearBlock DyadicMixedB4BlockModulus
open DyadicMixedB4ModulusAggregate DyadicMixedB4DyadicPartition DyadicMixedB4GcdSeries
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4TailAggregate
open DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth DyadicMixedB4Finish
open scoped Classical

structure ShortSuffixWaves (n : ℕ) (ι : Type*) where
  items : Finset ι
  step : ι → ℕ
  lower : ι → ℕ
  weight : ι → ℂ
  step_range : ∀ i ∈ items, 0 < step i ∧ step i ≤ maximumStep n

namespace ShortSuffixWaves

variable {n : ℕ} {ι : Type*}

noncomputable section

def WeightBound (F : ShortSuffixWaves n ι) (W : ℝ) : Prop :=
  ∀ u ∈ Icc 1 (maximumStep n),
    (∑ i ∈ F.items.filter (fun i => F.step i = u), ‖F.weight i‖) ≤ W

def polynomial (F : ShortSuffixWaves n ι) (t : ℝ) : ℂ :=
  ∑ i ∈ F.items, F.weight i * wave (F.step i) (F.lower i) (n / F.step i) t

def deepIntegral (F : ShortSuffixWaves n ι) : ℂ := secondPolynomialIntegral n F.polynomial

private def farPolynomial (F : ShortSuffixWaves n ι) (t : ℝ) : ℂ :=
  ∑ i ∈ F.items, F.weight i *
    offWave (radius (maximumStep n)) (F.step i) (F.lower i) (n / F.step i) t

private def farIntegral (F : ShortSuffixWaves n ι) : ℂ :=
  ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator
    (fun x => shiftedPolynomial n (lowCoefficients n) x * F.farPolynomial x) t

private def exactPair (F : ShortSuffixWaves n ι) : ℂ :=
  ∑ i ∈ F.items, F.weight i *
    ∑ q ∈ (F.step i).divisors.filter (fun q => cutoffR n < q),
      exactNearAtom n (F.lower i) (1, F.step i) q

private def smoothedPair (F : ShortSuffixWaves n ι) : ℂ :=
  ∑ i ∈ F.items, F.weight i *
    ∑ q ∈ (F.step i).divisors.filter (fun q => cutoffR n < q),
      smoothedNearAtom n (F.lower i) (1, F.step i) q

private def primitivePair (F : ShortSuffixWaves n ι) : ℂ :=
  ∑ i ∈ F.items, F.weight i *
    ∑ q ∈ (F.step i).divisors.filter (fun q => cutoffR n < q),
      primitiveNearAtom n (F.lower i) (1, F.step i) q

private def primitiveDyad (F : ShortSuffixWaves n ι) (k : ℕ) : ℂ :=
  ∑ i ∈ F.items, F.weight i * ∑ q ∈ (F.step i).divisors.filter (fun q => cutoffR n < q),
    primitiveBlock n (maximumStep n) (cutoffB n) (cutoffH n) q (F.step i) (F.lower i)
      (n / F.step i) (cutoffU n) (shortIndices n k) (fun a => (lowMoebiusWeight (cutoffU n) a : ℂ))

private theorem deep_split (F : ShortSuffixWaves n ι) (nPositive : 0 < n)
    (width : 4 * cutoffH n * maximumStep n ≤ n) :
    F.deepIntegral = F.farIntegral + F.exactPair := by
  classical
  let outside := (wide n (cutoffB n) (cutoffH n))ᶜ
  let A := shiftedPolynomial n (lowCoefficients n)
  let W (i : ι) := wave (F.step i) (F.lower i) (n / F.step i)
  let O (i : ι) := offWave (radius (maximumStep n)) (F.step i) (F.lower i) (n / F.step i)
  have FContinuous : Continuous A := shiftedPolynomial_continuous n _
  have WContinuous (i : ι) : Continuous (W i) := by unfold W wave phase; fun_prop
  have sMeasurable : MeasurableSet outside := (wide_measurable n (cutoffB n) (cutoffH n)).compl
  have usualIntegral (i : ι) : IntervalIntegrable (outside.indicator (fun t => A t * W i t)) volume 0 1 :=
    indicator_intervalIntegrable (FContinuous.mul (WContinuous i)) sMeasurable
  have outsideIntegral (i : ι) : IntervalIntegrable (outside.indicator (fun t => A t * O i t)) volume 0 1 := by
    let grid := gridNear (radius (maximumStep n)) (F.step i)
    have equivalent : outside.indicator (fun t => A t * O i t) =
        (outside ∩ gridᶜ).indicator (fun t => A t * W i t) := by
      funext t
      by_cases onGrid : t ∈ grid <;> by_cases onOutside : t ∈ outside <;>
        simp_all only [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, Set.mem_compl_iff,
          not_true_eq_false, not_false_eq_true, and_true, and_false, mul_zero, O, W, grid, offWave]
    rw [equivalent]
    exact indicator_intervalIntegrable (FContinuous.mul (WContinuous i))
      (sMeasurable.inter (gridNear_measurable (radius (maximumStep n)) (F.step i)).compl)
  have originalPointwise (t : ℝ) : outside.indicator (fun x => plainPolynomial n (lowCoefficients n) x *
        F.polynomial x * phase (-(n : ℝ) * x)) t =
      ∑ i ∈ F.items, F.weight i * outside.indicator (fun x => A x * W i x) t := by
    by_cases membership : t ∈ outside
    · simp only [Set.indicator_of_mem membership, polynomial, A, shiftedPolynomial_eq,
        mul_sum, sum_mul]
      refine sum_congr rfl fun i _ => ?_
      unfold W
      ring
    · simp [membership]
  have outsidePointwise (t : ℝ) : outside.indicator (fun x => A x * F.farPolynomial x) t =
      ∑ i ∈ F.items, F.weight i * outside.indicator (fun x => A x * O i x) t := by
    by_cases membership : t ∈ outside
    · simp only [Set.indicator_of_mem membership, farPolynomial, mul_sum, O]
      exact sum_congr rfl fun _ _ => by ring
    · simp [membership]
  have cutoffs := cutoffs_ordered n nPositive
  have each (i : ι) (iMember : i ∈ F.items) :
      (∫ t in (0 : ℝ)..1, outside.indicator (fun x => A x * W i x) t) =
        (∫ t in (0 : ℝ)..1, outside.indicator (fun x => A x * O i x) t) +
          ∑ q ∈ (F.step i).divisors.filter (fun q => cutoffR n < q), exactNearAtom n (F.lower i) (1, F.step i) q := by
    simpa only [exactNearAtom, atomStep, atomLower, atomUpper, one_mul, Nat.div_one] using
      split_shifted_wave n (maximumStep n) (cutoffB n) (cutoffH n) (cutoffR n)
      (F.step i) (F.lower i) (n / F.step i) (lowCoefficients n) nPositive
      (F.step_range i iMember).1 (F.step_range i iMember).2 cutoffs.2.2.1
      width cutoffs.1 cutoffs.2.1 (cutoffR_covered n nPositive)
  unfold deepIntegral secondPolynomialIntegral farIntegral exactPair
  change (∫ t in (0 : ℝ)..1, outside.indicator (fun x => plainPolynomial n (lowCoefficients n) x *
      F.polynomial x * phase (-(n : ℝ) * x)) t) =
    (∫ t in (0 : ℝ)..1, outside.indicator (fun x => A x * F.farPolynomial x) t) + _
  simp_rw [originalPointwise, outsidePointwise]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (usualIntegral i).const_mul (F.weight i)),
    intervalIntegral.integral_finsetSum (fun i _ => (outsideIntegral i).const_mul (F.weight i))]
  simp_rw [intervalIntegral.integral_const_mul, ← sum_add_distrib, ← mul_add]
  exact sum_congr rfl (fun i iMember => congrArg (fun z : ℂ => F.weight i * z) (each i iMember))

private theorem norm_farIntegral_le (F : ShortSuffixWaves n ι) (nPositive : 0 < n)
    {S A W : ℝ} (SPositive : 0 < S)
    (ANonnegative : 0 ≤ A) (WNonnegative : 0 ≤ W)
    (aBound : ∀ m ∈ range (n + 1), ‖lowCoefficients n m‖ ≤ A)
    (wBound : F.WeightBound W) :
    ‖F.farIntegral‖ ≤ (1 / 2) * (S * (((n : ℝ) + 1) * A ^ 2) +
      S⁻¹ * (128 * W ^ 2 * ((maximumStep n : ℝ) ^ 2 * (1 + Real.log ((n : ℝ) + 2)) ^ 2 +
        (radius (maximumStep n))⁻¹ * (1 + Real.log (maximumStep n : ℝ)) ^ 3))) := by
  let APoly := shiftedPolynomial n (lowCoefficients n)
  let G := F.farPolynomial
  have cutoffs := cutoffs_ordered n nPositive
  have MPositive : 0 < maximumStep n := cutoffs.1.trans (cutoffs.2.1.trans cutoffs.2.2.1)
  have bPositive : 0 < radius (maximumStep n) := by unfold radius; positivity
  have FContinuous : Continuous APoly := shiftedPolynomial_continuous n _
  have GMeasurable : Measurable G :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (DyadicMixedB4OffWaveMoment.offWave_measurable _ _ _ _))
  have Fint : IntervalIntegrable (fun t => ‖APoly t‖ ^ 2) volume 0 1 := (FContinuous.norm.pow 2).intervalIntegrable 0 1
  have Gint : IntervalIntegrable (fun t => ‖G t‖ ^ 2) volume 0 1 :=
    DyadicMixedB4OffWaveMoment.intervalIntegrable_offWave_norm_sq F.items _ F.step F.lower (fun i => n / F.step i) F.weight
  have Fbound : (∫ t in (0 : ℝ)..1, ‖APoly t‖ ^ 2) ≤ ((n : ℝ) + 1) * A ^ 2 := by
    rw [shiftedPolynomial_parseval]
    calc
      _ ≤ ∑ _ ∈ range (n + 1), A ^ 2 := sum_le_sum fun m member => pow_le_pow_left₀ (norm_nonneg _) (aBound m member) 2
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_range, Nat.cast_add, Nat.cast_one]
  have Gbound := DyadicMixedB4OffWaveMoment.offWave_mass_le_weighted F.items n (maximumStep n)
    (radius (maximumStep n)) W MPositive cutoffs.2.2.2 bPositive WNonnegative F.step F.lower (fun i => n / F.step i)
    F.weight (fun i member => F.step_range i member) (fun _ _ => le_rfl) wBound
  have productBound := DyadicMixedB4YoungIntegral.norm_indicator_product_le SPositive
    (wide_measurable n (cutoffB n) (cutoffH n)).compl FContinuous.measurable GMeasurable Fint Gint
  refine productBound.trans ?_
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left Fbound SPositive.le)
      (mul_le_mul_of_nonneg_left Gbound (inv_nonneg.mpr SPositive.le))) (by norm_num)

private theorem sum_weight_le (F : ShortSuffixWaves n ι) {W : ℝ} (wBound : F.WeightBound W) :
    (∑ i ∈ F.items, ‖F.weight i‖) ≤ (maximumStep n : ℝ) * W := by
  have mapsInto (i : ι) (member : i ∈ F.items) : F.step i ∈ Icc 1 (maximumStep n) :=
    mem_Icc.mpr (F.step_range i member)
  calc
    _ = ∑ u ∈ Icc 1 (maximumStep n), ∑ i ∈ F.items.filter (fun i => F.step i = u), ‖F.weight i‖ :=
      (sum_fiberwise_of_maps_to mapsInto _).symm
    _ ≤ ∑ _ ∈ Icc 1 (maximumStep n), W := sum_le_sum wBound
    _ = _ := by simp [nsmul_eq_mul]

private theorem norm_exact_sub_smoothed (F : ShortSuffixWaves n ι) (nPositive : 0 < n)
    {A T W : ℝ} (ANonnegative : 0 ≤ A) (TNonnegative : 0 ≤ T)
    (aBound : ∀ m ∈ range (n + 1), ‖lowCoefficients n m‖ ≤ A)
    (tBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (wBound : F.WeightBound W) :
    ‖F.exactPair - F.smoothedPair‖ ≤
      (A * (2 * Real.pi * (2 * radius (maximumStep n))) * T ^ 2 * (2 * (n : ℝ))) *
        ((maximumStep n : ℝ) * W) := by
  let radiusError := 2 * Real.pi * (2 * radius (maximumStep n))
  let C := A * radiusError * T * (2 * (n : ℝ))
  let moduli (i : ι) := (F.step i).divisors.filter (fun q => cutoffR n < q)
  have radiusNonnegative : 0 ≤ radiusError := by
    unfold radiusError
    exact mul_nonneg (by positivity) (mul_nonneg (by norm_num) (DyadicMixedB4WindowKernel.radius_nonnegative _))
  have CNonnegative : 0 ≤ C := by unfold C; positivity
  have cuts := cutoffs_ordered n nPositive
  have MPositive : 0 < maximumStep n := cuts.1.trans (cuts.2.1.trans cuts.2.2.1)
  have individual (i : ι) (iMember : i ∈ F.items) (q : ℕ) (qMember : q ∈ moduli i) :
      ‖exactNearAtom n (F.lower i) (1, F.step i) q - smoothedNearAtom n (F.lower i) (1, F.step i) q‖ ≤ C := by
    obtain ⟨gPositive, gBound⟩ := F.step_range i iMember
    obtain ⟨divisor, qAbove⟩ := mem_filter.mp qMember
    have qLower := cuts.1.trans_lt qAbove
    letI : NeZero q := ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors divisor)⟩
    have qBound := (Nat.le_of_dvd gPositive (Nat.dvd_of_mem_divisors divisor)).trans (gBound.trans cuts.2.2.2)
    have radiusBound : (F.step i : ℝ) * radius (maximumStep n) ≤ 1 / 2 := by
      have upper := radius_le_product (q := F.step i) (r := 1) gPositive (by decide) gBound MPositive
      have gRealPositive : (0 : ℝ) < F.step i := by exact_mod_cast gPositive
      calc
        _ ≤ (F.step i : ℝ) * (1 / (4 * (F.step i : ℝ) * (1 : ℕ))) :=
          mul_le_mul_of_nonneg_left upper gRealPositive.le
        _ = (1 : ℝ) / 4 := by simp only [Nat.cast_one, mul_one]; field_simp
        _ ≤ _ := by norm_num
    have actual := norm_sum_windowKernel_difference_le n (maximumStep n) (cutoffB n) (cutoffH n) q
      (F.step i) (F.lower i) (n / F.step i) (lowCoefficients n) qLower gPositive radiusBound aBound ANonnegative
    have normalized : ‖exactNearAtom n (F.lower i) (1, F.step i) q - smoothedNearAtom n (F.lower i) (1, F.step i) q‖ ≤
        (A * radiusError) * ((q.divisors.card : ℝ) * ((n : ℝ) + q)) := by
      unfold exactNearAtom smoothedNearAtom smoothKernelFactor radiusError
      simpa only [mul_assoc, atomStep, atomLower, atomUpper, one_mul, Nat.div_one] using actual
    refine normalized.trans ?_
    unfold C
    rw [mul_assoc (A * radiusError) T (2 * (n : ℝ))]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg ANonnegative radiusNonnegative)
    refine mul_le_mul (tBound q qBound) ?_ (by positivity) TNonnegative
    have qReal : (q : ℝ) ≤ n := by exact_mod_cast qBound
    linarith only [qReal]
  have inner (i : ι) (iMember : i ∈ F.items) :
      ‖∑ q ∈ moduli i, (exactNearAtom n (F.lower i) (1, F.step i) q - smoothedNearAtom n (F.lower i) (1, F.step i) q)‖ ≤ T * C := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _ ∈ moduli i, C := sum_le_sum (individual i iMember)
      _ ≤ ∑ _ ∈ (F.step i).divisors, C :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => CNonnegative)
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (tBound _ ((F.step_range i iMember).2.trans cuts.2.2.2)) CNonnegative
  unfold exactPair smoothedPair
  rw [← sum_sub_distrib]
  simp only [← mul_sub, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ F.items, ‖F.weight i‖ * (T * C) := by
      refine sum_le_sum fun i membership => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (inner i membership) (norm_nonneg _)
    _ = (∑ i ∈ F.items, ‖F.weight i‖) * (T * C) := (sum_mul _ _ _).symm
    _ ≤ ((maximumStep n : ℝ) * W) * (T * C) :=
      mul_le_mul_of_nonneg_right (sum_weight_le F wBound) (mul_nonneg TNonnegative CNonnegative)
    _ = _ := by unfold C radiusError; ring

private theorem norm_smoothed_sub_primitive (F : ShortSuffixWaves n ι) (nPositive : 0 < n)
    {T W : ℝ} (TNonnegative : 0 ≤ T) (tBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (wBound : F.WeightBound W) :
    ‖F.smoothedPair - F.primitivePair‖ ≤
      (16 * (lowCut n : ℝ) * T ^ 3 * (1 + T) * (Nat.log 2 n : ℝ) * Real.log n) *
        ((maximumStep n : ℝ) * W) := by
  let C : ℝ := 16 * (lowCut n : ℝ) * T ^ 2 * (1 + T) * (Nat.log 2 n : ℝ) * Real.log n
  let moduli (i : ι) := (F.step i).divisors.filter (fun q => cutoffR n < q)
  have logNonnegative : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast nPositive)
  have CNonnegative : 0 ≤ C := by unfold C; positivity
  have cutoffs := cutoffs_ordered n nPositive
  have inner (i : ι) (membership : i ∈ F.items) :
      ‖∑ q ∈ moduli i, (smoothedNearAtom n (F.lower i) (1, F.step i) q - primitiveNearAtom n (F.lower i) (1, F.step i) q)‖ ≤ C * T := by
    obtain ⟨positive, upper⟩ := F.step_range i membership
    have within : F.step i ≤ n := upper.trans cutoffs.2.2.2
    have stepPositive : (0 : ℝ) < F.step i := by exact_mod_cast positive
    have qBound (q : ℕ) (member : q ∈ moduli i) : q ≤ F.step i :=
      Nat.le_of_dvd positive (Nat.dvd_of_mem_divisors (mem_filter.mp member).1)
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ q ∈ moduli i, C / (F.step i : ℝ) * (q : ℝ) := by
        refine sum_le_sum fun q member => ?_
        simpa only [atomStep, one_mul] using norm_smoothedNearAtom_sub_primitive_le n (F.lower i) (1, F.step i) q nPositive
          (cutoffs.1.trans_lt (mem_filter.mp member).2) ((qBound q member).trans within) TNonnegative tBound
      _ ≤ ∑ _ ∈ moduli i, C := by
        refine sum_le_sum fun q member => ?_
        calc
          _ ≤ C / (F.step i : ℝ) * (F.step i : ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast qBound q member) (by positivity)
          _ = _ := div_mul_cancel₀ _ stepPositive.ne'
      _ ≤ ∑ _ ∈ (F.step i).divisors, C :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => CNonnegative)
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_right (tBound _ within) CNonnegative
  unfold smoothedPair primitivePair
  rw [← sum_sub_distrib]
  simp only [← mul_sub, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ F.items, ‖F.weight i‖ * (C * T) := by
      refine sum_le_sum fun i member => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (inner i member) (norm_nonneg _)
    _ = (∑ i ∈ F.items, ‖F.weight i‖) * (C * T) := (sum_mul _ _ _).symm
    _ ≤ ((maximumStep n : ℝ) * W) * (C * T) :=
      mul_le_mul_of_nonneg_right (sum_weight_le F wBound) (mul_nonneg CNonnegative TNonnegative)
    _ = _ := by unfold C; ring

private theorem primitivePair_eq_dyads (F : ShortSuffixWaves n ι) (nPositive : 0 < n) :
    F.primitivePair = ∑ k ∈ dyadicIndices n, F.primitiveDyad k := by
  let Q (i : ι) := (F.step i).divisors.filter (fun q => cutoffR n < q)
  let block (i : ι) (q k : ℕ) := primitiveBlock n (maximumStep n) (cutoffB n) (cutoffH n) q
    (F.step i) (F.lower i) (n / F.step i) (cutoffU n) (shortIndices n k)
    (fun a => (lowMoebiusWeight (cutoffU n) a : ℂ))
  have each (i : ι) (q : ℕ) : primitiveNearAtom n (F.lower i) (1, F.step i) q = ∑ k ∈ dyadicIndices n, block i q k := by
    simp only [primitiveNearAtom, block, shortIndices, primitiveBlock, atomStep, atomLower, atomUpper, one_mul, Nat.div_one]
    exact dyadic_sum_partition _ n (fun a member => (mem_Ioc.mp member).2.trans (lowCut_le n nPositive)) _
  calc
    _ = ∑ i ∈ F.items, F.weight i * ∑ q ∈ Q i, ∑ k ∈ dyadicIndices n, block i q k := by
      unfold primitivePair
      simp only [each, Q]
    _ = ∑ i ∈ F.items, ∑ k ∈ dyadicIndices n, F.weight i * ∑ q ∈ Q i, block i q k := by
      refine sum_congr rfl fun i _ => ?_
      rw [sum_comm, mul_sum]
    _ = _ := sum_comm

set_option maxHeartbeats 900000 in
private theorem norm_primitiveDyad_le (F : ShortSuffixWaves n ι) (k : ℕ) (nLower : 2 ≤ n)
    {T : ℝ} (TNonnegative : 0 ≤ T) (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (wBound : F.WeightBound (T * logBudget n)) :
    ‖F.primitiveDyad k‖ ≤
      2048000 * gcdSeriesConstant * T ^ 5 * logBudget n ^ 6 * (n : ℝ) ^ (255 / 256 : ℝ) := by
  have BNonnegative : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
  have constantNonnegative : 0 ≤ 2048000 * gcdSeriesConstant * T ^ 5 * logBudget n ^ 6 *
      (n : ℝ) ^ (255 / 256 : ℝ) := by
    have := gcdSeriesConstant_nonnegative
    positivity
  by_cases nonempty : (shortIndices n k).Nonempty
  · let A := dyadicBase k
    let U := cutoffU n
    let M := maximumStep n
    let R := cutoffR n
    let G := Icc 1 (2 * A)
    let D := Icc 1 M
    let energy := blockEnergy n A U
    let w (a : ℕ) := (lowMoebiusWeight U a : ℂ)
    let C := T ^ 2 * (16 + 24 * Real.log ((n : ℝ) + 1))
    let Q (i : ι) := (F.step i).divisors.filter (fun q => R < q)
    let cost := conductorCost G D n.divisors energy
    let W := T * logBudget n
    have nPositive : 0 < n := by omega
    have aPositive := dyadicBase_positive k
    have CNonnegative : 0 ≤ C := by
      unfold C
      have := Real.log_nonneg (show 1 ≤ (n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n])
      positivity
    have indicesRange : shortIndices n k ⊆ Ico A (2 * A) := by
      intro a member
      obtain ⟨within, equality⟩ := mem_filter.mp member
      exact mem_dyadicInterval ((Nat.zero_le _).trans_lt (mem_Ioc.mp within).1) equality
    have aUpper : A ≤ lowCut n := by
      obtain ⟨a, member⟩ := nonempty
      exact (mem_Ico.mp (indicesRange member)).1.trans (mem_Ioc.mp (mem_filter.mp member).1).2
    have uLower : U < 2 * A := by
      obtain ⟨a, member⟩ := nonempty
      exact (mem_Ioc.mp (mem_filter.mp member).1).1.trans (mem_Ico.mp (indicesRange member)).2
    obtain ⟨rPositive, rB, bM, mN⟩ := cutoffs_ordered n nPositive
    have mPositive : 0 < M := rPositive.trans (rB.trans bM)
    have radiusUpper : radius M ≤ 1 := by
      have mReal : (1 : ℝ) ≤ M := by exact_mod_cast mPositive
      unfold radius
      apply (div_le_one (by positivity)).mpr
      exact (one_le_pow₀ mReal).trans (le_mul_of_one_le_left (by positivity) (by norm_num))
    have coefficientBound (a : ℕ) (member : a ∈ shortIndices n k) : ‖w a‖ ≤ T := by
      unfold w
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_lowMoebiusWeight_le U a).trans
        (divisorBound a ((mem_Ioc.mp (mem_filter.mp member).1).2.trans (lowCut_le n nPositive)))
    have each (i : ι) (iMember : i ∈ F.items) (q : ℕ) (qMember : q ∈ Q i) :
        ‖primitiveBlock n M (cutoffB n) (cutoffH n) q (F.step i) (F.lower i) (n / F.step i)
          U (shortIndices n k) w‖ ≤ C / (F.step i : ℝ) * cost q := by
      obtain ⟨divisor, _⟩ := mem_filter.mp qMember
      obtain ⟨positive, bound⟩ := F.step_range i iMember
      exact norm_primitiveBlock_le n M (cutoffB n) (cutoffH n) q (F.step i) (F.lower i) (n / F.step i)
        U A nPositive aPositive (Nat.pos_of_mem_divisors divisor)
        ((Nat.le_of_dvd positive (Nat.dvd_of_mem_divisors divisor)).trans bound) mN
        radiusUpper (shortIndices n k) indicesRange w TNonnegative coefficientBound divisorBound
    have WNonnegative : 0 ≤ W := mul_nonneg TNonnegative BNonnegative
    have weightBound := wBound
    have mainBound := sum_weighted_moduli_le F.items F.step (fun i => ‖F.weight i‖)
      R M mPositive WNonnegative (fun i member => mem_Icc.mpr (F.step_range i member)) weightBound
      G D n.divisors energy (fun _ member => (mem_Icc.mp member).1) (fun _ member => (mem_Icc.mp member).1)
      (fun _ member => Nat.pos_of_mem_divisors member) (fun g _ d _ => blockEnergy_nonnegative n A U g d)
    have tailBound := sum_energy_tails_le nLower aPositive aUpper uLower TNonnegative divisorBound
    let tail := ∑ g ∈ G, ∑ d ∈ D, ∑ f ∈ n.divisors, tailWeight R g f d * energy g d
    have logPlus : Real.log ((n : ℝ) + 1) ≤ logBudget n :=
      (Real.log_le_log (by positivity) (by linarith)).trans (le_add_of_nonneg_left zero_le_one)
    have CBound : C ≤ 40 * T ^ 2 * logBudget n := by
      unfold C
      calc
        _ ≤ T ^ 2 * (40 * logBudget n) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          linarith only [logPlus, one_le_logBudget n]
        _ = _ := by ring
    have mLogNonnegative : 0 ≤ 1 + Real.log (M : ℝ) :=
      (add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast mPositive)))
    have tailNonnegative : 0 ≤ tail :=
      sum_nonneg fun g _ => sum_nonneg fun d _ => sum_nonneg fun f _ =>
        mul_nonneg (tailWeight_nonnegative _ _ _ _) (blockEnergy_nonnegative _ _ _ _ _)
    unfold primitiveDyad
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ i ∈ F.items, ‖F.weight i‖ * ∑ q ∈ Q i, C / (F.step i : ℝ) * cost q := by
        refine sum_le_sum fun i member => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum (each i member))) (norm_nonneg _)
      _ = C * (∑ i ∈ F.items, (‖F.weight i‖ / (F.step i : ℝ)) * ∑ q ∈ Q i, cost q) := by
        conv_rhs => rw [mul_sum]
        refine sum_congr rfl fun _ _ => ?_
        rw [← mul_sum]
        ring
      _ ≤ C * ((W * (1 + Real.log (M : ℝ))) * tail) :=
        mul_le_mul_of_nonneg_left mainBound CNonnegative
      _ ≤ (40 * T ^ 2 * logBudget n) * ((W * logBudget n) *
          (51200 * gcdSeriesConstant * T ^ 2 * logBudget n ^ 3 * (n : ℝ) ^ (255 / 256 : ℝ))) := by
        apply mul_le_mul CBound _ (mul_nonneg (mul_nonneg WNonnegative mLogNonnegative) tailNonnegative)
          (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (one_add_log_step_le n nPositive) WNonnegative)
          tailBound tailNonnegative (mul_nonneg WNonnegative BNonnegative)
      _ = _ := by unfold W; ring
  · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
    simp [primitiveDyad, empty, primitiveBlock, constantNonnegative]

private theorem norm_primitivePair_le (F : ShortSuffixWaves n ι) (nLower : 2 ≤ n)
    {T : ℝ} (TNonnegative : 0 ≤ T) (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (wBound : F.WeightBound (T * logBudget n)) :
    ‖F.primitivePair‖ ≤
      10240000 * gcdSeriesConstant * T ^ 5 * logBudget n ^ 7 * (n : ℝ) ^ (255 / 256 : ℝ) := by
  let C := 2048000 * gcdSeriesConstant * T ^ 5 * logBudget n ^ 6 * (n : ℝ) ^ (255 / 256 : ℝ)
  have logNonnegative : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
  have CNonnegative : 0 ≤ C := by unfold C; have := gcdSeriesConstant_nonnegative; positivity
  rw [primitivePair_eq_dyads F (by omega)]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ dyadicIndices n, C :=
      sum_le_sum fun k _ => norm_primitiveDyad_le F k nLower TNonnegative divisorBound wBound
    _ = ((Nat.log 2 n : ℝ) + 1) * C := by simp [dyadicIndices, nsmul_eq_mul]
    _ ≤ (5 * logBudget n) * C := mul_le_mul_of_nonneg_right (natLog_succ_le nLower le_rfl) CNonnegative
    _ = _ := by unfold C; ring

theorem norm_deepIntegral_le (F : ShortSuffixWaves n ι) (nLower : 2 ≤ n)
    (width : 4 * cutoffH n * maximumStep n ≤ n)
    {T : ℝ} (TLower : 1 ≤ T) (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (wBound : F.WeightBound (T * logBudget n)) :
    ‖F.deepIntegral‖ ≤ totalConstant * finalScale n T := by
  let A := T ^ 2 * logBudget n
  let W := T * logBudget n
  have nPositive : 0 < n := by omega
  have TNonnegative : 0 ≤ T := zero_le_one.trans TLower
  have BNonnegative : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
  have ANonnegative : 0 ≤ A := mul_nonneg (sq_nonneg _) BNonnegative
  have WNonnegative : 0 ≤ W := mul_nonneg TNonnegative BNonnegative
  have aBound (m : ℕ) (membership : m ∈ range (n + 1)) : ‖lowCoefficients n m‖ ≤ A := by
    have mBound : m ≤ n := Nat.le_of_lt_succ (mem_range.mp membership)
    unfold lowCoefficients A
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_lowBandCoefficient_le (cutoffU n) (lowCut n) m n mBound nPositive).trans
      (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (divisorBound m mBound) 2)
        (log_le_logBudget nPositive le_rfl) (Real.log_nonneg (by exact_mod_cast nPositive)) (sq_nonneg _))
  have far := (norm_farIntegral_le F nPositive (outsideScale_positive n nPositive)
    ANonnegative WNonnegative aBound wBound).trans (outside_budget_le n nPositive TLower)
  have smooth := (norm_exact_sub_smoothed F nPositive ANonnegative TNonnegative aBound divisorBound wBound).trans
    (smoothing_budget_le n nPositive TLower)
  have primitive := (norm_smoothed_sub_primitive F nPositive TNonnegative divisorBound wBound).trans
    (primitive_replacement_budget_le n nLower TLower)
  have main : ‖F.primitivePair‖ ≤ (10240000 * gcdSeriesConstant) * finalScale n T :=
    (norm_primitivePair_le F nLower TNonnegative divisorBound wBound).trans_eq (by unfold finalScale; ring)
  have approxNorm (x y : ℂ) : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - y) y
  rw [deep_split F nPositive width]
  have triangle := norm_add_le F.farIntegral F.exactPair
  have first := approxNorm F.exactPair F.smoothedPair
  have second := approxNorm F.smoothedPair F.primitivePair
  unfold totalConstant
  linarith only [triangle, first, second, far, smooth, primitive, main]

end

end ShortSuffixWaves

end B13NondividingResidueReductionProof

end

/- Left type one -/
section

namespace B13NondividingResidueReductionProof

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

def leftTypeOneRadius (n : ℕ) : ℝ := 1 / (4 * (n : ℝ) ^ (15 / 16 : ℝ))

def leftTypeOneCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (13 / 48 : ℝ)⌋₊

private theorem left_type_one_radius_le_wide {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (gated : q ≤ leftTypeOneCap n) :
    leftTypeOneRadius n ≤ (cutoffH n : ℝ) / ((q : ℝ) * n) := by
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have qr : (0 : ℝ) < q := by exact_mod_cast hq
  have cap : (q : ℝ) ≤ (n : ℝ) ^ (13 / 48 : ℝ) :=
    (show (q : ℝ) ≤ (leftTypeOneCap n : ℝ) by exact_mod_cast gated).trans (Nat.floor_le (by positivity))
  have bFloor : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ (cutoffB n : ℝ) :=
    floor_half_le (Real.one_le_rpow nOne (by norm_num))
  have logPos : 1 ≤ Nat.log 2 (n + 2) := Nat.log_pos (by decide) (by omega)
  have boundH : (cutoffB n : ℝ) ≤ cutoffH n := by
    have hN : cutoffB n ≤ cutoffH n := by
      unfold cutoffH
      simpa only [mul_one] using Nat.mul_le_mul (show cutoffB n ≤ 256 * cutoffB n by omega)
        (show 1 ≤ (Nat.log 2 (n + 2)) ^ 2 from one_le_pow₀ logPos)
    exact_mod_cast hN
  have power : (n : ℝ) ^ (15 / 16 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) =
    (n : ℝ) ^ (13 / 48 : ℝ) * (n : ℝ) := by
    calc
      _ = (n : ℝ) ^ (61 / 48 : ℝ) := by rw [← Real.rpow_add nr]; norm_num
      _ = (n : ℝ) ^ (13 / 48 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [← Real.rpow_add nr]; norm_num
      _ = _ := by rw [Real.rpow_one]
  apply (le_div_iff₀ (mul_pos qr nr)).mpr
  calc
    _ ≤ leftTypeOneRadius n * ((n : ℝ) ^ (13 / 48 : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cap nr.le) (by unfold leftTypeOneRadius; positivity)
    _ = (n : ℝ) ^ (1 / 3 : ℝ) / 4 := by
      rw [← power]
      unfold leftTypeOneRadius
      field_simp
    _ ≤ cutoffH n := by linarith only [bFloor, boundH, Real.rpow_nonneg nr.le (1 / 3 : ℝ)]

theorem left_type_one_grids_covered {n g : ℕ} (hn : 0 < n) (hg : 0 < g)
    (short : g ≤ leftTypeOneCap n) :
    gridNear (leftTypeOneRadius n) g ⊆ wide n (cutoffB n) (cutoffH n) := by
  rintro t ⟨j, jBound, near⟩
  let z := j.gcd g
  have hz : 0 < z := Nat.gcd_pos_of_pos_right j hg
  have dvdG : z ∣ g := Nat.gcd_dvd_right j g
  have dvdJ : z ∣ j := Nat.gcd_dvd_left j g
  let q := g / z
  let a := j / z
  have qPos : 0 < q := Nat.div_pos (Nat.le_of_dvd hg dvdG) hz
  have qLe : q ≤ leftTypeOneCap n := (Nat.div_le_self g z).trans short
  have bLe : leftTypeOneCap n ≤ cutoffB n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
  have same : (j : ℝ) / g = (a : ℝ) / q := by
    apply (div_eq_div_iff (by exact_mod_cast hg.ne') (by exact_mod_cast qPos.ne')).mpr
    exact_mod_cast (show j * q = a * g from calc
      _ = (a * z) * q := by rw [show a * z = j from Nat.div_mul_cancel dvdJ]
      _ = a * (q * z) := by ring
      _ = _ := by rw [show q * z = g from Nat.div_mul_cancel dvdG])
  refine ⟨q, a, qPos, qLe.trans bLe, Nat.div_le_div_right jBound,
    Nat.coprime_div_gcd_div_gcd hz, ?_⟩
  rw [← same]
  exact near.trans (left_type_one_radius_le_wide hn qPos qLe)

private theorem shortLeftMask_energy {ι : Type*} (items : Finset ι) {n : ℕ} (hn : 0 < n)
    {W : ℝ} (W0 : 0 ≤ W) (g l r : ι → ℕ) (c : ι → ℂ)
    (steps : ∀ i ∈ items, 0 < g i ∧ g i ≤ leftTypeOneCap n)
    (ends : ∀ i ∈ items, r i ≤ n / g i)
    (weights : ∀ u ∈ Icc 1 (leftTypeOneCap n), (∑ i ∈ items.filter (fun i => g i = u), ‖c i‖) ≤ W) :
    (∫ t in (0 : ℝ)..1, ‖∑ i ∈ items, c i * offWave (leftTypeOneRadius n) (g i) (l i) (r i) t‖ ^ 2) ≤
      640 * W ^ 2 * (n : ℝ) ^ (15 / 16 : ℝ) * logBudget n ^ 3 := by
  let M := leftTypeOneCap n
  let L := logBudget n
  let P := (n : ℝ) ^ (15 / 16 : ℝ)
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have mPos : 0 < M := Nat.le_floor (Real.one_le_rpow nOne (by norm_num))
  have mBound : M ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nOne (by norm_num))
  have mScale : (M : ℝ) ≤ (n : ℝ) ^ (13 / 48 : ℝ) := Nat.floor_le (by positivity)
  have bPos : 0 < leftTypeOneRadius n := by unfold leftTypeOneRadius; positivity
  have L1 : 1 ≤ L := one_le_logBudget n
  have logM : 1 + Real.log M ≤ L := by
    unfold L logBudget
    gcongr
    have realM : (M : ℝ) ≤ n := by exact_mod_cast mBound
    linarith only [realM]
  have logM0 : 0 ≤ 1 + Real.log M :=
    (add_nonneg) zero_le_one (Real.log_nonneg (by exact_mod_cast mPos))
  have mSq : (M : ℝ) ^ 2 ≤ P := calc
    _ ≤ ((n : ℝ) ^ (13 / 48 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) mScale 2
    _ = (n : ℝ) ^ (13 / 24 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le]; norm_num
    _ ≤ P := Real.rpow_le_rpow_of_exponent_le nOne (by norm_num)
  have inv : (leftTypeOneRadius n)⁻¹ = 4 * P := by unfold leftTypeOneRadius P; simp
  refine (offWave_mass_le_weighted items n M (leftTypeOneRadius n) W mPos mBound bPos W0
    g l r c steps ends weights).trans ?_
  change 128 * W ^ 2 * ((M : ℝ) ^ 2 * L ^ 2 + (leftTypeOneRadius n)⁻¹ * (1 + Real.log M) ^ 3) ≤ _
  rw [inv]
  have first : (M : ℝ) ^ 2 * L ^ 2 ≤ P * L ^ 3 :=
    mul_le_mul mSq (pow_le_pow_right₀ L1 (by decide)) (sq_nonneg _) (by positivity)
  have second : (4 * P) * (1 + Real.log M) ^ 3 ≤ 4 * P * L ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ logM0 logM _) (by positivity)
  calc
    _ ≤ 128 * W ^ 2 * (P * L ^ 3 + 4 * P * L ^ 3) :=
      mul_le_mul_of_nonneg_left (add_le_add first second) (by positivity)
    _ = _ := by unfold P L; ring

theorem shortLeftWavePair_bound {ι : Type*} (items : Finset ι) {n : ℕ} (hn : 0 < n)
    {W : ℝ} (W0 : 0 ≤ W) (g l r : ι → ℕ) (c : ι → ℂ)
    (steps : ∀ i ∈ items, 0 < g i ∧ g i ≤ leftTypeOneCap n)
    (ends : ∀ i ∈ items, r i ≤ n / g i)
    (weights : ∀ u ∈ Icc 1 (leftTypeOneCap n), (∑ i ∈ items.filter (fun i => g i = u), ‖c i‖) ≤ W)
    (A : ℕ → ℂ) {B : ℝ} (coefficients : ∀ m ≤ n, ‖A m‖ ≤ B) :
    ‖∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator (fun x =>
        shiftedPolynomial n A x * (∑ i ∈ items, c i * wave (g i) (l i) (r i) x)) t‖ ≤
      (n : ℝ) ^ (31 / 32 : ℝ) * (B ^ 2 + 320 * W ^ 2 * logBudget n ^ 3) := by
  let f := shiftedPolynomial n A
  let s := (wide n (cutoffB n) (cutoffH n))ᶜ
  let u (t : ℝ) := ∑ i ∈ items, c i * offWave (leftTypeOneRadius n) (g i) (l i) (r i) t
  let scale := (n : ℝ) ^ (-(1 / 32) : ℝ)
  let P := (n : ℝ) ^ (31 / 32 : ℝ)
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have scalePositive : 0 < scale := Real.rpow_pos_of_pos nr _
  have replacement :
      (∫ t in (0 : ℝ)..1, s.indicator (fun x =>
        f x * (∑ i ∈ items, c i * wave (g i) (l i) (r i) x)) t) =
      ∫ t in (0 : ℝ)..1, s.indicator (fun x => f x * u x) t := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    by_cases member : t ∈ s
    · simp only [Set.indicator_of_mem member]
      apply congrArg (f t * ·)
      refine sum_congr rfl fun i hi => ?_
      have outside : t ∉ gridNear (leftTypeOneRadius n) (g i) := fun h =>
        member (left_type_one_grids_covered hn (steps i hi).1 (steps i hi).2 h)
      have off : t ∈ (gridNear (leftTypeOneRadius n) (g i))ᶜ := outside
      rw [offWave, Set.indicator_of_mem off]
    · simp only [Set.indicator_of_notMem member]
  rw [replacement]
  have fCont : Continuous f := shiftedPolynomial_continuous n A
  have uMeas : Measurable u :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (offWave_measurable ..)
  have uInt : IntervalIntegrable (fun t => ‖u t‖ ^ 2) volume 0 1 :=
    (interval_sq_bound_of_uniform uMeas (K := ∑ i ∈ items, ‖c i‖ * (r i : ℝ)) (fun t _ =>
      (norm_sum_le _ _).trans (sum_le_sum (fun i _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_offWave_le _ _ _ _ t) (norm_nonneg _))))).1
  have fMass : (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) ≤ ((n : ℝ) + 1) * B ^ 2 := by
    unfold f
    rw [shiftedPolynomial_parseval]
    calc
      _ ≤ ∑ _ ∈ range (n + 1), B ^ 2 := sum_le_sum fun m hm => pow_le_pow_left₀ (norm_nonneg _)
        (coefficients m (Nat.le_of_lt_succ (mem_range.mp hm))) 2
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_range, Nat.cast_add, Nat.cast_one]
  have uMass := shortLeftMask_energy items hn W0 g l r c steps ends weights
  have fPower : scale * (n : ℝ) = P := by
    unfold scale P
    calc
      _ = (n : ℝ) ^ (-(1 / 32) : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add nr]; norm_num
  have uPower : scale⁻¹ * (n : ℝ) ^ (15 / 16 : ℝ) = P := by
    unfold scale P
    rw [Real.rpow_neg nr.le, inv_inv, ← Real.rpow_add nr]
    norm_num
  have fTerm : scale * (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) ≤ 2 * P * B ^ 2 := calc
    _ ≤ scale * (((n : ℝ) + 1) * B ^ 2) := mul_le_mul_of_nonneg_left fMass scalePositive.le
    _ ≤ scale * (2 * (n : ℝ) * B ^ 2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by linarith only [nOne]) (sq_nonneg _)) scalePositive.le
    _ = _ := by rw [← fPower]; ring
  have uTerm : scale⁻¹ * (∫ t in (0 : ℝ)..1, ‖u t‖ ^ 2) ≤ 640 * W ^ 2 * P * logBudget n ^ 3 := calc
    _ ≤ scale⁻¹ * (640 * W ^ 2 * (n : ℝ) ^ (15 / 16 : ℝ) * logBudget n ^ 3) :=
      mul_le_mul_of_nonneg_left uMass (inv_nonneg.mpr scalePositive.le)
    _ = _ := by rw [← uPower]; ring
  refine (norm_indicator_product_le scalePositive ((wide_measurable ..).compl) fCont.measurable uMeas
    ((fCont.norm.pow 2).intervalIntegrable 0 1) uInt).trans ?_
  refine (mul_le_mul_of_nonneg_left (add_le_add fTerm uTerm) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq ?_
  unfold P
  ring

end

end B13NondividingResidueReductionProof

end

/- Left zeta -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcDecomposition DyadicMixedB4Scale DyadicMixedB4ArcGeometry
open DyadicMixedB4Arithmetic DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4MoebiusGauss
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def leftBandMoebius (n a : ℕ) : ℝ :=
  ∑ d ∈ a.divisors.filter (fun d => cutoffU n < d), (μ d : ℝ)

theorem leftBand_polynomial_eq_cofactor_sum (n : ℕ) (hn : 0 < n) (w : ℕ → ℝ) (t : ℝ) :
    plainPolynomial n (fun m => (bandCoefficient n (cutoffU n) (lowCut n) w m : ℂ)) t =
      ∑ a ∈ Ioc (cutoffU n) (lowCut n), (leftBandMoebius n a : ℂ) *
        ∑ y ∈ Ioc (cutoffU n) (n / a), (w y : ℂ) * phase (((a * y : ℕ) : ℝ) * t) := by
  let U := cutoffU n
  let B := lowCut n
  let term (a y : ℕ) :=
    if (U < a ∧ a ≤ B) ∧ U < y then
      (leftBandMoebius n a : ℂ) * (w y : ℂ) * phase (((a * y : ℕ) : ℝ) * t) else 0
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have Bn : B ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nOne (by norm_num))
  have rangeFilter : (Icc 1 n).filter (fun a => U < a ∧ a ≤ B) = Ioc U B := by
    ext a
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  calc
    _ = ∑ m ∈ Icc 1 n, (bandCoefficient n (cutoffU n) (lowCut n) w m : ℂ) * phase ((m : ℝ) * t) := by
      unfold plainPolynomial
      symm
      refine sum_subset (fun m hm => mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hm).2)) ?_
      intro m hm excluded
      have eq : m = 0 := by
        by_contra! pos
        exact excluded (mem_Icc.mpr ⟨Nat.pos_of_ne_zero pos, Nat.le_of_lt_succ (mem_range.mp hm)⟩)
      simp [eq, bandCoefficient]
    _ = ∑ m ∈ Icc 1 n, ∑ a ∈ m.divisors, term a (m / a) := by
      refine sum_congr rfl fun m _ => ?_
      unfold bandCoefficient
      rw [sum_filter, Complex.ofReal_sum, sum_mul]
      refine sum_congr rfl fun a ha => ?_
      have div : a * (m / a) = m := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)
      unfold term
      rw [div]
      by_cases h : (U < a ∧ a ≤ B) ∧ U < m / a
      · have hd : cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a := ⟨h.1.1,h.1.2,h.2⟩
        rw [if_pos hd, if_pos h, Complex.ofReal_mul]
        rfl
      · have hd : ¬(cutoffU n < a ∧ a ≤ lowCut n ∧ cutoffU n < m / a) :=
          fun e => h ⟨⟨e.1,e.2.1⟩,e.2.2⟩
        simp only [hd, h, ite_false, Complex.ofReal_zero, zero_mul]
    _ = ∑ a ∈ Icc 1 n, ∑ y ∈ Icc 1 (n / a), term a y := finite_divisor_hyperbola n term
    _ = ∑ a ∈ Icc 1 n, if U < a ∧ a ≤ B then (leftBandMoebius n a : ℂ) *
          ∑ y ∈ Ioc U (n / a), (w y : ℂ) * phase (((a * y : ℕ) : ℝ) * t) else 0 := by
      refine sum_congr rfl fun a _ => ?_
      by_cases gate : U < a ∧ a ≤ B
      · have inner : (Icc 1 (n / a)).filter (fun y => U < y) = Ioc U (n / a) := by
          ext y
          simp only [mem_filter, mem_Icc, mem_Ioc]
          omega
        simp only [gate, ite_true, mul_sum]
        rw [← inner, sum_filter]
        refine sum_congr rfl fun y _ => ?_
        unfold term
        by_cases h : U < y <;> simp [gate, h, mul_assoc]
      · simp [term, gate]
    _ = _ := by rw [← sum_filter, rangeFilter]

theorem zeta_cofactor_sum_eq_waves (n U a S : ℕ) (f : ArithmeticFunction ℝ)
    (truncated : ∀ s, S < s → f s = 0) (t : ℝ) :
    (∑ y ∈ Ioc U (n / a), (((f * (ζ : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) y : ℝ) : ℂ) * phase (((a * y : ℕ) : ℝ) * t)) =
      ∑ s ∈ Icc 1 S, (f s : ℂ) * wave (a * s) (U / s) (n / (a * s)) t := by
  let N := n / a
  let term (s k : ℕ) :=
    if U < s * k then (f s : ℂ) * phase (((a * s * k : ℕ) : ℝ) * t) else 0
  let F (s : ℕ) := (f s : ℂ) * wave (a * s) (U / s) (n / (a * s)) t
  have inside : (Icc 1 N).filter (fun y => U < y) = Ioc U N := by
    ext y
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  have ordered (s : ℕ) (hs : 0 < s) :
      (Icc 1 (N / s)).filter (fun k => U < s * k) = Ioc (U / s) (n / (a * s)) := by
    unfold N
    rw [Nat.div_div_eq_div_mul]
    ext k
    simp only [mem_filter, mem_Icc, mem_Ioc]
    have same : U / s < k ↔ U < s * k := by simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hs)
    rw [same]
    constructor
    · exact fun h => ⟨h.2,h.1.2⟩
    · intro h
      have kPos : 0 < k := Nat.pos_of_ne_zero (fun zero => by simp [zero] at h)
      exact ⟨⟨kPos,h.2⟩,h.1⟩
  calc
    _ = ∑ y ∈ Icc 1 N, ∑ s ∈ y.divisors, term s (y / s) := by
      rw [← inside, sum_filter]
      refine sum_congr rfl fun y _ => ?_
      by_cases h : U < y
      · simp only [h, ite_true, coe_mul_zeta_apply, Complex.ofReal_sum, sum_mul]
        refine sum_congr rfl fun s hs => ?_
        have div : s * (y / s) = y := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hs)
        have multiplied : a * s * (y / s) = a * y := by rw [Nat.mul_assoc,div]
        simp only [term, div, multiplied, h, ite_true]
      · simp only [h, ite_false]
        symm
        refine sum_eq_zero fun s hs => ?_
        simp [term, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hs), h]
    _ = ∑ s ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / s), term s k := finite_divisor_hyperbola N term
    _ = ∑ s ∈ Icc 1 N, F s := by
      refine sum_congr rfl fun s hs => ?_
      unfold F wave
      rw [mul_sum, ← ordered s (mem_Icc.mp hs).1, sum_filter]
    _ = ∑ s ∈ Icc 1 (max N S), F s := by
      refine sum_subset (fun s hs => mem_Icc.mpr ⟨(mem_Icc.mp hs).1,(mem_Icc.mp hs).2.trans (le_max_left ..)⟩)
        fun s hs outside => ?_
      have large : N < s := by
        exact lt_of_not_ge (fun hi => outside (mem_Icc.mpr ⟨(mem_Icc.mp hs).1,hi⟩))
      have zero : n / (a*s) = 0 := by
        rw [← Nat.div_div_eq_div_mul]
        exact Nat.div_eq_of_lt large
      simp [F, wave, zero]
    _ = _ := by
      symm
      refine sum_subset (fun s hs => mem_Icc.mpr ⟨(mem_Icc.mp hs).1,(mem_Icc.mp hs).2.trans (le_max_right ..)⟩)
        fun s hs outside => ?_
      have large : S < s := lt_of_not_ge (fun hi => outside (mem_Icc.mpr ⟨(mem_Icc.mp hs).1,hi⟩))
      simp [F, truncated s large]

theorem left_band_short_zeta_polynomial_eq_waves (n S : ℕ) (hn : 0 < n) (f : ArithmeticFunction ℝ)
    (truncated : ∀ s, S < s → f s = 0) (t : ℝ) :
    plainPolynomial n (fun m => (bandCoefficient n (cutoffU n) (lowCut n) (fun y => ((f * (ζ : ArithmeticFunction ℝ)) : ArithmeticFunction ℝ) y) m : ℂ)) t =
      ∑ i ∈ Ioc (cutoffU n) (lowCut n) ×ˢ Icc 1 S,
        (leftBandMoebius n i.1 : ℂ) * (f i.2 : ℂ) *
          wave (i.1 * i.2) (cutoffU n / i.2) (n / (i.1 * i.2)) t := by
  rw [leftBand_polynomial_eq_cofactor_sum n hn,
    Finset.sum_product (Ioc (cutoffU n) (lowCut n)) (Icc 1 S)
      (fun i : ℕ × ℕ => (leftBandMoebius n i.1 : ℂ) * (f i.2 : ℂ) *
        wave (i.1 * i.2) (cutoffU n / i.2) (n / (i.1 * i.2)) t)]
  refine sum_congr rfl fun a _ => ?_
  rw [zeta_cofactor_sum_eq_waves n (cutoffU n) a S f truncated t, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  ring

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

def leftTypeOneFactorCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 48 : ℝ)⌋₊

private theorem left_short_pair_bounds {n : ℕ} (hn : 0 < n) {i : ℕ × ℕ}
    (hi : i ∈ Ioc (cutoffU n) (lowCut n) ×ˢ Icc 1 (leftTypeOneFactorCap n)) :
    0 < i.1 ∧ i.1 ≤ n ∧ 0 < i.2 ∧ i.2 ≤ n := by
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have aBound : lowCut n ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nOne (by norm_num))
  have bBound : leftTypeOneFactorCap n ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nOne (by norm_num))
  obtain ⟨ha,hb⟩ := mem_product.mp hi
  obtain ⟨lo,up⟩ := mem_Ioc.mp ha
  obtain ⟨bLo,bUp⟩ := mem_Icc.mp hb
  exact ⟨(Nat.zero_le _).trans_lt lo, up.trans aBound,bLo,bUp.trans bBound⟩

theorem left_short_wave_step {n : ℕ} (hn : 0 < n) {i : ℕ × ℕ}
    (hi : i ∈ Ioc (cutoffU n) (lowCut n) ×ˢ Icc 1 (leftTypeOneFactorCap n)) :
    0 < i.1 * i.2 ∧ i.1 * i.2 ≤ leftTypeOneCap n := by
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨aPos,_,bPos,_⟩ := left_short_pair_bounds hn hi
  have aReal : (i.1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    refine (show (i.1 : ℝ) ≤ lowCut n by exact_mod_cast (mem_Ioc.mp (mem_product.mp hi).1).2).trans ?_
    exact Nat.floor_le (by positivity)
  have bReal : (i.2 : ℝ) ≤ (n : ℝ) ^ (1 / 48 : ℝ) := by
    refine (show (i.2 : ℝ) ≤ leftTypeOneFactorCap n by exact_mod_cast (mem_Icc.mp (mem_product.mp hi).2).2).trans ?_
    exact Nat.floor_le (by positivity)
  refine ⟨Nat.mul_pos aPos bPos,Nat.le_floor ?_⟩
  push_cast
  calc
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 48 : ℝ) :=
      mul_le_mul aReal bReal (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add nr]; norm_num

theorem norm_left_short_weights {n : ℕ} (hn : 0 < n) (f : ArithmeticFunction ℝ)
    {T E : ℝ} (t0 : 0 ≤ T) (e0 : 0 ≤ E)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (factorBound : ∀ m ≤ n, ‖(f m : ℂ)‖ ≤ E)
    (u : ℕ) (hu : u ∈ Icc 1 (leftTypeOneCap n)) :
    (∑ i ∈ (Ioc (cutoffU n) (lowCut n) ×ˢ Icc 1 (leftTypeOneFactorCap n)).filter
      (fun i => i.1 * i.2 = u), ‖(leftBandMoebius n i.1 : ℂ) * (f i.2 : ℂ)‖) ≤ T ^ 2 * E := by
  let items := Ioc (cutoffU n) (lowCut n) ×ˢ Icc 1 (leftTypeOneFactorCap n)
  let v (i : ℕ × ℕ) := i.1 * i.2
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have cap : leftTypeOneCap n ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nOne (by norm_num))
  let selected := items.filter (fun i => v i = u)
  have count : selected.card ≤ u.divisors.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro i hi
      have member : i ∈ selected := hi
      have equal := (mem_filter.mp member).2
      change i.1 ∈ u.divisors
      refine Nat.mem_divisors.mpr ⟨?_, Nat.ne_of_gt (mem_Icc.mp hu).1⟩
      exact ⟨i.2, equal.symm⟩
    · intro x hx y hy first
      have xx : x ∈ selected := hx
      have yy : y ∈ selected := hy
      have eq : x.1 * x.2 = y.1 * y.2 := (mem_filter.mp xx).2.trans (mem_filter.mp yy).2.symm
      have aPos := (left_short_pair_bounds hn (mem_filter.mp xx).1).1
      apply Prod.ext first
      rw [← first] at eq
      exact Nat.eq_of_mul_eq_mul_left aPos eq
  have countReal : (selected.card : ℝ) ≤ T :=
    (show (selected.card : ℝ) ≤ u.divisors.card by exact_mod_cast count).trans
      (divisorBound u ((mem_Icc.mp hu).2.trans cap))
  calc
    _ ≤ ∑ _ ∈ selected, T * E := by
      refine sum_le_sum fun i hi => ?_
      obtain ⟨_,aBound,_,bBound⟩ := left_short_pair_bounds hn (mem_filter.mp hi).1
      rw [norm_mul]
      refine mul_le_mul ((norm_leftBandMoebius_le n i.1).trans (divisorBound _ aBound))
        (factorBound _ bBound) (norm_nonneg _) t0
    _ = (selected.card : ℝ) * (T * E) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ T * (T * E) := mul_le_mul_of_nonneg_right countReal (mul_nonneg t0 e0)
    _ = _ := by ring

theorem norm_left_zeta_pair_le {n : ℕ} (hn : 0 < n) (f : ArithmeticFunction ℝ)
    (short : ∀ y, leftTypeOneFactorCap n < y → f y = 0)
    {T E : ℝ} (t0 : 0 ≤ T) (e0 : 0 ≤ E)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (factorBound : ∀ m ≤ n, ‖(f m : ℂ)‖ ≤ E)
    (A : ℕ → ℂ) {B : ℝ} (coefficients : ∀ m ≤ n, ‖A m‖ ≤ B) :
    ‖∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator (fun x =>
        shiftedPolynomial n A x *
          plainPolynomial n (fun m => (bandCoefficient n (cutoffU n) (lowCut n) (fun y => ((f * (ζ : ArithmeticFunction ℝ)) : ArithmeticFunction ℝ) y) m : ℂ)) x) t‖ ≤
      (n : ℝ) ^ (31 / 32 : ℝ) * (B ^ 2 + 320 * (T ^ 2 * E) ^ 2 * logBudget n ^ 3) := by
  let S := leftTypeOneFactorCap n
  let items := Ioc (cutoffU n) (lowCut n) ×ˢ Icc 1 S
  let v (i : ℕ × ℕ) := i.1 * i.2
  let c (i : ℕ × ℕ) := (leftBandMoebius n i.1 : ℂ) * (f i.2 : ℂ)
  simp_rw [left_band_short_zeta_polynomial_eq_waves n S hn f short]
  exact shortLeftWavePair_bound items hn (by positivity) v (fun i => cutoffU n / i.2)
    (fun i => n / v i) c (fun _ hi => left_short_wave_step hn hi) (fun _ _ => le_rfl)
    (norm_left_short_weights hn f t0 e0 divisorBound factorBound) A coefficients

end

end B13NondividingResidueReductionProof

end

/- Abel log wave -/
section

namespace B13NondividingResidueReductionProof

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

private theorem logWaveStep_telescope {k r : ℕ} (hk : k ≤ r) :
    (∑ j ∈ Icc k r, logWaveStep r j) = Real.log k := by
  have I : Icc k r = Ico k (r + 1) := by
    ext i
    simp only [mem_Icc, mem_Ico]
    omega
  rw [I]
  unfold logWaveStep
  have telescoped := telescoping_Ico (hk.trans (Nat.le_succ _)) (fun j => - clippedLog r j)
  have out : ¬ r + 1 ≤ r := by omega
  simpa only [neg_sub_neg, clippedLog, out, hk, ite_true, ite_false, sub_zero] using telescoped

theorem log_wave_eq_weighted_prefixes (v l r : ℕ) (t : ℝ) :
    (∑ k ∈ Ioc l r, (Real.log k : ℂ) * phase (((v * k : ℕ) : ℝ) * t)) =
      ∑ j ∈ Ioc l r, (logWaveStep r j : ℂ) * wave v l j t := by
  let E (k : ℕ) := phase (((v * k : ℕ) : ℝ) * t)
  symm
  calc
    _ = ∑ j ∈ Ioc l r, ∑ k ∈ Ioc l r, if k ≤ j then (logWaveStep r j : ℂ) * E k else 0 := by
      refine sum_congr rfl fun j hj => ?_
      have select : (Ioc l r).filter (fun k => k ≤ j) = Ioc l j := by
        ext k
        simp only [mem_filter, mem_Ioc]
        have upper := (mem_Ioc.mp hj).2
        omega
      unfold wave E
      rw [← select, mul_sum, sum_filter]
    _ = ∑ k ∈ Ioc l r, ∑ j ∈ Icc k r, (logWaveStep r j : ℂ) * E k := by
      rw [sum_comm]
      refine sum_congr rfl fun k hk => ?_
      have select : (Ioc l r).filter (fun j => k ≤ j) = Icc k r := by
        ext j
        simp only [mem_filter, mem_Ioc, mem_Icc]
        have lower := (mem_Ioc.mp hk).1
        omega
      rw [← sum_filter, select]
    _ = _ := by
      refine sum_congr rfl fun k hk => ?_
      rw [← sum_mul, ← Complex.ofReal_sum, logWaveStep_telescope (mem_Ioc.mp hk).2]

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

def suffixLogIncrement (l j : ℕ) : ℝ :=
  Real.log (j + 1 : ℕ) - if j = l then 0 else Real.log j

private theorem suffix_log_increment_nonneg {l j : ℕ} (h : l ≤ j) :
    0 ≤ suffixLogIncrement l j := by
  by_cases hEq : j = l
  · simpa [suffixLogIncrement, hEq] using
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le l) : (1 : ℝ) ≤ (l+1 : ℕ))
  · have jPos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    rw [suffixLogIncrement, if_neg hEq]
    exact sub_nonneg.mpr (Real.log_le_log jPos (by exact_mod_cast Nat.le_succ j))

private theorem suffix_log_increment_sum {l k : ℕ} (h : l < k) :
    (∑ j ∈ Ico l k, suffixLogIncrement l j) = Real.log k := by
  rw [← sum_Ico_consecutive _ (Nat.le_succ l) (Nat.succ_le_iff.mpr h), Nat.Ico_succ_singleton, sum_singleton]
  have tail : (∑ j ∈ Ico (l+1) k, suffixLogIncrement l j) =
      Real.log k - Real.log (l+1 : ℕ) := by
    calc
      _ = ∑ j ∈ Ico (l+1) k, (Real.log (j+1 : ℕ) - Real.log j) := by
        refine sum_congr rfl fun j hj => ?_
        exact by simp [suffixLogIncrement, (show j ≠ l by have := (mem_Ico.mp hj).1; omega)]
      _ = _ := telescoping_Ico (Nat.succ_le_iff.mpr h) (fun j => Real.log (j : ℝ))
  rw [tail]
  simp [suffixLogIncrement]

theorem log_wave_suffix_weights_le (l r : ℕ) :
    (∑ j ∈ Ico l r, ‖(suffixLogIncrement l j : ℂ)‖) ≤ Real.log r := by
  by_cases h : l < r
  · have same : (∑ j ∈ Ico l r, ‖(suffixLogIncrement l j : ℂ)‖) =
        ∑ j ∈ Ico l r, suffixLogIncrement l j := by
      refine sum_congr rfl fun j hj => ?_
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (suffix_log_increment_nonneg (mem_Ico.mp hj).1)]
    rw [same, suffix_log_increment_sum h]
  · rw [Ico_eq_empty_of_le (le_of_not_gt h), sum_empty]
    cases r with
    | zero => simp
    | succ r => exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r))

theorem log_wave_eq_weighted_suffixes (v l r : ℕ) (t : ℝ) :
    (∑ k ∈ Ioc l r, (Real.log k : ℂ) * phase (((v * k : ℕ) : ℝ) * t)) =
      ∑ j ∈ Ico l r, (suffixLogIncrement l j : ℂ) * wave v j r t := by
  let e (k : ℕ) := phase (((v*k : ℕ) : ℝ) * t)
  symm
  calc
    _ = ∑ j ∈ Ico l r, ∑ k ∈ Ioc l r,
        if j < k then (suffixLogIncrement l j : ℂ) * e k else 0 := by
      refine sum_congr rfl fun j hj => ?_
      have same : (Ioc l r).filter (fun k => j < k) = Ioc j r := by
        ext k
        simp only [mem_filter, mem_Ioc]
        have := (mem_Ico.mp hj).1
        omega
      rw [← sum_filter, same]
      unfold wave
      rw [mul_sum]
    _ = ∑ k ∈ Ioc l r, ∑ j ∈ Ico l r,
        if j < k then (suffixLogIncrement l j : ℂ) * e k else 0 := sum_comm
    _ = _ := by
      refine sum_congr rfl fun k hk => ?_
      have same : (Ico l r).filter (fun j => j < k) = Ico l k := by
        ext j
        simp only [mem_filter, mem_Ico]
        have := (mem_Ioc.mp hk).2
        omega
      rw [← sum_filter, same, ← sum_mul, ← Complex.ofReal_sum, suffix_log_increment_sum (mem_Ioc.mp hk).1]

end

end B13NondividingResidueReductionProof

end

/- Left log expansion -/
section

namespace B13NondividingResidueReductionProof

open Finset DyadicMixedB4Geometric DyadicMixedB4Scale
open DyadicMixedB4ArcDecomposition DyadicMixedB4Arithmetic DyadicMixedB4PairIntegral
open ArithmeticFunction
open scoped Classical

noncomputable section

def logarithmicWave (v l r : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Ioc l r, (Real.log k : ℂ) * phase (((v * k : ℕ) : ℝ) * t)

theorem logarithmicWave_eq_prefixes (v l r : ℕ) (t : ℝ) :
    logarithmicWave v l r t = ∑ j ∈ Ioc l r, (logWaveStep r j : ℂ) * wave v l j t :=
  log_wave_eq_weighted_prefixes v l r t

theorem log_cofactor_sum_eq_waves (n U a S : ℕ) (f : ArithmeticFunction ℝ)
    (truncated : ∀ s, S < s → f s = 0) (t : ℝ) :
    (∑ y ∈ Ioc U (n / a), (((f * ArithmeticFunction.log : ArithmeticFunction ℝ) y : ℝ) : ℂ) * phase (((a * y : ℕ) : ℝ) * t)) =
      ∑ s ∈ Icc 1 S, (f s : ℂ) * logarithmicWave (a * s) (U / s) (n / (a * s)) t := by
  let N := n / a
  let term (s k : ℕ) :=
    if U < s * k then (f s : ℂ) * (Real.log k : ℂ) * phase (((a * s * k : ℕ) : ℝ) * t) else 0
  let F (s : ℕ) := (f s : ℂ) * logarithmicWave (a * s) (U / s) (n / (a * s)) t
  have inside : (Icc 1 N).filter (fun y => U < y) = Ioc U N := by
    ext y
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  have ordered (s : ℕ) (hs : 0 < s) :
      (Icc 1 (N / s)).filter (fun k => U < s * k) = Ioc (U / s) (n / (a * s)) := by
    unfold N
    rw [Nat.div_div_eq_div_mul]
    ext k
    simp only [mem_filter, mem_Icc, mem_Ioc]
    have same : U / s < k ↔ U < s * k := by simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hs)
    rw [same]
    constructor
    · exact fun h => ⟨h.2,h.1.2⟩
    · intro h
      have kPos : 0 < k := Nat.pos_of_ne_zero (fun zero => by simp [zero] at h)
      exact ⟨⟨kPos,h.2⟩,h.1⟩
  have coefficients (y : ℕ) : (f * ArithmeticFunction.log : ArithmeticFunction ℝ) y =
      ∑ s ∈ y.divisors, f s * Real.log (y / s : ℕ) := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun s k => f s * ArithmeticFunction.log k)]
    rfl
  calc
    _ = ∑ y ∈ Icc 1 N, ∑ s ∈ y.divisors, term s (y / s) := by
      rw [← inside, sum_filter]
      refine sum_congr rfl fun y _ => ?_
      by_cases h : U < y
      · simp only [h, ite_true, coefficients, Complex.ofReal_sum, sum_mul, Complex.ofReal_mul]
        refine sum_congr rfl fun s hs => ?_
        have div : s * (y / s) = y := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hs)
        have multiplied : a * s * (y / s) = a * y := by rw [Nat.mul_assoc,div]
        simp only [term, div, multiplied, h, ite_true]
      · simp only [h, ite_false]
        symm
        refine sum_eq_zero fun s hs => ?_
        simp [term, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hs), h]
    _ = ∑ s ∈ Icc 1 N, ∑ k ∈ Icc 1 (N / s), term s k := finite_divisor_hyperbola N term
    _ = ∑ s ∈ Icc 1 N, F s := by
      refine sum_congr rfl fun s hs => ?_
      unfold F logarithmicWave
      rw [mul_sum, ← ordered s (mem_Icc.mp hs).1, sum_filter]
      refine sum_congr rfl fun k _ => ?_
      by_cases hit : U < s * k <;> simp [term, hit, mul_assoc]
    _ = ∑ s ∈ Icc 1 (max N S), F s := by
      refine sum_subset (fun s hs => mem_Icc.mpr ⟨(mem_Icc.mp hs).1,(mem_Icc.mp hs).2.trans (le_max_left ..)⟩)
        fun s hs outside => ?_
      have large : N < s := by
        exact lt_of_not_ge (fun hi => outside (mem_Icc.mpr ⟨(mem_Icc.mp hs).1,hi⟩))
      have zero : n / (a*s) = 0 := by
        rw [← Nat.div_div_eq_div_mul]
        exact Nat.div_eq_of_lt large
      simp [F, logarithmicWave, zero]
    _ = _ := by
      symm
      refine sum_subset (fun s hs => mem_Icc.mpr ⟨(mem_Icc.mp hs).1,(mem_Icc.mp hs).2.trans (le_max_right ..)⟩)
        fun s hs outside => ?_
      have large : S < s := lt_of_not_ge (fun hi => outside (mem_Icc.mpr ⟨(mem_Icc.mp hs).1,hi⟩))
      simp [truncated s large]

theorem left_band_short_log_polynomial_eq_waves (n S : ℕ) (hn : 0 < n) (f : ArithmeticFunction ℝ)
    (truncated : ∀ s, S < s → f s = 0) (t : ℝ) :
    plainPolynomial n (fun m => (bandCoefficient n (cutoffU n) (lowCut n) (fun y => ((f * ArithmeticFunction.log) : ArithmeticFunction ℝ) y) m : ℂ)) t =
      ∑ i ∈ Ioc (cutoffU n) (lowCut n) ×ˢ Icc 1 S,
        (leftBandMoebius n i.1 : ℂ) * (f i.2 : ℂ) *
          logarithmicWave (i.1 * i.2) (cutoffU n / i.2) (n / (i.1 * i.2)) t := by
  rw [leftBand_polynomial_eq_cofactor_sum n hn,
    Finset.sum_product (Ioc (cutoffU n) (lowCut n)) (Icc 1 S)
      (fun i : ℕ × ℕ => (leftBandMoebius n i.1 : ℂ) * (f i.2 : ℂ) *
        logarithmicWave (i.1 * i.2) (cutoffU n / i.2) (n / (i.1 * i.2)) t)]
  refine sum_congr rfl fun a _ => ?_
  rw [log_cofactor_sum_eq_waves n (cutoffU n) a S f truncated t, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  ring

end

end B13NondividingResidueReductionProof

end

/- Right type one core -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4ArcDecomposition
open DyadicMixedB4PairIntegral DyadicMixedB4MoebiusGauss DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open DyadicMixedB4Finish DyadicMixedB4NumericBudgets
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

abbrev RightTypeOneIndex := Σ _ : ℕ, ℕ × ℕ

def rightTypeOneItems (n : ℕ) : Finset RightTypeOneIndex :=
  (Icc 1 (cutoffU n)).sigma fun d =>
    shortRightBandIndices n (rightLargeCofactorCut n) d ×ˢ Icc 1 (rightVaughanFactorCap n)

def rightTypeOneStep (i : RightTypeOneIndex) : ℕ := i.1 * i.2.1 * i.2.2

def rightTypeOneLower (n : ℕ) (i : RightTypeOneIndex) : ℕ := rightLargeCofactorCut n / i.2.2

def rightTypeOneWeight (f : ArithmeticFunction ℝ) (i : RightTypeOneIndex) : ℂ :=
  -(μ i.1 : ℂ) * (f i.2.2 : ℂ)

private theorem right_type_one_members {n : ℕ} {i : RightTypeOneIndex} (hi : i ∈ rightTypeOneItems n) :
    i.1 ∈ Icc 1 (cutoffU n) ∧
      i.2.1 ∈ shortRightBandIndices n (rightLargeCofactorCut n) i.1 ∧
      i.2.2 ∈ Icc 1 (rightVaughanFactorCap n) := by
  obtain ⟨d, p⟩ := mem_sigma.mp hi
  exact ⟨d, mem_product.mp p⟩

def restrictLargeRight (n : ℕ) (w : ℕ → ℝ) (b : ℕ) : ℝ :=
  if rightLargeCofactorCut n < b then w b else 0

def rightLargeIntegral (n : ℕ) (w : ℕ → ℝ) : ℂ :=
  mixedIntegral n (bandCoefficient n (cutoffB n) (splitCut n) (restrictLargeRight n w))

private theorem right_zeta_series {n : ℕ} (hn : 0 < n) (f : ArithmeticFunction ℝ)
    (short : ∀ s, rightVaughanFactorCap n < s → f s = 0) (t : ℝ) :
    plainPolynomial n (fun m => (bandCoefficient n (cutoffB n) (splitCut n)
      (restrictLargeRight n (fun b => ((f * (ζ : ArithmeticFunction ℝ)) : ArithmeticFunction ℝ) b)) m : ℂ)) t =
    ∑ i ∈ rightTypeOneItems n, rightTypeOneWeight f i *
      wave (rightTypeOneStep i) (rightTypeOneLower n i) (n / rightTypeOneStep i) t := by
  unfold restrictLargeRight
  rw [right_band_large_cofactor_polynomial hn (cutoffU_le_rightLargeCofactorCut hn) _ t,
    rightTypeOneItems, sum_sigma]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_product, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [zeta_cofactor_sum_eq_waves n (rightLargeCofactorCut n) (d*k) _ f short t, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  simp only [rightTypeOneWeight, rightTypeOneStep, rightTypeOneLower, mul_assoc]

private theorem right_log_series {n : ℕ} (hn : 0 < n) (f : ArithmeticFunction ℝ)
    (short : ∀ s, rightVaughanFactorCap n < s → f s = 0) (t : ℝ) :
    plainPolynomial n (fun m => (bandCoefficient n (cutoffB n) (splitCut n)
      (restrictLargeRight n (fun b => ((f * ArithmeticFunction.log) : ArithmeticFunction ℝ) b)) m : ℂ)) t =
    ∑ i ∈ rightTypeOneItems n, rightTypeOneWeight f i *
      logarithmicWave (rightTypeOneStep i) (rightTypeOneLower n i) (n / rightTypeOneStep i) t := by
  unfold restrictLargeRight
  rw [right_band_large_cofactor_polynomial hn (cutoffU_le_rightLargeCofactorCut hn) _ t,
    rightTypeOneItems, sum_sigma]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_product, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [log_cofactor_sum_eq_waves n (rightLargeCofactorCut n) (d*k) _ f short t, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  simp only [rightTypeOneWeight, rightTypeOneStep, rightTypeOneLower, mul_assoc]

private theorem right_type_one_weight_mass {n : ℕ} (hn : 0 < n) (f : ArithmeticFunction ℝ)
    {T E : ℝ} (hE : 0 ≤ E) (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (factorBound : ∀ s ≤ n, ‖(f s : ℂ)‖ ≤ E)
    (u : ℕ) (hu : u ∈ Icc 1 (maximumStep n)) :
    (∑ i ∈ (rightTypeOneItems n).filter (fun i => rightTypeOneStep i = u), ‖rightTypeOneWeight f i‖) ≤
      T ^ 2 * E := by
  let chosen := (rightTypeOneItems n).filter (fun i => rightTypeOneStep i = u)
  have uPos : 0 < u := (mem_Icc.mp hu).1
  have uBound : u ≤ n := (mem_Icc.mp hu).2.trans (cutoffs_ordered n hn).2.2.2
  have count : chosen.card ≤ (u.divisors ×ˢ u.divisors).card := by
    apply card_le_card_of_injOn (fun i : RightTypeOneIndex => (i.1, i.2.2))
    · intro i hi
      have hi' : i ∈ chosen := hi
      have eq : i.1 * i.2.1 * i.2.2 = u := (mem_filter.mp hi').2
      refine mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨?_, uPos.ne'⟩, Nat.mem_divisors.mpr ⟨?_, uPos.ne'⟩⟩
      · exact ⟨i.2.1 * i.2.2, eq.symm.trans (Nat.mul_assoc _ _ _)⟩
      · exact ⟨i.1 * i.2.1, eq.symm.trans (Nat.mul_comm (i.1*i.2.1) i.2.2)⟩
    · intro x hx y hy equal
      have hx' : x ∈ chosen := hx
      have hy' : y ∈ chosen := hy
      have eq := (mem_filter.mp hx').2.trans (mem_filter.mp hy').2.symm
      have ⟨dx, _, sx⟩ := right_type_one_members (mem_filter.mp hx').1
      rcases x with ⟨d, k, s⟩
      rcases y with ⟨e, j, q⟩
      change (d,s) = (e,q) at equal
      injection equal with hd hs
      subst e
      subst q
      change d*k*s = d*j*s at eq
      have hk : k = j := Nat.eq_of_mul_eq_mul_left (mem_Icc.mp dx).1
        (Nat.eq_of_mul_eq_mul_right (mem_Icc.mp sx).1 eq)
      subst j
      rfl
  have countReal : (chosen.card : ℝ) ≤ T^2 := by
    calc
      _ ≤ ((u.divisors ×ˢ u.divisors).card : ℝ) := by exact_mod_cast count
      _ = (u.divisors.card : ℝ)^2 := by simp [card_product, pow_two]
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) (divisorBound u uBound) _
  have Swithin : rightVaughanFactorCap n ≤ n :=
    Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num))
  calc
    _ ≤ ∑ _ ∈ chosen, E := by
      refine sum_le_sum fun i hi => ?_
      have sBound := (mem_Icc.mp (right_type_one_members (mem_filter.mp hi).1).2.2).2.trans Swithin
      rw [rightTypeOneWeight, norm_mul, norm_neg]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (by simpa [moebiusComplex] using norm_moebiusComplex_le_one i.1)).trans (factorBound _ sBound)
    _ = (chosen.card : ℝ) * E := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right countReal hE

theorem norm_right_zeta_pair_le {n : ℕ} (nLower : 2 ≤ n) (width : 4 * cutoffH n * maximumStep n ≤ n)
    (steps : ∀ d ∈ Icc 1 (cutoffU n), ∀ k ∈ shortRightBandIndices n (rightLargeCofactorCut n) d,
      ∀ s ∈ Icc 1 (rightVaughanFactorCap n), 0 < d*k*s ∧ d*k*s ≤ maximumStep n)
    (f : ArithmeticFunction ℝ) (short : ∀ s, rightVaughanFactorCap n < s → f s = 0)
    {T : ℝ} (T1 : 1 ≤ T) (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (factorBound : ∀ s ≤ n, ‖(f s : ℂ)‖ ≤ T * logBudget n) :
    ‖rightLargeIntegral n (fun b => ((f * (ζ : ArithmeticFunction ℝ)) : ArithmeticFunction ℝ) b)‖ ≤
      totalConstant * finalScale n (T^3) := by
  have hn : 0 < n := by omega
  let W : ShortSuffixWaves n RightTypeOneIndex :=
    { items := rightTypeOneItems n
      step := rightTypeOneStep
      lower := rightTypeOneLower n
      weight := rightTypeOneWeight f
      step_range := fun i hi =>
        let ⟨hd, hk, hs⟩ := right_type_one_members hi
        steps i.1 hd i.2.1 hk i.2.2 hs }
  have weights : W.WeightBound (T^3 * logBudget n) := by
    intro u hu
    exact (right_type_one_weight_mass hn f (show 0 ≤ T * logBudget n by
      exact mul_nonneg (zero_le_one.trans T1) (zero_le_one.trans (one_le_logBudget n)))
      divisorBound factorBound u hu).trans_eq (by ring)
  have eq : rightLargeIntegral n (fun b => ((f * (ζ : ArithmeticFunction ℝ)) : ArithmeticFunction ℝ) b) =
      W.deepIntegral := by
    unfold rightLargeIntegral mixedIntegral ShortSuffixWaves.deepIntegral
    apply congrArg (secondPolynomialIntegral n)
    funext t
    exact right_zeta_series hn f short t
  rw [eq]
  exact W.norm_deepIntegral_le nLower width (one_le_pow₀ T1)
    (fun m hm => (divisorBound m hm).trans (by simpa using pow_le_pow_right₀ T1 (by decide : 1 ≤ 3)))
    weights

theorem norm_right_log_pair_le {n : ℕ} (nLower : 2 ≤ n) (width : 4 * cutoffH n * maximumStep n ≤ n)
    (steps : ∀ d ∈ Icc 1 (cutoffU n), ∀ k ∈ shortRightBandIndices n (rightLargeCofactorCut n) d,
      ∀ s ∈ Icc 1 (rightVaughanFactorCap n), 0 < d*k*s ∧ d*k*s ≤ maximumStep n)
    (f : ArithmeticFunction ℝ) (short : ∀ s, rightVaughanFactorCap n < s → f s = 0)
    {T : ℝ} (T1 : 1 ≤ T) (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (factorBound : ∀ s ≤ n, ‖(f s : ℂ)‖ ≤ 1) :
    ‖rightLargeIntegral n (fun b => ((f * ArithmeticFunction.log) : ArithmeticFunction ℝ) b)‖ ≤
      totalConstant * finalScale n (T^3) := by
  have hn : 0 < n := by omega
  let step := rightTypeOneStep
  let l := rightTypeOneLower n
  let r (i : RightTypeOneIndex) := n / step i
  let windows (i : RightTypeOneIndex) := Ico (l i) (r i)
  let W : ShortSuffixWaves n (Σ _ : RightTypeOneIndex, ℕ) :=
    { items := (rightTypeOneItems n).sigma windows
      step := fun x => step x.1
      lower := fun x => x.2
      weight := fun x => rightTypeOneWeight f x.1 * (suffixLogIncrement (l x.1) x.2 : ℂ)
      step_range := fun i hi =>
        let ⟨hd, hk, hs⟩ := right_type_one_members (mem_sigma.mp hi).1
        steps i.1.1 hd i.1.2.1 hk i.1.2.2 hs }
  have mass (i : RightTypeOneIndex) :
      (∑ j ∈ windows i, ‖(suffixLogIncrement (l i) j : ℂ)‖) ≤ logBudget n := by
    refine (log_wave_suffix_weights_le (l i) (r i)).trans ?_
    by_cases zero : r i = 0
    · simpa [zero] using (zero_le_one.trans (one_le_logBudget n))
    · exact log_le_logBudget (Nat.pos_of_ne_zero zero) (Nat.div_le_self n (step i))
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have weights : W.WeightBound (T^3 * logBudget n) := by
    intro u hu
    change (∑ x ∈ ((rightTypeOneItems n).sigma windows).filter (fun x => step x.1 = u),
      ‖rightTypeOneWeight f x.1 * (suffixLogIncrement (l x.1) x.2 : ℂ)‖) ≤ _
    rw [Finset.filter_sigma, Finset.sum_sigma]
    calc
      _ ≤ ∑ i ∈ rightTypeOneItems n, if step i = u then ‖rightTypeOneWeight f i‖ * logBudget n else 0 := by
        refine sum_le_sum fun i _ => ?_
        by_cases equal : step i = u
        · simpa only [equal, Finset.filter_true, if_true, norm_mul, ← Finset.mul_sum] using
            mul_le_mul_of_nonneg_left (mass i) (norm_nonneg (rightTypeOneWeight f i))
        · simp [equal]
      _ = (∑ i ∈ (rightTypeOneItems n).filter (fun i => step i = u), ‖rightTypeOneWeight f i‖) *
          logBudget n := by
        rw [Finset.sum_filter, Finset.sum_mul]
        refine sum_congr rfl fun i _ => ?_
        by_cases equal : step i = u <;> simp [equal]
      _ ≤ T^2 * logBudget n := mul_le_mul_of_nonneg_right
        (by simpa only [mul_one] using right_type_one_weight_mass hn f zero_le_one divisorBound factorBound u hu) L0
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ T1 (by decide)) L0
  have expansion (t : ℝ) :
      (∑ i ∈ rightTypeOneItems n, rightTypeOneWeight f i * logarithmicWave (step i) (l i) (r i) t) =
        W.polynomial t := by
    change _ = ∑ x ∈ (rightTypeOneItems n).sigma windows, (rightTypeOneWeight f x.1 *
      (suffixLogIncrement (l x.1) x.2 : ℂ)) * wave (step x.1) x.2 (r x.1) t
    rw [Finset.sum_sigma]
    refine sum_congr rfl fun i _ => ?_
    unfold logarithmicWave
    rw [log_wave_eq_weighted_suffixes, Finset.mul_sum]
    exact sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
  have eq : rightLargeIntegral n (fun b => ((f * ArithmeticFunction.log) : ArithmeticFunction ℝ) b) =
      W.deepIntegral := by
    unfold rightLargeIntegral mixedIntegral ShortSuffixWaves.deepIntegral
    apply congrArg (secondPolynomialIntegral n)
    funext t
    exact (right_log_series hn f short t).trans (expansion t)
  rw [eq]
  exact W.norm_deepIntegral_le nLower width (one_le_pow₀ T1)
    (fun m hm => (divisorBound m hm).trans (by simpa using pow_le_pow_right₀ T1 (by decide : 1 ≤ 3)))
    weights

end

end B13NondividingResidueReductionProof

end

/- Vaughan zeta -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail
open DyadicMixedB4MoebiusGauss DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def vaughanShortCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 96 : ℝ)⌋₊

def vaughanZetaFactor (n : ℕ) : ArithmeticFunction ℝ :=
  truncateArithmetic (μ : ArithmeticFunction ℝ) (vaughanShortCut n) *
    truncateArithmetic vonMangoldt (vaughanShortCut n)

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

theorem vaughan_zeta_factor_short {n : ℕ} (hn : 0 < n) :
    ∀ s, leftTypeOneFactorCap n < s → vaughanZetaFactor n s = 0 := by
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  let P := vaughanShortCut n
  have up : (P : ℝ) ≤ (n : ℝ) ^ (1 / 96 : ℝ) := Nat.floor_le (by positivity)
  have pBound : P * P ≤ leftTypeOneFactorCap n := by
    apply Nat.le_floor
    push_cast
    calc
      _ ≤ (n : ℝ) ^ (1 / 96 : ℝ) * (n : ℝ) ^ (1 / 96 : ℝ) :=
        mul_le_mul up up (Nat.cast_nonneg _) (by positivity)
      _ = (n : ℝ) ^ (1 / 48 : ℝ) := by rw [← Real.rpow_add nr]; norm_num
  exact truncate_moebius_mangoldt_support pBound

private theorem norm_vonMangoldt_le_budget {n j : ℕ} (h : j ≤ n) :
    ‖(vonMangoldt j : ℂ)‖ ≤ logBudget n := by
  by_cases zero : j = 0
  · simp [zero, zero_le_one.trans (one_le_logBudget n)]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact vonMangoldt_le_log.trans (log_le_logBudget (Nat.pos_of_ne_zero zero) h)

theorem norm_truncatedMoebiusMangoldt_le (P : ℕ) {n s : ℕ} (hs : s ≤ n) {D : ℝ}
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ D) :
    ‖(((truncateArithmetic (μ : ArithmeticFunction ℝ) P * truncateArithmetic vonMangoldt P :
      ArithmeticFunction ℝ) s) : ℂ)‖ ≤ D * logBudget n := by
  let f := truncateArithmetic (μ : ArithmeticFunction ℝ) P
  let g := truncateArithmetic vonMangoldt P
  change ‖((f * g) s : ℂ)‖ ≤ D * logBudget n
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    Complex.ofReal_sum]
  calc
    _ ≤ ∑ a ∈ s.divisors, ‖((f a * g (s / a) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ s.divisors, logBudget n := by
      refine sum_le_sum fun a _ => ?_
      have fMass : ‖(f a : ℂ)‖ ≤ 1 := by
        by_cases short : a ≤ P
        · simpa [f, truncateArithmetic, short, moebiusComplex] using norm_moebiusComplex_le_one a
        · simp [f, truncateArithmetic, short]
      have gMass : ‖(g (s / a) : ℂ)‖ ≤ logBudget n := by
        by_cases short : s / a ≤ P
        · simpa [g, truncateArithmetic, short] using norm_vonMangoldt_le_budget ((Nat.div_le_self s a).trans hs)
        · simp [g, truncateArithmetic, short, zero_le_one.trans (one_le_logBudget n)]
      rw [Complex.ofReal_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) fMass).trans gMass
    _ = (s.divisors.card : ℝ) * logBudget n := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (divisorBound s hs) (zero_le_one.trans (one_le_logBudget n))

end

end B13NondividingResidueReductionProof

end

/- Right type one saving -/
section

namespace B13NondividingResidueReductionProof

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

def rightVaughanLogWeight (n b : ℕ) : ℝ :=
  ((rightVaughanMoebius n * ArithmeticFunction.log) : ArithmeticFunction ℝ) b

def rightVaughanZetaWeight (n b : ℕ) : ℝ :=
  ((rightVaughanMoebius n * rightVaughanMangoldt n * (ζ : ArithmeticFunction ℝ)) : ArithmeticFunction ℝ) b

private theorem right_vaughan_moebius_short {n : ℕ} (hn : 0 < n) :
    ∀ s, rightVaughanFactorCap n < s → rightVaughanMoebius n s = 0 := by
  have cutoff : rightVaughanCut n ≤ rightVaughanFactorCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
  intro s hs
  simp [rightVaughanMoebius, truncateArithmetic, not_le_of_gt (cutoff.trans_lt hs)]

private theorem norm_right_vaughan_moebius_le (n s : ℕ) :
    ‖(rightVaughanMoebius n s : ℂ)‖ ≤ 1 := by
  by_cases short : s ≤ rightVaughanCut n
  · simpa [rightVaughanMoebius, truncateArithmetic, short, moebiusComplex] using norm_moebiusComplex_le_one s
  · simp [rightVaughanMoebius, truncateArithmetic, short]

private theorem divisor_envelope_for_right (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
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

private theorem eventually_log_budget_le_for_right (p : ℝ) (hp : 0 < p) :
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

private theorem right_finalScale_eventually (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∃ T : ℝ, 1 ≤ T ∧ (∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) ∧
      totalConstant * finalScale n (T^3) ≤ e * (n : ℝ) := by
  obtain ⟨D, D1, divBound⟩ := divisor_envelope_for_right 8192 (by decide)
  let C := totalConstant * D ^ 15
  have limit : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(5 / 4096) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 4096)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(5 / 4096) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le_for_right (1/8192) (by norm_num),
    scaled.eventually_lt_const he] with n hn logSmall small
  let X := (n : ℝ) ^ (1 / 8192 : ℝ)
  let T := D * X
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have nr : (0 : ℝ) < n := zero_lt_one.trans_le nOne
  have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1 (Real.one_le_rpow nOne (by norm_num))
  refine ⟨T,T1,divBound n,?_⟩
  have eq : X ^ 22 * (n : ℝ) ^ (255 / 256 : ℝ) =
      (n : ℝ) ^ (-(5 / 4096) : ℝ) * (n : ℝ) := by
    unfold X
    rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le, ← Real.rpow_add nr]
    calc
      _ = (n : ℝ) ^ (-(5 / 4096) + 1 : ℝ) := by congr 1; norm_num
      _ = (n : ℝ) ^ (-(5 / 4096) : ℝ) * (n : ℝ) ^ (1 : ℝ) := Real.rpow_add nr _ _
      _ = _ := by rw [Real.rpow_one]
  calc
    _ ≤ totalConstant * ((T^3)^5 * X^7 * (n : ℝ) ^ (255 / 256 : ℝ)) := by
      unfold finalScale
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (one_le_logBudget n)) logSmall 7) (by positivity))
        (by positivity)) totalConstant_nonnegative
    _ = C * (X ^ 22 * (n : ℝ) ^ (255 / 256 : ℝ)) := by unfold C T; ring
    _ = (C * (n : ℝ) ^ (-(5 / 4096) : ℝ)) * (n : ℝ) := by rw [eq]; unfold C; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le

theorem rightVaughan_type_one_saving :
    saving (fun n => rightLargeIntegral n (rightVaughanLogWeight n)) ∧
    saving (fun n => rightLargeIntegral n (rightVaughanZetaWeight n)) := by
  have estimates (e : ℝ) (he : 0 < e) : ∀ᶠ n : ℕ in atTop,
      ‖rightLargeIntegral n (rightVaughanLogWeight n)‖ ≤ e * (n : ℝ) ∧
      ‖rightLargeIntegral n (rightVaughanZetaWeight n)‖ ≤ e * (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, eventually_small_width,
      right_short_step_eventually, right_finalScale_eventually e he]
      with n nLower width steps envelope
    obtain ⟨T,T1,divisorBound,scale⟩ := envelope
    have hn : 0 < n := by omega
    have estimateLog := norm_right_log_pair_le nLower width steps (rightVaughanMoebius n)
      (right_vaughan_moebius_short hn) T1 divisorBound (fun s _ => norm_right_vaughan_moebius_le n s)
    have estimateZeta := norm_right_zeta_pair_le nLower width steps
      (rightVaughanMoebius n * rightVaughanMangoldt n)
      (truncate_moebius_mangoldt_support (right_cap_product hn)) T1 divisorBound
      (fun _ hs => norm_truncatedMoebiusMangoldt_le (rightVaughanCut n) hs divisorBound)
    exact ⟨estimateLog.trans scale, estimateZeta.trans scale⟩
  constructor <;> intro e he <;>
    obtain ⟨N, h⟩ := eventually_atTop.mp (estimates e he)
  · exact ⟨N, fun n hn _ => (h n hn).1⟩
  · exact ⟨N, fun n hn _ => (h n hn).2⟩

end

end B13NondividingResidueReductionProof

end

/- Right vaughan bridge -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Scale DyadicMixedB4Arithmetic DyadicMixedB4ArcDecomposition
open DyadicMixedB4Geometric DyadicMixedB4PairIntegral DyadicMixedB4ArcGeometry
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def rightVaughanBilinearWeight (n b : ℕ) : ℝ :=
  (((μ : ArithmeticFunction ℝ) - rightVaughanMoebius n) *
    (vonMangoldt - rightVaughanMangoldt n) * (ζ : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) b

def rightResidualWeight (n b : ℕ) : ℝ :=
  if rightLargeCofactorCut n < b then rightVaughanBilinearWeight n b else vonMangoldt b

def rightVaughanRemainder (n : ℕ) : ℂ :=
  mixedIntegral n (bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n))

private theorem vonMangoldt_eq_right_residual {n : ℕ} (hn : 0 < n) (b : ℕ) :
    vonMangoldt b = rightResidualWeight n b +
      restrictLargeRight n (rightVaughanLogWeight n) b - restrictLargeRight n (rightVaughanZetaWeight n) b := by
  by_cases high : rightLargeCofactorCut n < b
  · have cutoff : rightVaughanCut n ≤ rightLargeCofactorCut n :=
      Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
    have zero : rightVaughanMangoldt n b = 0 := by
      simp [rightVaughanMangoldt, truncateArithmetic, not_le_of_gt (cutoff.trans_lt high)]
    have identity :
        rightVaughanLogWeight n b - rightVaughanZetaWeight n b + rightVaughanMangoldt n b +
          rightVaughanBilinearWeight n b = vonMangoldt b :=
      congrArg (fun f : ArithmeticFunction ℝ => f b) (vaughan_identity_real (rightVaughanCut n) (rightVaughanCut n))
    simp only [rightResidualWeight, restrictLargeRight, high, ite_true]
    rw [zero] at identity
    linarith only [identity]
  · simp [rightResidualWeight, restrictLargeRight, high]

private theorem right_large_band_eq {n m : ℕ} (hn : 0 < n) (hm : m ≤ n) (w : ℕ → ℝ) :
    bandCoefficient n (cutoffB n) (upperCut n) (restrictLargeRight n w) m =
      bandCoefficient n (cutoffB n) (splitCut n) (restrictLargeRight n w) m := by
  simp only [bandCoefficient, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : a ≤ splitCut n
  · simp [ha, ha.trans (cuts_ordered n hn).2.2]
  · have cofactor := cofactor_of_high_divisor hn (lt_of_not_ge ha : splitCut n < a)
      ((Nat.mul_div_le m a).trans hm)
    have cutoff : ⌊(n : ℝ) ^ (5 / 12 : ℝ)⌋₊ ≤ rightLargeCofactorCut n :=
      Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
    simp [ha, restrictLargeRight, not_lt_of_ge (cofactor.trans cutoff)]

private theorem rightVaughan_split_coeff {n m : ℕ} (hn : 0 < n) (hm : m ≤ n) :
    bandCoefficient n (cutoffB n) (upperCut n) vonMangoldt m =
      bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n) m +
        bandCoefficient n (cutoffB n) (splitCut n) (restrictLargeRight n (rightVaughanLogWeight n)) m -
        bandCoefficient n (cutoffB n) (splitCut n) (restrictLargeRight n (rightVaughanZetaWeight n)) m := by
  rw [← right_large_band_eq hn hm, ← right_large_band_eq hn hm]
  simp only [bandCoefficient, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← mul_add, ← mul_sub, ← vonMangoldt_eq_right_residual hn]

theorem original_eq_right_vaughan {n : ℕ} (hn : 0 < n) :
    mixedIntegral n (bandCoefficient n (cutoffB n) (upperCut n) vonMangoldt) =
      rightVaughanRemainder n + rightLargeIntegral n (rightVaughanLogWeight n) -
        rightLargeIntegral n (rightVaughanZetaWeight n) := by
  let original := bandCoefficient n (cutoffB n) (upperCut n) vonMangoldt
  let residual := bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n)
  let wlog := bandCoefficient n (cutoffB n) (splitCut n) (restrictLargeRight n (rightVaughanLogWeight n))
  let wzeta := bandCoefficient n (cutoffB n) (splitCut n) (restrictLargeRight n (rightVaughanZetaWeight n))
  let s := (wide n (cutoffB n) (cutoffH n))ᶜ
  let C (w : ℕ → ℝ) := plainPolynomial n (fun m => (w m : ℂ))
  let integrand (w : ℕ → ℝ) := s.indicator (fun t => plainPolynomial n (lowCoefficients n) t *
    C w t * phase (-(n : ℝ) * t))
  have integrable (w : ℕ → ℝ) : IntervalIntegrable (integrand w) volume 0 1 := by
    apply indicator_intervalIntegrable _ (wide_measurable ..).compl
    unfold C plainPolynomial phase
    fun_prop
  change (∫ t in (0 : ℝ)..1, integrand original t) =
      (∫ t in (0 : ℝ)..1, integrand residual t) + (∫ t in (0 : ℝ)..1, integrand wlog t) -
        (∫ t in (0 : ℝ)..1, integrand wzeta t)
  rw [← intervalIntegral.integral_add (integrable residual) (integrable wlog),
    ← intervalIntegral.integral_sub ((integrable residual).add (integrable wlog)) (integrable wzeta)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have poly : C original t = C residual t + C wlog t - C wzeta t := by
    unfold C plainPolynomial
    rw [← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun m hm => ?_
    have eq : original m = residual m + wlog m - wzeta m :=
      rightVaughan_split_coeff hn (Nat.le_of_lt_succ (mem_range.mp hm))
    dsimp only
    rw [eq, Complex.ofReal_sub, Complex.ofReal_add, sub_mul, add_mul]
  by_cases ht : t ∈ s
  · simp only [integrand, Set.indicator_of_mem ht, poly]
    ring
  · simp [integrand, ht]

theorem frozen_iff_right_vaughan : frozenGoal ↔ saving rightVaughanRemainder := by
  change saving (fun n => mixedIntegral n (bandCoefficient n (cutoffB n) (upperCut n) vonMangoldt)) ↔ _
  have subAdd (a b c : ℂ) : ‖a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le (a - b) c).trans (add_le_add (norm_sub_le a b) le_rfl)
  have addSub (a b c : ℂ) : ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_sub_le (a + b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  constructor <;> intro initial e he <;>
    obtain ⟨N, left⟩ := initial (e / 3) (by positivity) <;>
    obtain ⟨L, logBound⟩ := rightVaughan_type_one_saving.1 (e / 3) (by positivity) <;>
    obtain ⟨Z, zetaBound⟩ := rightVaughan_type_one_saving.2 (e / 3) (by positivity) <;>
    refine ⟨max 1 (max N (max L Z)), fun n hn nEven => ?_⟩ <;>
    have nPos : 0 < n := by omega
  · have same : rightVaughanRemainder n =
      mixedIntegral n (bandCoefficient n (cutoffB n) (upperCut n) vonMangoldt) -
        rightLargeIntegral n (rightVaughanLogWeight n) + rightLargeIntegral n (rightVaughanZetaWeight n) := by
      rw [original_eq_right_vaughan nPos]
      abel
    rw [same]
    refine (subAdd (mixedIntegral n (bandCoefficient n (cutoffB n) (upperCut n) vonMangoldt))
      (rightLargeIntegral n (rightVaughanLogWeight n)) (rightLargeIntegral n (rightVaughanZetaWeight n))).trans ?_
    linarith only [left n (by omega) nEven, logBound n (by omega) nEven, zetaBound n (by omega) nEven]
  · change ‖mixedIntegral n (bandCoefficient n (cutoffB n) (upperCut n) vonMangoldt)‖ ≤ _
    rw [original_eq_right_vaughan nPos]
    refine (addSub (rightVaughanRemainder n)
      (rightLargeIntegral n (rightVaughanLogWeight n)) (rightLargeIntegral n (rightVaughanZetaWeight n))).trans ?_
    linarith only [left n (by omega) nEven, logBound n (by omega) nEven, zetaBound n (by omega) nEven]

end

end B13NondividingResidueReductionProof

end

/- Vaughan bridge -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Scale DyadicMixedB4Geometric DyadicMixedB4ArcGeometry
open DyadicMixedB4ArcDecomposition DyadicMixedB4PairIntegral
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def vaughanZetaWeight (n y : ℕ) : ℝ :=
  ((vaughanZetaFactor n * (ζ : ArithmeticFunction ℝ)) : ArithmeticFunction ℝ) y

def vaughanSurvivingWeight (n y : ℕ) : ℝ :=
  let P := vaughanShortCut n
  let M := (μ : ArithmeticFunction ℝ)
  let f := truncateArithmetic M P
  let g := truncateArithmetic vonMangoldt P
  ((f * ArithmeticFunction.log : ArithmeticFunction ℝ) y) +
    (((M - f) * (vonMangoldt - g) * (ζ : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) y)

theorem vaughan_at_left_band_cofactor {n y : ℕ} (hn : 0 < n) (hy : cutoffU n < y) :
    vonMangoldt y = vaughanSurvivingWeight n y - vaughanZetaWeight n y := by
  let P := vaughanShortCut n
  let M := (μ : ArithmeticFunction ℝ)
  let f := truncateArithmetic M P
  let g := truncateArithmetic vonMangoldt P
  let Z := (ζ : ArithmeticFunction ℝ)
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have cutoff : P ≤ cutoffU n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nOne (by norm_num))
  have smallZero : g y = 0 := by
    change (if y ≤ P then vonMangoldt y else 0) = 0
    exact if_neg (not_le_of_gt (cutoff.trans_lt hy))
  have evaluated :
      (f * ArithmeticFunction.log : ArithmeticFunction ℝ) y -
        ((f * g) * Z : ArithmeticFunction ℝ) y + g y +
        ((M - f) * (vonMangoldt - g) * Z : ArithmeticFunction ℝ) y = vonMangoldt y :=
    congrArg (fun F : ArithmeticFunction ℝ => F y) (vaughan_identity_real P P)
  change vonMangoldt y =
    ((f * ArithmeticFunction.log : ArithmeticFunction ℝ) y +
      ((M - f) * (vonMangoldt - g) * Z : ArithmeticFunction ℝ) y) - ((f * g) * Z : ArithmeticFunction ℝ) y
  rw [smallZero] at evaluated
  linarith only [evaluated]

end

end B13NondividingResidueReductionProof

end

/- Vaughan log -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open DyadicMixedB4PairIntegral DyadicMixedB4MoebiusGauss
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition DyadicMixedB4EnergyTail
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

theorem norm_left_log_pair_le {n : ℕ} (hn : 0 < n) (f : ArithmeticFunction ℝ)
    (short : ∀ y, leftTypeOneFactorCap n < y → f y = 0)
    {T E : ℝ} (t0 : 0 ≤ T) (e0 : 0 ≤ E)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (factorBound : ∀ m ≤ n, ‖(f m : ℂ)‖ ≤ E)
    (A : ℕ → ℂ) {B : ℝ} (coefficients : ∀ m ≤ n, ‖A m‖ ≤ B) :
    ‖∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator (fun x =>
        shiftedPolynomial n A x *
          plainPolynomial n (fun m => (bandCoefficient n (cutoffU n) (lowCut n)
            (fun y => ((f * ArithmeticFunction.log) : ArithmeticFunction ℝ) y) m : ℂ)) x) t‖ ≤
      (n : ℝ) ^ (31 / 32 : ℝ) * (B ^ 2 + 320 * (T ^ 2 * E * (2 * logBudget n)) ^ 2 *
        logBudget n ^ 3) := by
  let base := Ioc (cutoffU n) (lowCut n) ×ˢ Icc 1 (leftTypeOneFactorCap n)
  let v (i : ℕ × ℕ) := i.1 * i.2
  let l (i : ℕ × ℕ) := cutoffU n / i.2
  let r (i : ℕ × ℕ) := n / v i
  let c (i : ℕ × ℕ) := (leftBandMoebius n i.1 : ℂ) * (f i.2 : ℂ)
  let prefixItems (i : ℕ × ℕ) := Ioc (l i) (r i)
  let items := base.sigma prefixItems
  let step (x : Σ _ : ℕ × ℕ, ℕ) := v x.1
  let start (x : Σ _ : ℕ × ℕ, ℕ) := l x.1
  let weight (x : Σ _ : ℕ × ℕ, ℕ) := c x.1 * (logWaveStep (r x.1) x.2 : ℂ)
  have expansion (t : ℝ) :
      plainPolynomial n (fun m => (bandCoefficient n (cutoffU n) (lowCut n)
        (fun y => ((f * ArithmeticFunction.log) : ArithmeticFunction ℝ) y) m : ℂ)) t =
        ∑ x ∈ items, weight x * wave (step x) (start x) x.2 t := by
    dsimp only [items]
    rw [left_band_short_log_polynomial_eq_waves n (leftTypeOneFactorCap n) hn f short, Finset.sum_sigma]
    refine sum_congr rfl fun i _ => ?_
    change c i * logarithmicWave (v i) (l i) (r i) t =
      ∑ j ∈ prefixItems i, (c i * (logWaveStep (r i) j : ℂ)) * wave (v i) (l i) j t
    rw [logarithmicWave_eq_prefixes, Finset.mul_sum]
    exact sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
  have L0 : 0 ≤ logBudget n := zero_le_one.trans (one_le_logBudget n)
  have mass (i : ℕ × ℕ) :
      (∑ j ∈ prefixItems i, ‖(logWaveStep (r i) j : ℂ)‖) ≤ 2 * logBudget n := by
    refine (log_wave_prefix_weights_le (l i) (r i)).trans ?_
    have hLog : Real.log (r i) ≤ logBudget n := by
      by_cases zero : r i = 0
      · simpa [zero] using L0
      · exact log_le_logBudget (Nat.pos_of_ne_zero zero) (Nat.div_le_self n (v i))
    exact mul_le_mul_of_nonneg_left hLog (by norm_num)
  have weights (u : ℕ) (hu : u ∈ Icc 1 (leftTypeOneCap n)) :
      (∑ x ∈ items.filter (fun x => step x = u), ‖weight x‖) ≤ T ^ 2 * E * (2 * logBudget n) := by
    dsimp only [items]
    rw [Finset.filter_sigma, Finset.sum_sigma]
    change (∑ i ∈ base, ∑ j ∈ (prefixItems i).filter (fun _ => v i = u),
      ‖c i * (logWaveStep (r i) j : ℂ)‖) ≤ _
    calc
      _ ≤ ∑ i ∈ base, if v i = u then ‖c i‖ * (2 * logBudget n) else 0 := by
        refine sum_le_sum fun i _ => ?_
        by_cases equal : v i = u
        · simpa only [equal, Finset.filter_true, if_true, norm_mul, ← Finset.mul_sum] using
            mul_le_mul_of_nonneg_left (mass i) (norm_nonneg (c i))
        · simp [equal]
      _ = (∑ i ∈ base.filter (fun i => v i = u), ‖c i‖) * (2 * logBudget n) := by
        rw [Finset.sum_filter, Finset.sum_mul]
        refine sum_congr rfl fun i _ => ?_
        by_cases equal : v i = u <;> simp [equal]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (norm_left_short_weights hn f t0 e0 divisorBound factorBound u hu) (by positivity)
  simp_rw [expansion]
  exact shortLeftWavePair_bound items hn (by positivity) step start (fun x => x.2) weight
    (fun x hx => left_short_wave_step hn (Finset.mem_sigma.mp hx).1)
    (fun x hx => (Finset.mem_Ioc.mp (Finset.mem_sigma.mp hx).2).2)
    weights A coefficients

def vaughanLogFactor (n : ℕ) : ArithmeticFunction ℝ :=
  truncateArithmetic (μ : ArithmeticFunction ℝ) (vaughanShortCut n)

def vaughanLogWeight (n y : ℕ) : ℝ :=
  ((vaughanLogFactor n * ArithmeticFunction.log) : ArithmeticFunction ℝ) y

theorem vaughan_log_factor_short {n : ℕ} (hn : 0 < n) :
    ∀ s, leftTypeOneFactorCap n < s → vaughanLogFactor n s = 0 := by
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have cutoff : vaughanShortCut n ≤ leftTypeOneFactorCap n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le nOne (by norm_num))
  intro s hs
  simp [vaughanLogFactor, truncateArithmetic, not_le_of_gt (cutoff.trans_lt hs)]

theorem norm_vaughan_log_factor_le (n s : ℕ) :
    ‖(vaughanLogFactor n s : ℂ)‖ ≤ 1 := by
  by_cases short : s ≤ vaughanShortCut n
  · simpa [vaughanLogFactor, truncateArithmetic, short, moebiusComplex] using norm_moebiusComplex_le_one s
  · simp [vaughanLogFactor, truncateArithmetic, short]

end

end B13NondividingResidueReductionProof

end

/- Bilinear bridge -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Scale DyadicMixedB4Geometric DyadicMixedB4ArcGeometry
open DyadicMixedB4ArcDecomposition DyadicMixedB4PairIntegral
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def vaughanBilinearWeight (n y : ℕ) : ℝ :=
  let P := vaughanShortCut n
  let M := (μ : ArithmeticFunction ℝ)
  ((M - truncateArithmetic M P) * (vonMangoldt - truncateArithmetic vonMangoldt P) *
    (ζ : ArithmeticFunction ℝ) : ArithmeticFunction ℝ) y

end

end B13NondividingResidueReductionProof

end

/- Bilateral short -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4PairIntegral
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4MoebiusGauss
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def bilateralVaughanPair (n : ℕ) (left right : ℕ → ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator (fun x =>
    shiftedPolynomial n (fun m => (bandCoefficient n (cutoffB n) (upperCut n) right m : ℂ)) x *
    plainPolynomial n (fun m => (bandCoefficient n (cutoffU n) (lowCut n) left m : ℂ)) x) t

private theorem norm_real_mangoldt_le {n m : ℕ} (hm : m ≤ n) :
    ‖(vonMangoldt m : ℂ)‖ ≤ logBudget n := by
  by_cases zero : m = 0
  · simp [zero, zero_le_one.trans (one_le_logBudget n)]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact vonMangoldt_le_log.trans (log_le_logBudget (Nat.pos_of_ne_zero zero) hm)

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

private theorem norm_right_residual_weight {n m : ℕ} (hm : m ≤ n)
    {T : ℝ} (T1 : 1 ≤ T) (divisorBound : ∀ x ≤ n, (x.divisors.card : ℝ) ≤ T) :
    ‖(rightResidualWeight n m : ℂ)‖ ≤ T ^ 2 * logBudget n := by
  have L0 := zero_le_one.trans (one_le_logBudget n)
  by_cases high : rightLargeCofactorCut n < m
  · let f := (μ : ArithmeticFunction ℝ) - rightVaughanMoebius n
    let g := vonMangoldt - rightVaughanMangoldt n
    have fBound : ∀ x ≤ n, ‖(f x : ℂ)‖ ≤ 1 := by
      intro x _
      change ‖(((μ x : ℝ) - (if x ≤ rightVaughanCut n then (μ x : ℝ) else 0) : ℝ) : ℂ)‖ ≤ 1
      by_cases short : x ≤ rightVaughanCut n
      · simp [short]
      · simpa [short, moebiusComplex] using norm_moebiusComplex_le_one x
    have gBound : ∀ x ≤ n, ‖(g x : ℂ)‖ ≤ logBudget n := by
      intro x hx
      change ‖((vonMangoldt x - (if x ≤ rightVaughanCut n then vonMangoldt x else 0) : ℝ) : ℂ)‖ ≤ logBudget n
      by_cases short : x ≤ rightVaughanCut n
      · simp [short, L0]
      · simpa [short] using norm_real_mangoldt_le hx
    have ζBound : ∀ x ≤ n, ‖(((ζ : ArithmeticFunction ℝ) x : ℝ) : ℂ)‖ ≤ 1 := by
      intro x _
      by_cases zero : x = 0
      · simp [zero]
      · simp [zeta_apply_ne zero]
    have first : ∀ x ≤ n, ‖((f*g) x : ℂ)‖ ≤ T * logBudget n := by
      intro x hx
      simpa only [one_mul] using norm_convolution_apply_le hx f g zero_le_one L0
        (divisorBound x hx) fBound gBound
    have est := norm_convolution_apply_le hm (f*g) (ζ : ArithmeticFunction ℝ)
      (mul_nonneg (zero_le_one.trans T1) L0) zero_le_one (divisorBound m hm) first ζBound
    simp only [rightResidualWeight, high, ite_true, rightVaughanBilinearWeight]
    refine est.trans_eq ?_
    ring
  · simp only [rightResidualWeight, high, ite_false]
    exact (norm_real_mangoldt_le hm).trans (le_mul_of_one_le_left L0 (one_le_pow₀ T1))

theorem norm_right_residual_coefficient {n m : ℕ} (hm : m ≤ n)
    {T : ℝ} (T1 : 1 ≤ T) (divisorBound : ∀ x ≤ n, (x.divisors.card : ℝ) ≤ T) :
    ‖(bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n) m : ℂ)‖ ≤ T ^ 4 * logBudget n := by
  have T0 := zero_le_one.trans T1
  have L0 := zero_le_one.trans (one_le_logBudget n)
  unfold bandCoefficient
  rw [Complex.ofReal_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ m.divisors.filter (fun a => cutoffB n < a ∧ a ≤ upperCut n ∧ cutoffU n < m / a),
        T * (T^2 * logBudget n) := by
      refine sum_le_sum fun a ha => ?_
      have hd := (mem_filter.mp ha).1
      have aBound := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.dvd_of_mem_divisors hd)
      rw [Complex.ofReal_mul, norm_mul]
      exact mul_le_mul ((norm_leftBandMoebius_le n a).trans (divisorBound a (aBound.trans hm)))
        (norm_right_residual_weight ((Nat.div_le_self m a).trans hm) T1 divisorBound) (norm_nonneg _) T0
    _ ≤ ∑ _ ∈ m.divisors, T * (T^2 * logBudget n) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (m.divisors.card : ℝ) * (T * (T^2 * logBudget n)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ T * (T * (T^2 * logBudget n)) :=
      mul_le_mul_of_nonneg_right (divisorBound m hm) (by positivity)
    _ = _ := by ring

theorem bilateral_left_type_one_saving :
    saving (fun n => bilateralVaughanPair n (vaughanLogWeight n) (rightResidualWeight n)) ∧
    saving (fun n => bilateralVaughanPair n (vaughanZetaWeight n) (rightResidualWeight n)) := by
  have estimates (e : ℝ) (he : 0 < e) : ∀ᶠ n : ℕ in atTop,
      ‖bilateralVaughanPair n (vaughanLogWeight n) (rightResidualWeight n)‖ ≤ e * (n : ℝ) ∧
      ‖bilateralVaughanPair n (vaughanZetaWeight n) (rightResidualWeight n)‖ ≤ e * (n : ℝ) := by
    obtain ⟨D, D1, divBound⟩ := divisor_envelope
    let C := 1281 * D^8
    have limit : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(19 / 1024) : ℝ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 19 / 1024)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have scaled : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(19 / 1024) : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul limit
    filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le, scaled.eventually_lt_const he]
      with n hn logBound small
    have nPos : 0 < n := by omega
    have nr : (0 : ℝ) < n := by exact_mod_cast nPos
    let X := (n : ℝ) ^ (1 / 1024 : ℝ)
    let T := D * X
    let L := logBudget n
    have T1 : 1 ≤ T :=
      one_le_mul_of_one_le_of_one_le D1 (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))
    have T0 := zero_le_one.trans T1
    have L1 : 1 ≤ L := one_le_logBudget n
    have L0 := zero_le_one.trans L1
    have nBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T := divBound n
    let R (m : ℕ) := (bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n) m : ℂ)
    have rBound : ∀ m ≤ n, ‖R m‖ ≤ T^4 * L := fun _ hm => norm_right_residual_coefficient hm T1 nBound
    have logEst := norm_left_log_pair_le nPos (vaughanLogFactor n) (vaughan_log_factor_short nPos)
      T0 zero_le_one nBound (fun m _ => norm_vaughan_log_factor_le n m) R rBound
    have zetaEst := norm_left_zeta_pair_le nPos (vaughanZetaFactor n) (vaughan_zeta_factor_short nPos)
      T0 (mul_nonneg T0 L0) nBound (fun _ hm => norm_truncatedMoebiusMangoldt_le (vaughanShortCut n) hm nBound)
      R rBound
    have main : 1281 * (n : ℝ) ^ (31 / 32 : ℝ) * T^8 * L^5 ≤ e * (n : ℝ) := by
      have exp : (n : ℝ) ^ (31 / 32 : ℝ) * X^13 =
          (n : ℝ) ^ (-(19 / 1024) : ℝ) * (n : ℝ) := by
        unfold X
        rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le, ← Real.rpow_add nr]
        calc
          _ = (n : ℝ) ^ (-(19 / 1024) + 1 : ℝ) := by congr 1; norm_num
          _ = (n : ℝ) ^ (-(19 / 1024) : ℝ) * (n : ℝ) ^ (1 : ℝ) := Real.rpow_add nr _ _
          _ = _ := by rw [Real.rpow_one]
      calc
        _ ≤ 1281 * (n : ℝ) ^ (31 / 32 : ℝ) * T^8 * X^5 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ L0 logBound 5) (by positivity)
        _ = C * ((n : ℝ) ^ (31 / 32 : ℝ) * X^13) := by unfold T C; ring
        _ = (C * (n : ℝ) ^ (-(19 / 1024) : ℝ)) * (n : ℝ) := by rw [exp]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
    have first : (T^4 * L)^2 ≤ T^8 * L^5 := by
      calc
        _ = T^8 * L^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ L1 (by decide)) (by positivity)
    have t4 : T^4 ≤ T^8 := pow_le_pow_right₀ T1 (by decide)
    have t6 : T^6 ≤ T^8 := pow_le_pow_right₀ T1 (by decide)
    refine ⟨logEst.trans ?_, zetaEst.trans ?_⟩
    · refine le_trans ?_ main
      change (n : ℝ) ^ (31 / 32 : ℝ) * ((T^4 * L)^2 + 320 * (T^2 * 1 * (2*L))^2 * L^3) ≤ _
      have hl : 320 * (T^2 * 1 * (2*L))^2 * L^3 ≤ 1280 * (T^8 * L^5) := by
        calc
          _ = (1280 * L^5) * T^4 := by ring
          _ ≤ (1280 * L^5) * T^8 := mul_le_mul_of_nonneg_left t4 (by positivity)
          _ = _ := by ring
      exact (mul_le_mul_of_nonneg_left (add_le_add first hl) (by positivity)).trans_eq (by ring)
    · refine le_trans ?_ main
      change (n : ℝ) ^ (31 / 32 : ℝ) * ((T^4 * L)^2 + 320 * (T^2 * (T*L))^2 * L^3) ≤ _
      have hz : 320 * (T^2 * (T*L))^2 * L^3 ≤ 1280 * (T^8 * L^5) := by
        calc
          _ = (320 * L^5) * T^6 := by ring
          _ ≤ (320 * L^5) * T^8 := mul_le_mul_of_nonneg_left t6 (by positivity)
          _ ≤ (1280 * L^5) * T^8 := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) (by positivity)
          _ = _ := by ring
      exact (mul_le_mul_of_nonneg_left (add_le_add first hz) (by positivity)).trans_eq (by ring)
  constructor <;> intro e he <;>
    obtain ⟨N, h⟩ := eventually_atTop.mp (estimates e he)
  · exact ⟨N, fun n hn _ => (h n hn).1⟩
  · exact ⟨N, fun n hn _ => (h n hn).2⟩

end

end B13NondividingResidueReductionProof

end

/- Bilateral vaughan bridge -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4PairIntegral
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open ArithmeticFunction
open scoped Classical

noncomputable section

def bilateralVaughanRemainder (n : ℕ) : ℂ :=
  bilateralVaughanPair n (vaughanBilinearWeight n) (rightResidualWeight n)

private theorem right_remainder_eq_pair (n : ℕ) :
    rightVaughanRemainder n = bilateralVaughanPair n vonMangoldt (rightResidualWeight n) := by
  unfold rightVaughanRemainder mixedIntegral secondPolynomialIntegral bilateralVaughanPair
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases inside : t ∈ (wide n (cutoffB n) (cutoffH n))ᶜ
  · simp only [Set.indicator_of_mem inside, shiftedPolynomial_eq]
    change _ = _ * plainPolynomial n (lowCoefficients n) t
    ring
  · simp [inside]

theorem right_remainder_eq_bilateral_vaughan {n : ℕ} (hn : 0 < n) :
    rightVaughanRemainder n = bilateralVaughanRemainder n +
      bilateralVaughanPair n (vaughanLogWeight n) (rightResidualWeight n) -
      bilateralVaughanPair n (vaughanZetaWeight n) (rightResidualWeight n) := by
  rw [right_remainder_eq_pair]
  let v := vaughanBilinearWeight n
  let l := vaughanLogWeight n
  let z := vaughanZetaWeight n
  let s := (wide n (cutoffB n) (cutoffH n))ᶜ
  let r := shiftedPolynomial n
    (fun m => (bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n) m : ℂ))
  let L (f : ℕ → ℝ) := plainPolynomial n (fun m => (bandCoefficient n (cutoffU n) (lowCut n) f m : ℂ))
  let J (f : ℕ → ℝ) := s.indicator (fun t => r t * L f t)
  have int (f : ℕ → ℝ) : IntervalIntegrable (J f) volume 0 1 := by
    have LCont : Continuous (L f) := by unfold L plainPolynomial phase; fun_prop
    exact indicator_intervalIntegrable ((shiftedPolynomial_continuous ..).mul LCont)
      (wide_measurable ..).compl
  have weights (m : ℕ) :
      bandCoefficient n (cutoffU n) (lowCut n) vonMangoldt m =
        bandCoefficient n (cutoffU n) (lowCut n) v m +
        bandCoefficient n (cutoffU n) (lowCut n) l m -
        bandCoefficient n (cutoffU n) (lowCut n) z m := by
    simp only [bandCoefficient, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a ha => ?_
    have eq := vaughan_at_left_band_cofactor hn (mem_filter.mp ha).2.2.2
    change vonMangoldt (m/a) = (l (m/a) + v (m/a)) - z (m/a) at eq
    rw [← mul_add, ← mul_sub, eq, add_comm (l (m/a))]
  change (∫ t in (0 : ℝ)..1, J vonMangoldt t) =
    (∫ t in (0 : ℝ)..1, J v t) + (∫ t in (0 : ℝ)..1, J l t) - (∫ t in (0 : ℝ)..1, J z t)
  rw [← intervalIntegral.integral_add (int v) (int l),
    ← intervalIntegral.integral_sub ((int v).add (int l)) (int z)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases inside : t ∈ s
  · have poly : L vonMangoldt t = L v t + L l t - L z t := by
      simp only [L, plainPolynomial, weights, Complex.ofReal_sub, Complex.ofReal_add,
        sub_mul, add_mul, sum_add_distrib, sum_sub_distrib]
    simp only [J, Set.indicator_of_mem inside, poly]
    ring
  · simp [J, inside]

theorem frozen_iff_bilateral_vaughan : frozenGoal ↔ saving bilateralVaughanRemainder := by
  rw [frozen_iff_right_vaughan]
  have subAdd (a b c : ℂ) : ‖a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le (a-b) c).trans (add_le_add (norm_sub_le a b) le_rfl)
  have addSub (a b c : ℂ) : ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_sub_le (a+b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  constructor <;> intro input e he <;>
    obtain ⟨N, h⟩ := input (e/3) (by positivity) <;>
    obtain ⟨L, hl⟩ := bilateral_left_type_one_saving.1 (e/3) (by positivity) <;>
    obtain ⟨Z, hz⟩ := bilateral_left_type_one_saving.2 (e/3) (by positivity) <;>
    refine ⟨max 1 (max N (max L Z)), fun n hn even => ?_⟩ <;>
    have hp : 0 < n := by omega
  · have same : bilateralVaughanRemainder n = rightVaughanRemainder n -
        bilateralVaughanPair n (vaughanLogWeight n) (rightResidualWeight n) +
        bilateralVaughanPair n (vaughanZetaWeight n) (rightResidualWeight n) := by
      rw [right_remainder_eq_bilateral_vaughan hp]
      abel
    rw [same]
    refine (subAdd (rightVaughanRemainder n) (bilateralVaughanPair n (vaughanLogWeight n) (rightResidualWeight n))
      (bilateralVaughanPair n (vaughanZetaWeight n) (rightResidualWeight n))).trans ?_
    linarith only [h n (by omega) even, hl n (by omega) even, hz n (by omega) even]
  · rw [right_remainder_eq_bilateral_vaughan hp]
    refine (addSub (bilateralVaughanRemainder n) (bilateralVaughanPair n (vaughanLogWeight n) (rightResidualWeight n))
      (bilateralVaughanPair n (vaughanZetaWeight n) (rightResidualWeight n))).trans ?_
    linarith only [h n (by omega) even, hl n (by omega) even, hz n (by omega) even]

end

end B13NondividingResidueReductionProof

end

/- Left medium waves -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4EnergyTail
open DyadicMixedB4ArcGeometry DyadicMixedB4OffWaveMoment DyadicMixedB4YoungIntegral
open DyadicMixedB4ArcDecomposition DyadicMixedB4PairIntegral
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

noncomputable section

def leftMediumRadius (n : ℕ) : ℝ := 1 / (4 * (n : ℝ) ^ (29 / 30 : ℝ))

def leftMediumCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (3 / 10 : ℝ)⌋₊

private theorem left_medium_radius_le_wide {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (gated : q ≤ leftMediumCap n) :
    leftMediumRadius n ≤ (cutoffH n : ℝ) / ((q : ℝ) * n) := by
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have qr : (0 : ℝ) < q := by exact_mod_cast hq
  have cap : (q : ℝ) ≤ (n : ℝ) ^ (3 / 10 : ℝ) :=
    (show (q : ℝ) ≤ (leftMediumCap n : ℝ) by exact_mod_cast gated).trans (Nat.floor_le (by positivity))
  have bFloor : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ (cutoffB n : ℝ) :=
    floor_half_le (Real.one_le_rpow nOne (by norm_num))
  have logPos : 1 ≤ Nat.log 2 (n + 2) := Nat.log_pos (by decide) (by omega)
  have boundH : (cutoffB n : ℝ) ≤ cutoffH n := by
    have hN : cutoffB n ≤ cutoffH n := by
      unfold cutoffH
      simpa only [mul_one] using Nat.mul_le_mul (show cutoffB n ≤ 256 * cutoffB n by omega)
        (show 1 ≤ (Nat.log 2 (n + 2)) ^ 2 from one_le_pow₀ logPos)
    exact_mod_cast hN
  have power : (n : ℝ) ^ (29 / 30 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) =
    (n : ℝ) ^ (3 / 10 : ℝ) * (n : ℝ) := by
    calc
      _ = (n : ℝ) ^ (13 / 10 : ℝ) := by rw [← Real.rpow_add nr]; norm_num
      _ = (n : ℝ) ^ (3 / 10 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [← Real.rpow_add nr]; norm_num
      _ = _ := by rw [Real.rpow_one]
  apply (le_div_iff₀ (mul_pos qr nr)).mpr
  calc
    _ ≤ leftMediumRadius n * ((n : ℝ) ^ (3 / 10 : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cap nr.le) (by unfold leftMediumRadius; positivity)
    _ = (n : ℝ) ^ (1 / 3 : ℝ) / 4 := by
      rw [← power]
      unfold leftMediumRadius
      field_simp
    _ ≤ cutoffH n := by linarith only [bFloor, boundH, Real.rpow_nonneg nr.le (1 / 3 : ℝ)]

theorem left_medium_grids_covered {n g : ℕ} (hn : 0 < n) (hg : 0 < g)
    (short : g ≤ leftMediumCap n) :
    gridNear (leftMediumRadius n) g ⊆ wide n (cutoffB n) (cutoffH n) := by
  rintro t ⟨j, jBound, near⟩
  let z := j.gcd g
  have hz : 0 < z := Nat.gcd_pos_of_pos_right j hg
  have dvdG : z ∣ g := Nat.gcd_dvd_right j g
  have dvdJ : z ∣ j := Nat.gcd_dvd_left j g
  let q := g / z
  let a := j / z
  have qPos : 0 < q := Nat.div_pos (Nat.le_of_dvd hg dvdG) hz
  have qLe : q ≤ leftMediumCap n := (Nat.div_le_self g z).trans short
  have bLe : leftMediumCap n ≤ cutoffB n :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
  have same : (j : ℝ) / g = (a : ℝ) / q := by
    apply (div_eq_div_iff (by exact_mod_cast hg.ne') (by exact_mod_cast qPos.ne')).mpr
    exact_mod_cast (show j * q = a * g from calc
      _ = (a * z) * q := by rw [show a * z = j from Nat.div_mul_cancel dvdJ]
      _ = a * (q * z) := by ring
      _ = _ := by rw [show q * z = g from Nat.div_mul_cancel dvdG])
  refine ⟨q, a, qPos, qLe.trans bLe, Nat.div_le_div_right jBound,
    Nat.coprime_div_gcd_div_gcd hz, ?_⟩
  rw [← same]
  exact near.trans (left_medium_radius_le_wide hn qPos qLe)

private theorem mediumLeftMask_energy {ι : Type*} (items : Finset ι) {n : ℕ} (hn : 0 < n)
    {W : ℝ} (W0 : 0 ≤ W) (g l r : ι → ℕ) (c : ι → ℂ)
    (steps : ∀ i ∈ items, 0 < g i ∧ g i ≤ leftMediumCap n)
    (ends : ∀ i ∈ items, r i ≤ n / g i)
    (weights : ∀ u ∈ Icc 1 (leftMediumCap n), (∑ i ∈ items.filter (fun i => g i = u), ‖c i‖) ≤ W) :
    (∫ t in (0 : ℝ)..1, ‖∑ i ∈ items, c i * offWave (leftMediumRadius n) (g i) (l i) (r i) t‖ ^ 2) ≤
      640 * W ^ 2 * (n : ℝ) ^ (29 / 30 : ℝ) * logBudget n ^ 3 := by
  let M := leftMediumCap n
  let L := logBudget n
  let P := (n : ℝ) ^ (29 / 30 : ℝ)
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have mPos : 0 < M := Nat.le_floor (Real.one_le_rpow nOne (by norm_num))
  have mBound : M ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nOne (by norm_num))
  have mScale : (M : ℝ) ≤ (n : ℝ) ^ (3 / 10 : ℝ) := Nat.floor_le (by positivity)
  have bPos : 0 < leftMediumRadius n := by unfold leftMediumRadius; positivity
  have L1 : 1 ≤ L := one_le_logBudget n
  have logM : 1 + Real.log M ≤ L := by
    unfold L logBudget
    gcongr
    have realM : (M : ℝ) ≤ n := by exact_mod_cast mBound
    linarith only [realM]
  have logM0 : 0 ≤ 1 + Real.log M :=
    (add_nonneg) zero_le_one (Real.log_nonneg (by exact_mod_cast mPos))
  have mSq : (M : ℝ) ^ 2 ≤ P := calc
    _ ≤ ((n : ℝ) ^ (3 / 10 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) mScale 2
    _ = (n : ℝ) ^ (3 / 5 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le]; norm_num
    _ ≤ P := Real.rpow_le_rpow_of_exponent_le nOne (by norm_num)
  have inv : (leftMediumRadius n)⁻¹ = 4 * P := by unfold leftMediumRadius P; simp
  refine (offWave_mass_le_weighted items n M (leftMediumRadius n) W mPos mBound bPos W0
    g l r c steps ends weights).trans ?_
  change 128 * W ^ 2 * ((M : ℝ) ^ 2 * L ^ 2 + (leftMediumRadius n)⁻¹ * (1 + Real.log M) ^ 3) ≤ _
  rw [inv]
  have first : (M : ℝ) ^ 2 * L ^ 2 ≤ P * L ^ 3 :=
    mul_le_mul mSq (pow_le_pow_right₀ L1 (by decide)) (sq_nonneg _) (by positivity)
  have second : (4 * P) * (1 + Real.log M) ^ 3 ≤ 4 * P * L ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ logM0 logM _) (by positivity)
  calc
    _ ≤ 128 * W ^ 2 * (P * L ^ 3 + 4 * P * L ^ 3) :=
      mul_le_mul_of_nonneg_left (add_le_add first second) (by positivity)
    _ = _ := by unfold P L; ring

theorem mediumLeftWavePair_bound {ι : Type*} (items : Finset ι) {n : ℕ} (hn : 0 < n)
    {W : ℝ} (W0 : 0 ≤ W) (g l r : ι → ℕ) (c : ι → ℂ)
    (steps : ∀ i ∈ items, 0 < g i ∧ g i ≤ leftMediumCap n)
    (ends : ∀ i ∈ items, r i ≤ n / g i)
    (weights : ∀ u ∈ Icc 1 (leftMediumCap n), (∑ i ∈ items.filter (fun i => g i = u), ‖c i‖) ≤ W)
    (A : ℕ → ℂ) {B : ℝ} (coefficients : ∀ m ≤ n, ‖A m‖ ≤ B) :
    ‖∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator (fun x =>
        shiftedPolynomial n A x * (∑ i ∈ items, c i * wave (g i) (l i) (r i) x)) t‖ ≤
      (n : ℝ) ^ (59 / 60 : ℝ) * (B ^ 2 + 320 * W ^ 2 * logBudget n ^ 3) := by
  let f := shiftedPolynomial n A
  let s := (wide n (cutoffB n) (cutoffH n))ᶜ
  let u (t : ℝ) := ∑ i ∈ items, c i * offWave (leftMediumRadius n) (g i) (l i) (r i) t
  let scale := (n : ℝ) ^ (-(1 / 60) : ℝ)
  let P := (n : ℝ) ^ (59 / 60 : ℝ)
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have scalePositive : 0 < scale := Real.rpow_pos_of_pos nr _
  have replacement :
      (∫ t in (0 : ℝ)..1, s.indicator (fun x =>
        f x * (∑ i ∈ items, c i * wave (g i) (l i) (r i) x)) t) =
      ∫ t in (0 : ℝ)..1, s.indicator (fun x => f x * u x) t := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    by_cases member : t ∈ s
    · simp only [Set.indicator_of_mem member]
      apply congrArg (f t * ·)
      refine sum_congr rfl fun i hi => ?_
      have outside : t ∉ gridNear (leftMediumRadius n) (g i) := fun h =>
        member (left_medium_grids_covered hn (steps i hi).1 (steps i hi).2 h)
      have off : t ∈ (gridNear (leftMediumRadius n) (g i))ᶜ := outside
      rw [offWave, Set.indicator_of_mem off]
    · simp only [Set.indicator_of_notMem member]
  rw [replacement]
  have fCont : Continuous f := shiftedPolynomial_continuous n A
  have uMeas : Measurable u :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (offWave_measurable ..)
  have uInt : IntervalIntegrable (fun t => ‖u t‖ ^ 2) volume 0 1 :=
    (interval_sq_bound_of_uniform uMeas (K := ∑ i ∈ items, ‖c i‖ * (r i : ℝ)) (fun t _ =>
      (norm_sum_le _ _).trans (sum_le_sum (fun i _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_offWave_le _ _ _ _ t) (norm_nonneg _))))).1
  have fMass : (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) ≤ ((n : ℝ) + 1) * B ^ 2 := by
    unfold f
    rw [shiftedPolynomial_parseval]
    calc
      _ ≤ ∑ _ ∈ range (n + 1), B ^ 2 := sum_le_sum fun m hm => pow_le_pow_left₀ (norm_nonneg _)
        (coefficients m (Nat.le_of_lt_succ (mem_range.mp hm))) 2
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_range, Nat.cast_add, Nat.cast_one]
  have uMass := mediumLeftMask_energy items hn W0 g l r c steps ends weights
  have fPower : scale * (n : ℝ) = P := by
    unfold scale P
    calc
      _ = (n : ℝ) ^ (-(1 / 60) : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add nr]; norm_num
  have uPower : scale⁻¹ * (n : ℝ) ^ (29 / 30 : ℝ) = P := by
    unfold scale P
    rw [Real.rpow_neg nr.le, inv_inv, ← Real.rpow_add nr]
    norm_num
  have fTerm : scale * (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) ≤ 2 * P * B ^ 2 := calc
    _ ≤ scale * (((n : ℝ) + 1) * B ^ 2) := mul_le_mul_of_nonneg_left fMass scalePositive.le
    _ ≤ scale * (2 * (n : ℝ) * B ^ 2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by linarith only [nOne]) (sq_nonneg _)) scalePositive.le
    _ = _ := by rw [← fPower]; ring
  have uTerm : scale⁻¹ * (∫ t in (0 : ℝ)..1, ‖u t‖ ^ 2) ≤ 640 * W ^ 2 * P * logBudget n ^ 3 := calc
    _ ≤ scale⁻¹ * (640 * W ^ 2 * (n : ℝ) ^ (29 / 30 : ℝ) * logBudget n ^ 3) :=
      mul_le_mul_of_nonneg_left uMass (inv_nonneg.mpr scalePositive.le)
    _ = _ := by rw [← uPower]; ring
  refine (norm_indicator_product_le scalePositive ((wide_measurable ..).compl) fCont.measurable uMeas
    ((fCont.norm.pow 2).intervalIntegrable 0 1) uInt).trans ?_
  refine (mul_le_mul_of_nonneg_left (add_le_add fTerm uTerm) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq ?_
  unfold P
  ring

end

end B13NondividingResidueReductionProof

end

/- Left bilinear short -/
section

namespace B13NondividingResidueReductionProof

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

def leftBilinearPolynomial (n : ℕ) (items : Finset (ℕ × ℕ)) (t : ℝ) : ℂ :=
  ∑ i ∈ items, leftBilinearWeight n i *
    wave (leftBilinearStep i) (cutoffU n / i.2) (n / leftBilinearStep i) t

theorem left_bilinear_eq_polynomial {n : ℕ} (hn : 0 < n) (t : ℝ) :
    plainPolynomial n (fun m => (bandCoefficient n (cutoffU n) (lowCut n) (vaughanBilinearWeight n) m : ℂ)) t =
      leftBilinearPolynomial n (leftBilinearItems n) t := by
  let f := leftBilinearFactor n
  let g := truncateArithmetic f n
  let Z := (ζ : ArithmeticFunction ℝ)
  have short (s : ℕ) (hs : n < s) : g s = 0 := by
    simp [g, truncateArithmetic, not_le_of_gt hs]
  have weights (y : ℕ) (hy : y ≤ n) : vaughanBilinearWeight n y = ((g * Z) : ArithmeticFunction ℝ) y := by
    change ((f * Z) : ArithmeticFunction ℝ) y = ((g * Z) : ArithmeticFunction ℝ) y
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_mul_zeta_apply]
    refine sum_congr rfl fun d hd => ?_
    have dBound := (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
      (Nat.dvd_of_mem_divisors hd)).trans hy
    simp [g, truncateArithmetic, dBound]
  calc
    _ = plainPolynomial n (fun m => (bandCoefficient n (cutoffU n) (lowCut n)
          (fun y => ((g * Z) : ArithmeticFunction ℝ) y) m : ℂ)) t := by
      unfold plainPolynomial
      refine sum_congr rfl fun m hm => ?_
      apply congrArg (fun c : ℂ => c * phase ((m : ℝ) * t))
      apply congrArg Complex.ofReal
      unfold bandCoefficient
      refine sum_congr rfl fun a _ => ?_
      rw [weights _ ((Nat.div_le_self m a).trans (Nat.le_of_lt_succ (mem_range.mp hm)))]
    _ = _ := by
      rw [left_band_short_zeta_polynomial_eq_waves n n hn g short]
      unfold leftBilinearPolynomial leftBilinearItems
      refine sum_congr rfl fun i hi => ?_
      have b := (mem_Icc.mp (mem_product.mp hi).2).2
      simp [leftBilinearStep, leftBilinearWeight, g, truncateArithmetic, b, f]

def leftSmallBilinearItems (n : ℕ) : Finset (ℕ × ℕ) :=
  (leftBilinearItems n).filter (fun i => leftBilinearStep i ≤ leftMediumCap n)

def leftLargeBilinearItems (n : ℕ) : Finset (ℕ × ℕ) :=
  (leftBilinearItems n).filter (fun i => leftMediumCap n < leftBilinearStep i)

def doubleVaughanAfterLeftCut (n : ℕ) (items : Finset (ℕ × ℕ)) : ℂ :=
  ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator
    (fun x => shiftedPolynomial n
      (fun m => (bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n) m : ℂ)) x *
      leftBilinearPolynomial n items x) t

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

private theorem norm_left_small_step_weights {n : ℕ} (hn : 0 < n) {T : ℝ} (T0 : 0 ≤ T)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (u : ℕ) (hu : u ∈ Icc 1 (leftMediumCap n)) :
    (∑ i ∈ (leftSmallBilinearItems n).filter (fun i => leftBilinearStep i = u),
      ‖leftBilinearWeight n i‖) ≤ T^3 * logBudget n := by
  let chosen := (leftSmallBilinearItems n).filter (fun i => leftBilinearStep i = u)
  have hLow : lowCut n ≤ n :=
    Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num))
  have hCap : leftMediumCap n ≤ n :=
    Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num))
  have uPos : 0 < u := (mem_Icc.mp hu).1
  have uBound : u ≤ n := (mem_Icc.mp hu).2.trans hCap
  have count : chosen.card ≤ u.divisors.card := by
    apply card_le_card_of_injOn (Prod.fst : ℕ × ℕ → ℕ)
    · intro i hi
      have hi' : i ∈ chosen := hi
      exact Nat.mem_divisors.mpr ⟨⟨i.2, (mem_filter.mp hi').2.symm⟩, uPos.ne'⟩
    · intro i hi j hj same
      have hi' : i ∈ chosen := hi
      have hj' : j ∈ chosen := hj
      have eq : i.1 * i.2 = j.1 * j.2 := (mem_filter.mp hi').2.trans (mem_filter.mp hj').2.symm
      have first : i.1 ∈ Ioc (cutoffU n) (lowCut n) :=
        (mem_product.mp (mem_filter.mp (mem_filter.mp hi').1).1).1
      apply Prod.ext same
      change i.1 = j.1 at same
      rw [← same] at eq
      exact Nat.eq_of_mul_eq_mul_left ((Nat.zero_le _).trans_lt (mem_Ioc.mp first).1) eq
  have realCount : (chosen.card : ℝ) ≤ T :=
    (show (chosen.card : ℝ) ≤ u.divisors.card by exact_mod_cast count).trans (divisorBound u uBound)
  have L0 := zero_le_one.trans (one_le_logBudget n)
  calc
    _ ≤ ∑ _ ∈ chosen, T * (T * logBudget n) := by
      refine sum_le_sum fun i hi => ?_
      obtain ⟨ha, hs⟩ := mem_product.mp (mem_filter.mp (mem_filter.mp hi).1).1
      have aBound : i.1 ≤ n := (mem_Ioc.mp ha).2.trans hLow
      rw [leftBilinearWeight, norm_mul]
      exact mul_le_mul ((norm_leftBandMoebius_le n i.1).trans (divisorBound i.1 aBound))
        (norm_left_bilinear_factor (mem_Icc.mp hs).2 divisorBound) (norm_nonneg _) T0
    _ = (chosen.card : ℝ) * (T * (T * logBudget n)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ T * (T * (T * logBudget n)) :=
      mul_le_mul_of_nonneg_right realCount (mul_nonneg T0 (mul_nonneg T0 L0))
    _ = _ := by ring

theorem norm_small_left_bilinear_pair {n : ℕ} (hn : 0 < n) {T : ℝ} (T1 : 1 ≤ T)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖doubleVaughanAfterLeftCut n (leftSmallBilinearItems n)‖ ≤
      321 * (n : ℝ) ^ (59 / 60 : ℝ) * T^8 * logBudget n^5 := by
  let R (m : ℕ) := (bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n) m : ℂ)
  let W := T^3 * logBudget n
  let L := logBudget n
  have T0 := zero_le_one.trans T1
  have L1 := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have rBound : ∀ m ≤ n, ‖R m‖ ≤ T^4 * L := fun _ hm => norm_right_residual_coefficient hm T1 divisorBound
  have steps (i : ℕ × ℕ) (hi : i ∈ leftSmallBilinearItems n) :
      0 < leftBilinearStep i ∧ leftBilinearStep i ≤ leftMediumCap n := by
    obtain ⟨product, step⟩ := mem_filter.mp hi
    obtain ⟨ha, hs⟩ := mem_product.mp product
    exact ⟨Nat.mul_pos ((Nat.zero_le _).trans_lt (mem_Ioc.mp ha).1) (mem_Icc.mp hs).1, step⟩
  have est := mediumLeftWavePair_bound (leftSmallBilinearItems n) hn (W := W) (by positivity)
    leftBilinearStep (fun i => cutoffU n / i.2) (fun i => n / leftBilinearStep i)
    (leftBilinearWeight n) steps (fun _ _ => le_rfl)
    (norm_left_small_step_weights hn T0 divisorBound) R rBound
  refine est.trans ?_
  have b1 : (T^4 * L)^2 ≤ T^8 * L^5 := by
    calc
      _ = T^8 * L^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ L1 (by decide)) (by positivity)
  have b2 : 320 * W^2 * L^3 ≤ 320 * (T^8 * L^5) := by
    calc
      _ = (320 * L^5) * T^6 := by unfold W L; ring
      _ ≤ (320 * L^5) * T^8 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ T1 (by decide)) (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by positivity)).trans_eq (by unfold L; ring)

end

end B13NondividingResidueReductionProof

end

/- Left bilinear bridge -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4PairIntegral
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def bilateralLargeLeftRemainder (n : ℕ) : ℂ :=
  doubleVaughanAfterLeftCut n (leftLargeBilinearItems n)

def bilateralSmallLeftContribution (n : ℕ) : ℂ :=
  doubleVaughanAfterLeftCut n (leftSmallBilinearItems n)

theorem bilateralSmallLeftContribution_saving : saving bilateralSmallLeftContribution := by
  intro e he
  obtain ⟨D, D1, divBound⟩ := divisor_envelope
  let C := 321 * D^8
  have limit : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(61 / 15360) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 61 / 15360)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(61 / 15360) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have estimates : ∀ᶠ n : ℕ in atTop, ‖bilateralSmallLeftContribution n‖ ≤ e * (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le, scaled.eventually_lt_const he]
      with n hn logs small
    have an : 0 < n := by omega
    have nr : (0 : ℝ) < n := by exact_mod_cast an
    let X := (n : ℝ) ^ (1 / 1024 : ℝ)
    let T := D * X
    have T1 : 1 ≤ T :=
      one_le_mul_of_one_le_of_one_le D1 (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))
    have exp : (n : ℝ) ^ (59 / 60 : ℝ) * X^13 =
        (n : ℝ) ^ (-(61 / 15360) : ℝ) * (n : ℝ) := by
      unfold X
      rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le, ← Real.rpow_add nr]
      calc
        _ = (n : ℝ) ^ (-(61 / 15360) + 1 : ℝ) := by congr 1; norm_num
        _ = (n : ℝ) ^ (-(61 / 15360) : ℝ) * (n : ℝ) ^ (1 : ℝ) := Real.rpow_add nr _ _
        _ = _ := by rw [Real.rpow_one]
    refine (norm_small_left_bilinear_pair an T1 (divBound n)).trans ?_
    calc
      _ ≤ 321 * (n : ℝ) ^ (59 / 60 : ℝ) * T^8 * X^5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (one_le_logBudget n)) logs 5)
          (by positivity)
      _ = C * ((n : ℝ) ^ (59 / 60 : ℝ) * X^13) := by unfold C T; ring
      _ = (C * (n : ℝ) ^ (-(61 / 15360) : ℝ)) * (n : ℝ) := by rw [exp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
  obtain ⟨N, bound⟩ := eventually_atTop.mp estimates
  exact ⟨N, fun n hn _ => bound n hn⟩

theorem bilateralVaughanRemainder_eq_left_cut {n : ℕ} (hn : 0 < n) :
    bilateralVaughanRemainder n = bilateralLargeLeftRemainder n + bilateralSmallLeftContribution n := by
  let s := (wide n (cutoffB n) (cutoffH n))ᶜ
  let r := shiftedPolynomial n
    (fun m => (bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n) m : ℂ))
  let J (items : Finset (ℕ × ℕ)) := s.indicator (fun t => r t * leftBilinearPolynomial n items t)
  have int (items : Finset (ℕ × ℕ)) : IntervalIntegrable (J items) volume 0 1 := by
    have cont : Continuous (leftBilinearPolynomial n items) := by
      unfold leftBilinearPolynomial wave phase
      fun_prop
    exact indicator_intervalIntegrable ((shiftedPolynomial_continuous ..).mul cont)
      (wide_measurable ..).compl
  have eq : bilateralVaughanRemainder n = doubleVaughanAfterLeftCut n (leftBilinearItems n) := by
    unfold bilateralVaughanRemainder bilateralVaughanPair doubleVaughanAfterLeftCut
    simp_rw [left_bilinear_eq_polynomial hn]
  rw [eq]
  change (∫ t in (0 : ℝ)..1, J (leftBilinearItems n) t) =
    (∫ t in (0 : ℝ)..1, J (leftLargeBilinearItems n) t) +
      (∫ t in (0 : ℝ)..1, J (leftSmallBilinearItems n) t)
  rw [← intervalIntegral.integral_add (int _) (int _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have partition : leftBilinearPolynomial n (leftBilinearItems n) t =
      leftBilinearPolynomial n (leftLargeBilinearItems n) t +
        leftBilinearPolynomial n (leftSmallBilinearItems n) t := by
    unfold leftBilinearPolynomial leftLargeBilinearItems leftSmallBilinearItems
    rw [add_comm]
    symm
    simpa only [not_le] using sum_filter_add_sum_filter_not (leftBilinearItems n)
      (fun i => leftBilinearStep i ≤ leftMediumCap n)
      (fun i => leftBilinearWeight n i *
        wave (leftBilinearStep i) (cutoffU n / i.2) (n / leftBilinearStep i) t)
  by_cases inside : t ∈ s
  · simp only [J, Set.indicator_of_mem inside, partition, mul_add]
  · simp [J, inside]

theorem frozen_iff_bilateral_large_left : frozenGoal ↔ saving bilateralLargeLeftRemainder := by
  rw [frozen_iff_bilateral_vaughan]
  constructor <;> intro b e he <;>
    obtain ⟨N, h⟩ := b (e/2) (by positivity) <;>
    obtain ⟨M, hs⟩ := bilateralSmallLeftContribution_saving (e/2) (by positivity) <;>
    refine ⟨max 1 (max N M), fun n hn even => ?_⟩ <;>
    have np : 0 < n := by omega
  · have difference : bilateralLargeLeftRemainder n =
      bilateralVaughanRemainder n - bilateralSmallLeftContribution n := by
      rw [bilateralVaughanRemainder_eq_left_cut np]
      abel
    rw [difference]
    refine (norm_sub_le (bilateralVaughanRemainder n) (bilateralSmallLeftContribution n)).trans ?_
    linarith only [h n (by omega) even, hs n (by omega) even]
  · rw [bilateralVaughanRemainder_eq_left_cut np]
    refine (norm_add_le (bilateralLargeLeftRemainder n) (bilateralSmallLeftContribution n)).trans ?_
    linarith only [h n (by omega) even, hs n (by omega) even]

end

end B13NondividingResidueReductionProof

end

/- Right bilinear waves -/
section

namespace B13NondividingResidueReductionProof

open Finset ArithmeticFunction
open DyadicMixedB4Arithmetic DyadicMixedB4Scale DyadicMixedB4ArcDecomposition DyadicMixedB4Geometric
open DyadicMixedB4HighAtoms DyadicMixedB4MoebiusGauss DyadicMixedB4TailScale DyadicMixedB4EnergyTail
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

private theorem band_as_progression_tails (n lo hi m : ℕ) (weight : ℕ → ℝ) (ordered : lo ≤ hi) :
    bandCoefficient n lo hi weight m =
      upperBandWeight (cutoffU n) lo (fun d => (μ d : ℝ)) weight m -
      upperBandWeight (cutoffU n) hi (fun d => (μ d : ℝ)) weight m := by
  classical
  unfold bandCoefficient upperBandWeight
  simp only [sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun a _ => ?_
  by_cases hl : lo < a
  · by_cases hh : a ≤ hi
    · simp [hl, hh, not_lt_of_ge hh]
    · simp [hl, hh, lt_of_not_ge hh]
  · have nh : ¬ hi < a := fun h => hl (ordered.trans_lt h)
    simp [hl, nh]

private theorem band_interval_sum_sub {lo hi limit : ℕ} (h : lo ≤ hi) (f : ℕ → ℂ) :
    (∑ k ∈ Ioc lo limit, f k) - (∑ k ∈ Ioc hi limit, f k) =
      ∑ k ∈ Ioc lo (min hi limit), f k := by
  have left : (Ioc lo limit).filter (· ≤ hi) = Ioc lo (min hi limit) := by
    ext k
    simp only [mem_filter, mem_Ioc, le_min_iff]
    tauto
  have right : (Ioc lo limit).filter (fun k => ¬ k ≤ hi) = Ioc hi limit := by
    ext k
    simp only [mem_filter, mem_Ioc, not_le]
    omega
  have split := sum_filter_add_sum_filter_not (Ioc lo limit) (· ≤ hi) f
  rw [left, right] at split
  exact (eq_sub_of_add_eq split).symm

theorem band_series_progressions (n L V : ℕ) (lower : 1 ≤ L) (ordered : L ≤ V) (t : ℝ) (weight : ℕ → ℝ) :
    plainPolynomial n
      (fun m => (bandCoefficient n L V weight m : ℂ)) t =
    ∑ b ∈ Ioc (cutoffU n) n, ∑ d ∈ Icc 1 (min (cutoffU n) (n / b)),
      (-(μ d : ℂ)) * (weight b : ℂ) *
        ∑ k ∈ Ioc (L / d) (min (V / d) (n / (d * b))),
          phase (((d * b * k : ℕ) : ℝ) * t) := by
  let w (b : ℕ) : ℂ := weight b
  let f (m : ℕ) : ℂ := phase ((m : ℝ) * t)
  let U := cutoffU n
  have cast (lo m : ℕ) :
      (↑(upperBandWeight (R := ℝ) (cutoffU n) lo (fun d => (μ d : ℝ)) weight m) : ℂ) =
        upperBandWeight (R := ℂ) U lo (fun d => (μ d : ℂ)) w m := by
    unfold upperBandWeight w
    push_cast
    rfl
  have tail (lo : ℕ) (loPos : 1 ≤ lo) :
      (∑ m ∈ range (n + 1), upperBandWeight U lo (fun d => (μ d : ℂ)) w m * f m) =
        ∑ b ∈ Ioc U n, ∑ d ∈ Icc 1 (min U (n / b)),
          (-(μ d : ℂ)) * w b * ∑ k ∈ Ioc (lo / d) (n / (d * b)), f (d * b * k) := by
    refine upper_band_progressions n U lo n le_rfl ?_ _ _ _ ?_
    · intro a b larger prod
      exact (Nat.le_mul_of_pos_left b (by omega)).trans prod
    · intro a larger
      have nonunit : a ≠ 1 := by omega
      have integer : (∑ d ∈ a.divisors, μ d) = 0 := by
        rw [← coe_mul_zeta_apply (f := μ), moebius_mul_coe_zeta, one_apply_ne nonunit]
      exact_mod_cast integer
  unfold plainPolynomial
  change (∑ m ∈ range (n + 1), (bandCoefficient n L V weight m : ℂ) * f m) = _
  simp only [band_as_progression_tails n L V _ weight ordered, Complex.ofReal_sub,
    cast, sub_mul, sum_sub_distrib]
  rw [tail L lower, tail V (lower.trans ordered)]
  simp only [← sum_sub_distrib, ← mul_sub]
  refine sum_congr rfl fun b _ => sum_congr rfl fun d _ => ?_
  rw [band_interval_sum_sub (Nat.div_le_div_right ordered)]

private theorem right_large_lower_band_eq {n m : ℕ} (hn : 0 < n) (hm : m ≤ n) (w : ℕ → ℝ) :
    bandCoefficient n (cutoffB n) (upperCut n) (restrictLargeRight n w) m =
      bandCoefficient n (cutoffB n) (splitCut n) (restrictLargeRight n w) m := by
  simp only [bandCoefficient, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : a ≤ splitCut n
  · simp [ha, ha.trans (cuts_ordered n hn).2.2]
  · have cofactor := cofactor_of_high_divisor hn (lt_of_not_ge ha : splitCut n < a)
      ((Nat.mul_div_le m a).trans hm)
    have cutoff : ⌊(n : ℝ) ^ (5 / 12 : ℝ)⌋₊ ≤ rightLargeCofactorCut n :=
      Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num))
    simp [ha, restrictLargeRight, not_lt_of_ge (cofactor.trans cutoff)]

abbrev RightLowWaveIndex := Σ _ : ℕ, ℕ

def rightLowWaveItems (n : ℕ) : Finset RightLowWaveIndex :=
  (Ioc (cutoffU n) (min n (rightLargeCofactorCut n))).sigma fun b =>
    Icc 1 (min (cutoffU n) (n/b))

def rightLowWaveStep (i : RightLowWaveIndex) : ℕ := i.2 * i.1

def rightLowWaveWeight (i : RightLowWaveIndex) : ℂ := -(μ i.2 : ℂ) * (vonMangoldt i.1 : ℂ)

def rightLowWaveUpper (n : ℕ) (i : RightLowWaveIndex) : ℕ :=
  min (upperCut n / i.2) (n / rightLowWaveStep i)

def rightLowPolynomial (n : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ rightLowWaveItems n, rightLowWaveWeight i *
    wave (rightLowWaveStep i) (cutoffB n / i.2) (rightLowWaveUpper n i) t

def rightLowResidualWeight (n b : ℕ) : ℝ :=
  if b ≤ rightLargeCofactorCut n then vonMangoldt b else 0

private theorem right_low_series {n : ℕ} (hn : 0 < n) (t : ℝ) :
    plainPolynomial n (fun m => (bandCoefficient n (cutoffB n) (upperCut n)
      (rightLowResidualWeight n) m : ℂ)) t = rightLowPolynomial n t := by
  have order := cuts_ordered n hn
  rw [band_series_progressions n (cutoffB n) (upperCut n) order.1 (order.2.1.trans order.2.2)]
  unfold rightLowPolynomial rightLowWaveItems
  rw [sum_sigma]
  symm
  let K := rightLargeCofactorCut n
  let G (b d : ℕ) := -(μ d : ℂ) * (rightLowResidualWeight n b : ℂ) *
    ∑ k ∈ Ioc (cutoffB n/d) (min (upperCut n/d) (n/(d*b))), phase (((d*b*k : ℕ) : ℝ)*t)
  calc
    _ = ∑ b ∈ Ioc (cutoffU n) (min n K), ∑ d ∈ Icc 1 (min (cutoffU n) (n/b)), G b d := by
      refine sum_congr rfl fun b hb => sum_congr rfl fun d _ => ?_
      have small : b ≤ K := (mem_Ioc.mp hb).2.trans (min_le_right _ _)
      simp [G, rightLowResidualWeight, K] at small ⊢
      simp [small, rightLowWaveWeight, rightLowWaveStep, rightLowWaveUpper, wave]
    _ = _ := by
      refine sum_subset (fun b hb => mem_Ioc.mpr ⟨(mem_Ioc.mp hb).1, (mem_Ioc.mp hb).2.trans (min_le_left ..)⟩) ?_
      intro b hb outside
      have h : ¬ b ≤ K := fun bSmall => outside
        (mem_Ioc.mpr ⟨(mem_Ioc.mp hb).1, le_min (mem_Ioc.mp hb).2 bSmall⟩)
      have h' : ¬ b ≤ rightLargeCofactorCut n := h
      simp [G, rightLowResidualWeight, h']

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

def rightHighPolynomial (n : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ rightHighWaveItems n, rightHighWaveWeight n i *
    wave (rightHighWaveStep i) (rightHighWaveLower n i) (n / rightHighWaveStep i) t

private theorem right_high_series {n : ℕ} (hn : 0 < n) (t : ℝ) :
    plainPolynomial n (fun m => (bandCoefficient n (cutoffB n) (upperCut n)
      (restrictLargeRight n (rightVaughanBilinearWeight n)) m : ℂ)) t = rightHighPolynomial n t := by
  let f := rightHighWaveFactor n
  let g := truncateArithmetic f n
  let Z := (ζ : ArithmeticFunction ℝ)
  let w (y : ℕ) := ((g * Z) : ArithmeticFunction ℝ) y
  have short (s : ℕ) (hs : n < s) : g s = 0 := by
    simp [g, truncateArithmetic, not_le_of_gt hs]
  have agree (y : ℕ) (hy : y ≤ n) : rightVaughanBilinearWeight n y = w y := by
    change ((f * Z) : ArithmeticFunction ℝ) y = ((g * Z) : ArithmeticFunction ℝ) y
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_mul_zeta_apply]
    refine sum_congr rfl fun d hd => ?_
    have dBound := (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
      (Nat.dvd_of_mem_divisors hd)).trans hy
    simp [g, truncateArithmetic, dBound]
  have coeff (m : ℕ) (hm : m ≤ n) :
      bandCoefficient n (cutoffB n) (upperCut n) (restrictLargeRight n (rightVaughanBilinearWeight n)) m =
        bandCoefficient n (cutoffB n) (splitCut n) (restrictLargeRight n w) m := by
    rw [right_large_lower_band_eq hn hm]
    unfold bandCoefficient restrictLargeRight
    refine sum_congr rfl fun a _ => ?_
    rw [agree _ ((Nat.div_le_self _ _).trans hm)]
  calc
    _ = plainPolynomial n (fun m => (bandCoefficient n (cutoffB n) (splitCut n)
          (restrictLargeRight n w) m : ℂ)) t := by
      unfold plainPolynomial
      refine sum_congr rfl fun m hm => ?_
      dsimp only
      rw [coeff m (Nat.le_of_lt_succ (mem_range.mp hm))]
    _ = ∑ i ∈ rightHighWaveBase n, rightHighWaveWeight n i *
          wave (rightHighWaveStep i) (rightHighWaveLower n i) (n / rightHighWaveStep i) t := by
      unfold restrictLargeRight
      rw [right_band_large_cofactor_polynomial hn (cutoffU_le_rightLargeCofactorCut hn) _ t,
        rightHighWaveBase, sum_sigma]
      refine sum_congr rfl fun d _ => ?_
      rw [sum_product, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      change -(μ d : ℂ) * (∑ b ∈ Ioc (rightLargeCofactorCut n) (n / (d*k)),
        (((g * (ζ : ArithmeticFunction ℝ)) : ArithmeticFunction ℝ) b : ℂ) *
          phase (((d*k*b : ℕ) : ℝ)*t)) = _
      rw [zeta_cofactor_sum_eq_waves n (rightLargeCofactorCut n) (d*k) n g short t, mul_sum]
      refine sum_congr rfl fun a ha => ?_
      have le := (mem_Icc.mp ha).2
      simp [rightHighWaveWeight, rightHighWaveStep, rightHighWaveLower, g, f, truncateArithmetic, le, mul_assoc]
    _ = _ := by
      symm
      unfold rightHighPolynomial rightHighWaveItems
      refine sum_subset (filter_subset _ _) fun i hi outside => ?_
      have big : n < rightHighWaveStep i := lt_of_not_ge fun small => outside (mem_filter.mpr ⟨hi,small⟩)
      simp [wave, Nat.div_eq_of_lt big]

theorem right_residual_polynomial_eq_waves (n : ℕ) (hn : 0 < n) (t : ℝ) :
    plainPolynomial n (fun m => (bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n) m : ℂ)) t =
      rightLowPolynomial n t + rightHighPolynomial n t := by
  rw [← right_low_series hn, ← right_high_series hn]
  have coeff (m : ℕ) :
      bandCoefficient n (cutoffB n) (upperCut n) (rightResidualWeight n) m =
        bandCoefficient n (cutoffB n) (upperCut n) (rightLowResidualWeight n) m +
          bandCoefficient n (cutoffB n) (upperCut n)
            (restrictLargeRight n (rightVaughanBilinearWeight n)) m := by
    unfold bandCoefficient
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← mul_add]
    by_cases high : rightLargeCofactorCut n < m/a <;>
      simp [rightResidualWeight, rightLowResidualWeight, restrictLargeRight, high, not_le_of_gt, le_of_not_gt]
  simp only [plainPolynomial, ← sum_add_distrib, coeff, Complex.ofReal_add, add_mul]

end

end B13NondividingResidueReductionProof

end

/- Common wave centers -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory Filter
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open DyadicMixedB4ArcDecomposition DyadicMixedB4WindowKernel DyadicMixedB4Ramanujan
open DyadicMixedB4OffWaveMoment
open scoped Classical

noncomputable section

theorem centered_deep_periodic_integral (n M B H R g : ℕ) (k : ℤ) (A : ℝ → ℂ)
    (continuous : Continuous A)
    (recenter : ∀ q : ℕ, 0 < q → q ∣ g → ∀ (a : ℕ) (t : ℝ), A (t + (a : ℝ)/q) = A t)
    (nPositive : 0 < n) (gPositive : 0 < g) (gBound : g ≤ M) (Bbound : B ≤ M)
    (width : 4 * H * M ≤ n) (Rpositive : 1 ≤ R) (Rbound : R ≤ B)
    (cover : (R : ℝ) * n * radius M ≤ H) :
    (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator
        (fun x => phase ((k : ℝ) * x) * A x) t) =
      ∑ q ∈ g.divisors.filter (fun q => R < q), ramanujan q k *
        ∫ t in window n M B H q, phase ((k : ℝ) * t) * A t := by
  classical
  let f (x : ℝ) := phase ((k : ℝ) * x) * A x
  have phaseContinuous : Continuous (fun x : ℝ => phase ((k : ℝ) * x)) := by
    unfold phase
    fun_prop
  have fContinuous : Continuous f := phaseContinuous.mul continuous
  have cellIntegrable (q a : ℕ) : IntervalIntegrable ((cell n M B H q a).indicator f) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (fContinuous.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
      (cell_measurable n M B H q a)
  have split : (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator f t) =
      ∑ q ∈ g.divisors, ∑ a ∈ numSet q, ∫ t in (0 : ℝ)..1, (cell n M B H q a).indicator f t := by
    calc
      _ = ∫ t in (0 : ℝ)..1, ∑ q ∈ g.divisors, ∑ a ∈ numSet q, (cell n M B H q a).indicator f t := by
        apply intervalIntegral.integral_congr
        intro t _
        exact deep_cell_indicator f n M g B H nPositive gPositive gBound Bbound width t
      _ = _ := by
        rw [intervalIntegral.integral_finsetSum]
        · refine sum_congr rfl fun q _ => ?_
          rw [intervalIntegral.integral_finsetSum]
          exact fun a _ => cellIntegrable q a
        · intro q _
          have integrated := IntervalIntegrable.sum (numSet q) (fun a _ => cellIntegrable q a)
          convert integrated using 1
          funext t
          simp only [Finset.sum_apply]
  change (∫ t in (0 : ℝ)..1, (gridNear (radius M) g ∩ (wide n B H)ᶜ).indicator f t) = _
  rw [split, Finset.sum_filter]
  refine sum_congr rfl fun q qMember => ?_
  have qPositive := Nat.pos_of_mem_divisors qMember
  by_cases large : R < q
  · have qLower : 1 < q := Rpositive.trans_lt large
    have divides := (Nat.mem_divisors.mp qMember).1
    have qBound : q ≤ M := (Nat.le_of_dvd gPositive divides).trans gBound
    rw [if_pos large, ramanujan, sum_mul]
    refine sum_congr rfl fun a aMember => ?_
    rw [integral_cell_translate qLower qBound aMember, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    change phase ((k : ℝ) * (t + (a : ℝ) / q)) * A (t + (a : ℝ) / q) = _
    rw [recenter q qPositive divides a t, mul_add, phase_add]
    ring
  · rw [if_neg large]
    apply sum_eq_zero
    intro a _
    have emptyWindow := window_empty_of_small_modulus nPositive qPositive (le_of_not_gt large) Rbound cover
    have emptyCell : cell n M B H q a = ∅ := by simp [cell, emptyWindow]
    simp [emptyCell]

/-- Only the reduced fractions of the common grid enter the neighborhood term. -/
theorem centered_deep_wave_product (n M B H R u v l r p s : ℕ) (k : ℤ)
    (hn : 0 < n) (hu : 0 < u) (hM : u.gcd v ≤ M) (hB : B ≤ M)
    (width : 4 * H * M ≤ n) (hR : 1 ≤ R) (hRB : R ≤ B)
    (cover : (R : ℝ) * n * radius M ≤ H) :
    (∫ t in (0 : ℝ)..1, (gridNear (radius M) (u.gcd v) ∩ (wide n B H)ᶜ).indicator
        (fun x => phase ((k : ℝ) * x) * (wave u l r x * wave v p s x)) t) =
      ∑ q ∈ (u.gcd v).divisors.filter (fun q => R < q), ramanujan q k *
        ∫ t in window n M B H q, phase ((k : ℝ) * t) * (wave u l r t * wave v p s t) := by
  refine centered_deep_periodic_integral n M B H R (u.gcd v) k _
    ((wave_continuous ..).mul (wave_continuous ..)) ?_ hn
    (Nat.gcd_pos_of_pos_left v hu) hM hB width hR hRB cover
  intro q hq qDiv a t
  rw [wave_at_cell_center hq (qDiv.trans (Nat.gcd_dvd_left u v)),
    wave_at_cell_center hq (qDiv.trans (Nat.gcd_dvd_right u v))]

private theorem integral_center_kernel_sq {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Icc (-1 : ℝ) 1, (smoothKernel a 0 t)^2) ≤ 4/a := by
  let F (t : ℝ) := (smoothKernel a 0 t)^2
  have fc : Continuous F := (cont_smoothKernel ha).pow 2
  have mirror : (∫ t in (-1 : ℝ)..0, F t) = ∫ t in (0 : ℝ)..1, F t := by
    calc
      _ = ∫ t in (-1 : ℝ)..0, F (-t) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp [F, smoothKernel]
      _ = _ := by simpa using intervalIntegral.integral_comp_neg (f := F) (a := (-1 : ℝ)) (b := 0)
  change (∫ t in Set.Icc (-1 : ℝ) 1, F t) ≤ _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (fc.intervalIntegrable (-1) 0) (fc.intervalIntegrable 0 1), mirror]
  have part : (∫ t in (0 : ℝ)..1, F t) ≤ 2/a :=
    integral_smoothKernel_sq (c := 0) ha le_rfl (by norm_num)
  exact (add_le_add part part).trans_eq (by ring)

theorem norm_common_window_pair_le (n M B H q u v l r p s : ℕ) (k : ℤ)
    (hn : 0 < n) (hu : 0 < u) (hv : 0 < v) (size : u*v ≤ M^2)
    (hr : r ≤ n/u) (hs : s ≤ n/v) :
    ‖∫ t in window n M B H q, phase ((k : ℝ)*t) * (wave u l r t * wave v p s t)‖ ≤
      32 * (n : ℝ) / ((u : ℝ)*v) := by
  let a := 1 / ((n : ℝ)+1)
  let W := window n M B H q
  let P (t : ℝ) := phase ((k : ℝ)*t) * (wave u l r t * wave v p s t)
  let F (t : ℝ) := (smoothKernel a 0 t)^2
  let C := 4 / ((u : ℝ)*v)
  have mPos : 0 < M := by
    by_contra! h
    have zero : M = 0 := by omega
    subst M
    simp [Nat.ne_of_gt hu, Nat.ne_of_gt hv] at size
  have mReal : (0 : ℝ) < M := by exact_mod_cast mPos
  have radiusOne : radius M ≤ 1 := by
    unfold radius
    apply (div_le_one (by positivity)).mpr
    have oneM : (1 : ℝ) ≤ M := by exact_mod_cast mPos
    nlinarith only [one_le_pow₀ (n := 2) oneM]
  have aPos : 0 < a := by unfold a; positivity
  have C0 : 0 ≤ C := by unfold C; positivity
  have boundOn (g : ℕ) (hg : g ≤ M^2) (t : ℝ) (ht : t ∈ W) :
      |(g : ℝ)*t - (0 : ℕ)| ≤ 1/2 := by
    have win := window_subset_interval n M B H q ht
    have hAbs : |t| ≤ radius M := abs_le.mpr win
    have hmax : (g : ℝ) ≤ (M : ℝ)^2 := by exact_mod_cast hg
    simp only [Nat.cast_zero, sub_zero, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) g)]
    calc
      _ ≤ (g : ℝ) * radius M := mul_le_mul_of_nonneg_left hAbs (Nat.cast_nonneg _)
      _ ≤ (M : ℝ)^2 * radius M := mul_le_mul_of_nonneg_right hmax (radius_nonnegative M)
      _ = 1/8 := by unfold radius; field_simp
      _ ≤ _ := by norm_num
  have first (t : ℝ) (ht : t ∈ W) : ‖wave u l r t‖ ≤ (2/(u:ℝ)) * smoothKernel a 0 t := by
    simpa only [Nat.cast_zero, zero_div] using
      waveBound (l := l) hu hr (boundOn u ((Nat.le_mul_of_pos_right u hv).trans size) t ht)
  have second (t : ℝ) (ht : t ∈ W) : ‖wave v p s t‖ ≤ (2/(v:ℝ)) * smoothKernel a 0 t := by
    simpa only [Nat.cast_zero, zero_div] using
      waveBound (l := p) hv hs (boundOn v ((Nat.le_mul_of_pos_left v hu).trans size) t ht)
  have sub : W ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro t ht
    obtain ⟨lo,hi⟩ := window_subset_interval n M B H q ht
    exact ⟨(neg_le_neg radiusOne).trans lo, hi.trans radiusOne⟩
  have pc : Continuous P := by unfold P wave phase; fun_prop
  have fc : Continuous F := (cont_smoothKernel aPos).pow 2
  have compF : IntegrableOn F (Set.Icc (-1 : ℝ) 1) volume := fc.continuousOn.integrableOn_Icc
  have intP : IntegrableOn (fun t => ‖P t‖) W volume := pc.norm.continuousOn.integrableOn_Icc.mono_set sub
  have intF : IntegrableOn (fun t => C*F t) W volume := (compF.mono_set sub).const_mul C
  have point (t : ℝ) (ht : t ∈ W) : ‖P t‖ ≤ C * F t := by
    simp only [P, norm_mul, norm_phase', one_mul]
    refine (mul_le_mul (first t ht) (second t ht) (norm_nonneg _) ?_).trans_eq ?_
    · exact mul_nonneg (by positivity) (nonneg_smoothKernel aPos.le)
    · unfold C F
      ring
  change ‖∫ t in W, P t‖ ≤ _
  calc
    _ ≤ ∫ t in W, ‖P t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in W, C*F t := setIntegral_mono_on intP intF (window_measurable ..) point
    _ = C * ∫ t in W, F t := integral_const_mul ..
    _ ≤ C * (∫ t in Set.Icc (-1 : ℝ) 1, F t) :=
      mul_le_mul_of_nonneg_left (setIntegral_mono_set compF
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) (Filter.Eventually.of_forall sub)) C0
    _ ≤ C * (4/a) := mul_le_mul_of_nonneg_left (integral_center_kernel_sq aPos) C0
    _ = 16 * ((n : ℝ)+1) / ((u : ℝ)*v) := by unfold C a; field_simp; ring
    _ ≤ _ := by
      have oneN : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact div_le_div_of_nonneg_right (by linarith only [oneN]) (by positivity)

end

end B13NondividingResidueReductionProof

end

/- Joint short pair -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open DyadicMixedB4ArcDecomposition DyadicMixedB4OffWaveMoment DyadicMixedB4WindowKernel
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def productStepDeepIntegral (n u v l r p s : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator
    (fun x => phase (((-(n : ℤ)) : ℝ) * x) * (wave u l r x * wave v p s x)) t

theorem norm_product_step_deep_integral_le (n u v l r p s : ℕ)
    (hn : 0 < n) (hu : 0 < u) (hv : 0 < v)
    (withinU : u ≤ n) (withinV : v ≤ n) (size : u*v ≤ maximumStep n^2)
    (hr : r ≤ n/u) (hs : s ≤ n/v) (width : 4 * cutoffH n * maximumStep n ≤ n) :
    ‖productStepDeepIntegral n u v l r p s‖ ≤
      128 * (logBudget n^2 + (u.gcd v : ℝ) / ((u : ℝ)*v*radius (maximumStep n))) +
        (32 * (n : ℝ) / ((u : ℝ)*v)) *
          ∑ q ∈ (u.gcd v).divisors.filter (fun q => cutoffR n < q), ‖ramanujan q (-(n : ℤ))‖ := by
  let M := maximumStep n
  let B := cutoffB n
  let H := cutoffH n
  let R := cutoffR n
  let d := u.gcd v
  let grid := gridNear (radius M) d
  let deep := (wide n B H)ᶜ
  let F (t : ℝ) := phase (((-(n : ℤ)) : ℝ)*t) * (wave u l r t * wave v p s t)
  let Q (t : ℝ) := ‖wave u l r t * wave v p s t‖
  have phaseC : Continuous (fun t : ℝ => phase (((-(n : ℤ)) : ℝ) * t)) := by unfold phase; fun_prop
  have FC : Continuous F := phaseC.mul ((wave_continuous ..).mul (wave_continuous ..))
  have QC : Continuous Q := ((wave_continuous ..).mul (wave_continuous ..)).norm
  have gridM : MeasurableSet grid := gridNear_measurable ..
  have deepM : MeasurableSet deep := (wide_measurable ..).compl
  have nearInt : IntervalIntegrable ((grid ∩ deep).indicator F) volume 0 1 :=
    indicator_intervalIntegrable FC (gridM.inter deepM)
  have farInt : IntervalIntegrable ((gridᶜ ∩ deep).indicator F) volume 0 1 :=
    indicator_intervalIntegrable FC (gridM.compl.inter deepM)
  have split : productStepDeepIntegral n u v l r p s =
      (∫ t in (0 : ℝ)..1, (gridᶜ ∩ deep).indicator F t) +
      (∫ t in (0 : ℝ)..1, (grid ∩ deep).indicator F t) := by
    unfold productStepDeepIntegral
    rw [← intervalIntegral.integral_add farInt nearInt]
    refine intervalIntegral.integral_congr fun t _ => ?_
    change deep.indicator F t = (gridᶜ ∩ deep).indicator F t + (grid ∩ deep).indicator F t
    by_cases gridHit : t ∈ grid <;> by_cases deepHit : t ∈ deep <;> simp [gridHit, deepHit]
  have cuts := cutoffs_ordered n hn
  have bPos : 0 < radius M := by
    have mPos : (0 : ℝ) < M := by exact_mod_cast cuts.1.trans (cuts.2.1.trans cuts.2.2.1)
    unfold radius
    positivity
  have far : ‖∫ t in (0 : ℝ)..1, (gridᶜ ∩ deep).indicator F t‖ ≤
      128 * (logBudget n^2 + (d : ℝ)/((u : ℝ)*v*radius M)) := by
    have dom (t : ℝ) : ‖(gridᶜ ∩ deep).indicator F t‖ ≤ gridᶜ.indicator Q t := by
      by_cases g : t ∈ grid <;> by_cases m : t ∈ deep <;>
        simp [g, m, F, Q, norm_phase'] <;> positivity
    have intQ : IntervalIntegrable (gridᶜ.indicator Q) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact (QC.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator gridM.compl
    have first := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := (gridᶜ ∩ deep).indicator F)
      (by norm_num : (0 : ℝ) ≤ 1)
    exact first.trans ((intervalIntegral.integral_mono_on zero_le_one farInt.norm intQ (fun t _ => dom t)).trans
      (awayBound n u v l r p s (radius M) bPos hu hv withinU withinV hr hs))
  have dBound : d ≤ M :=
    (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (calc
      d^2 = d*d := by rw [pow_two]
      _ ≤ u*v := Nat.mul_le_mul (Nat.le_of_dvd hu (Nat.gcd_dvd_left _ _))
        (Nat.le_of_dvd hv (Nat.gcd_dvd_right _ _))
      _ ≤ M^2 := size)
  have exactNear := centered_deep_wave_product n M B H R u v l r p s (-(n : ℤ)) hn hu dBound
    cuts.2.2.1 width cuts.1 cuts.2.1 (cutoffR_covered n hn)
  have near : ‖∫ t in (0 : ℝ)..1, (grid ∩ deep).indicator F t‖ ≤
      (32 * (n : ℝ) / ((u : ℝ)*v)) * ∑ q ∈ d.divisors.filter (fun q => R < q), ‖ramanujan q (-(n : ℤ))‖ := by
    have nearEq : (∫ t in (0 : ℝ)..1, (grid ∩ deep).indicator F t) =
        ∑ q ∈ d.divisors.filter (fun q => R < q), ramanujan q (-(n : ℤ)) *
          ∫ t in window n M B H q, F t := by
      simpa only [grid, deep, d, F, Int.cast_neg] using exactNear
    rw [nearEq, mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun q _ => ?_)
    rw [norm_mul, mul_comm ‖ramanujan q (-(n : ℤ))‖]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [F, Int.cast_neg] using norm_common_window_pair_le n M B H q u v l r p s
      (-(n : ℤ)) hn hu hv size hr hs
  rw [split]
  exact (norm_add_le _ _).trans (add_le_add far near)

end

end B13NondividingResidueReductionProof

end

/- Joint short budget -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4ArcCenters DyadicMixedB4Ramanujan DyadicMixedB4ModulusTail
open DyadicMixedB4GcdHarmonic
open scoped Classical

noncomputable section

theorem ramanujan_inverse_square_tail (n R L : ℕ) (hn : 0 < n) (hR : 1 ≤ R) :
    (∑ q ∈ Icc (R+1) L, ‖ramanujan q (-(n : ℤ))‖ / (q : ℝ)^2) ≤
      (n.divisors.card : ℝ) * (2 / (R : ℝ)) := by
  let Q := Icc (R+1) L
  let term (d q : ℕ) : ℝ := if d ∣ q then d else 0
  have bound (q : ℕ) (hq : q ∈ Q) : ‖ramanujan q (-(n : ℤ))‖ ≤
      ∑ d ∈ n.divisors, term d q := by
    have q1 : 1 < q := hR.trans_lt (mem_Icc.mp hq).1
    have qp := zero_lt_one.trans q1
    letI : NeZero q := ⟨qp.ne'⟩
    rw [norm_ramanujan_neg]
    refine (norm_ramanujan_le_divisor_sum q1 n).trans_eq ?_
    rw [Nat.sum_div_divisors q (fun d => if d ∣ n then (d : ℝ) else 0),
      ← sum_filter, ← sum_filter]
    have eq : q.divisors.filter (fun d => d ∣ n) = n.divisors.filter (fun d => d ∣ q) := by
      ext d
      simp only [mem_filter, Nat.mem_divisors]
      exact ⟨fun ⟨⟨dq, _⟩, dn⟩ => ⟨⟨dn, hn.ne'⟩, dq⟩,
        fun ⟨⟨dn, _⟩, dq⟩ => ⟨⟨dq, qp.ne'⟩, dn⟩⟩
    rw [eq]
  have row (d : ℕ) (hd : d ∈ n.divisors) :
      (∑ q ∈ Q, term d q / (q : ℝ)^2) ≤ 2 / (R : ℝ) := by
    have dPos := Nat.pos_of_mem_divisors hd
    have dr : (0 : ℝ) < d := by exact_mod_cast dPos
    have rr : (0 : ℝ) < R := by exact_mod_cast (show 0 < R from hR)
    calc
      _ = (d : ℝ) * ∑ q ∈ Q.filter (fun q => d ∣ q), 1 / (q : ℝ)^2 := by
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun q _ => ?_
        by_cases h : d ∣ q <;> simp [term, h, div_eq_mul_inv]
      _ ≤ (d : ℝ) * (2 / ((d : ℝ) * ((max R d : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (inverse_square_multiples_tail d R L dPos) dr.le
      _ = 2 / ((max R d : ℕ) : ℝ) := by
        have pos : (0 : ℝ) < (max R d : ℕ) := by exact_mod_cast dPos.trans_le (le_max_right R d)
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) rr (by exact_mod_cast le_max_left R d)
  change (∑ q ∈ Q, ‖ramanujan q (-(n : ℤ))‖ / (q : ℝ)^2) ≤ _
  calc
    _ ≤ ∑ q ∈ Q, (∑ d ∈ n.divisors, term d q) / (q : ℝ)^2 :=
      sum_le_sum fun q hq => div_le_div_of_nonneg_right (bound q hq) (sq_nonneg _)
    _ = ∑ d ∈ n.divisors, ∑ q ∈ Q, term d q / (q : ℝ)^2 := by
      simp only [div_eq_mul_inv, sum_mul]
      exact sum_comm
    _ ≤ ∑ _ ∈ n.divisors, 2 / (R : ℝ) := sum_le_sum row
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem ramanujan_common_step_budget (n R : ℕ) (hn : 0 < n) (hR : 1 ≤ R) :
    (∑ u ∈ Icc 1 n, ∑ v ∈ Icc 1 n,
      (∑ q ∈ (u.gcd v).divisors.filter (fun q => R < q), ‖ramanujan q (-(n : ℤ))‖) /
        ((u : ℝ)*v)) ≤
      (1 + Real.log (n : ℝ))^2 * ((n.divisors.card : ℝ) * (2/(R : ℝ))) := by
  let Q := Icc (R+1) n
  let steps := Icc 1 n
  let mass (q : ℕ) := ‖ramanujan q (-(n : ℤ))‖
  let row (q u : ℕ) : ℝ := if q ∣ u then (u : ℝ)⁻¹ else 0
  let A := 1 + Real.log (n : ℝ)
  have row0 (q u : ℕ) : 0 ≤ row q u := by unfold row; split_ifs <;> positivity
  have pointwise (u v : ℕ) (hu : u ∈ steps) :
      (∑ q ∈ (u.gcd v).divisors.filter (fun q => R < q), mass q) / ((u : ℝ) * v) ≤
        ∑ q ∈ Q, mass q * row q u * row q v := by
    let ds := (u.gcd v).divisors.filter (fun q => R < q)
    have dsSubset : ds ⊆ Q := by
      intro q hq
      have ⟨div, large⟩ := mem_filter.mp hq
      have uPos := (mem_Icc.mp hu).1
      have qU := Nat.le_of_dvd uPos ((Nat.dvd_of_mem_divisors div).trans (Nat.gcd_dvd_left u v))
      exact mem_Icc.mpr ⟨large,qU.trans (mem_Icc.mp hu).2⟩
    calc
      _ = ∑ q ∈ ds, mass q * row q u * row q v := by
        rw [div_eq_mul_inv, sum_mul]
        refine sum_congr rfl fun q hq => ?_
        have divides := Nat.dvd_of_mem_divisors (mem_filter.mp hq).1
        rw [show row q u = (u : ℝ)⁻¹ from if_pos (divides.trans (Nat.gcd_dvd_left u v)),
          show row q v = (v : ℝ)⁻¹ from if_pos (divides.trans (Nat.gcd_dvd_right u v)), mul_inv_rev]
        ring
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg dsSubset (fun q _ _ =>
        mul_nonneg (mul_nonneg (norm_nonneg _) (row0 q u)) (row0 q v))
  have rowBound (q : ℕ) (hq : q ∈ Q) : (∑ u ∈ steps, row q u) ≤ (q : ℝ)⁻¹ * A := by
    have qPos : 0 < q := by have := (mem_Icc.mp hq).1; omega
    unfold row steps
    rw [← sum_filter, sum_inverse_multiples q n qPos]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self n q))
      (fun _ _ _ => by positivity)).trans ?_
    exact sum_inverse_Icc_le n
  have reorder :
      (∑ u ∈ steps, ∑ v ∈ steps, ∑ q ∈ Q, mass q * row q u * row q v) =
        ∑ q ∈ Q, mass q * (∑ u ∈ steps, row q u)^2 := by
    calc
      _ = ∑ u ∈ steps, ∑ q ∈ Q, ∑ v ∈ steps, mass q * row q u * row q v :=
        sum_congr rfl fun _ _ => sum_comm
      _ = ∑ q ∈ Q, ∑ u ∈ steps, ∑ v ∈ steps, mass q * row q u * row q v := sum_comm
      _ = _ := by
        refine sum_congr rfl fun q _ => ?_
        calc
          _ = ∑ u ∈ steps, (mass q * row q u) * (∑ v ∈ steps, row q v) :=
            sum_congr rfl fun u _ => (mul_sum _ _ _).symm
          _ = (∑ u ∈ steps, mass q * row q u) * (∑ v ∈ steps, row q v) := (sum_mul _ _ _).symm
          _ = _ := by rw [← mul_sum]; ring
  change (∑ u ∈ steps, ∑ v ∈ steps,
    (∑ q ∈ (u.gcd v).divisors.filter (fun q => R < q), mass q) / ((u : ℝ)*v)) ≤ _
  calc
    _ ≤ ∑ u ∈ steps, ∑ v ∈ steps, ∑ q ∈ Q, mass q * row q u * row q v :=
      sum_le_sum fun u hu => sum_le_sum fun v _ => pointwise u v hu
    _ = ∑ q ∈ Q, mass q * (∑ u ∈ steps, row q u)^2 := reorder
    _ ≤ ∑ q ∈ Q, mass q * ((q : ℝ)⁻¹ * A)^2 := by
      refine sum_le_sum fun q hq => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (sum_nonneg fun u _ => row0 q u) (rowBound q hq) _) (norm_nonneg _)
    _ = A^2 * ∑ q ∈ Q, mass q / (q : ℝ)^2 := by
      rw [mul_sum]
      refine sum_congr rfl fun q _ => ?_
      rw [mul_pow, inv_pow]
      rw [div_eq_mul_inv]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ramanujan_inverse_square_tail n R n hn hR) (sq_nonneg _)

end

end B13NondividingResidueReductionProof

end

/- Joint short aggregate -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4Scale
open DyadicMixedB4EnergyTail DyadicMixedB4GcdHarmonic
open scoped Classical

noncomputable section

def productStepBudget (n u v : ℕ) : ℝ :=
  128 * (logBudget n ^ 2 + (u.gcd v : ℝ) / ((u : ℝ) * v * radius (maximumStep n))) +
    (32 * (n : ℝ) / ((u : ℝ) * v)) *
      ∑ q ∈ (u.gcd v).divisors.filter (fun q => cutoffR n < q), ‖ramanujan q (-(n : ℤ))‖

theorem product_step_budget_nonneg (n u v : ℕ) : 0 ≤ productStepBudget n u v := by
  unfold productStepBudget radius
  positivity

private theorem sum_step_product_count (n K : ℕ) :
    (∑ u ∈ Icc 1 n, ∑ v ∈ Icc 1 n, if u*v ≤ K then (1 : ℝ) else 0) ≤
      (K : ℝ) * (1 + Real.log (n : ℝ)) := by
  have row (u : ℕ) (hu : u ∈ Icc 1 n) :
      (∑ v ∈ Icc 1 n, if u*v ≤ K then (1 : ℝ) else 0) ≤ (K : ℝ) / u := by
    let selected := (Icc 1 n).filter (fun v => u*v ≤ K)
    have subset : selected ⊆ Icc 1 (K / u) := by
      intro v hv
      obtain ⟨bound, product⟩ := mem_filter.mp hv
      exact mem_Icc.mpr ⟨(mem_Icc.mp bound).1, (Nat.le_div_iff_mul_le (mem_Icc.mp hu).1).mpr
        (by simpa only [Nat.mul_comm v u] using product)⟩
    have count : selected.card ≤ K/u :=
      (card_le_card subset).trans_eq (by simp)
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    calc
      _ ≤ ((K/u : ℕ) : ℝ) := by exact_mod_cast count
      _ ≤ _ := Nat.cast_div_le
  calc
    _ ≤ ∑ u ∈ Icc 1 n, (K : ℝ)/u := sum_le_sum row
    _ = (K : ℝ) * ∑ u ∈ Icc 1 n, (u : ℝ)⁻¹ := by simp only [div_eq_mul_inv, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inverse_Icc_le n) (Nat.cast_nonneg _)

theorem sum_product_step_budget_le (n : ℕ) (hn : 0 < n) :
    (∑ u ∈ Icc 1 n, ∑ v ∈ Icc 1 n,
      if u*v ≤ maximumStep n^2 then productStepBudget n u v else 0) ≤
      1152 * (maximumStep n : ℝ)^2 * logBudget n^3 +
        (64 * (n : ℝ) * (n.divisors.card : ℝ) * logBudget n^2) / cutoffR n := by
  let L := logBudget n
  let A := 1 + Real.log (n : ℝ)
  let M := maximumStep n
  let R := cutoffR n
  let S := Icc 1 n
  let count (u v : ℕ) : ℝ := if u*v ≤ M^2 then 1 else 0
  let gcdCost (u v : ℕ) : ℝ := (u.gcd v : ℝ) / ((u : ℝ)*v)
  let charCost (u v : ℕ) : ℝ :=
    (∑ q ∈ (u.gcd v).divisors.filter (fun q => R < q), ‖ramanujan q (-(n : ℤ))‖) / ((u : ℝ)*v)
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have A0 : 0 ≤ A := add_nonneg zero_le_one (Real.log_nonneg nOne)
  have AL : A ≤ L := by
    unfold A L logBudget
    gcongr
    linarith
  have Mp : 0 < M := (cutoffs_ordered n hn).1.trans ((cutoffs_ordered n hn).2.1.trans (cutoffs_ordered n hn).2.2.1)
  have rp : 1 ≤ R := (cutoffs_ordered n hn).1
  have mainPoint (u v : ℕ) (hu : u ∈ S) (hv : v ∈ S) :
      (if u*v ≤ M^2 then productStepBudget n u v else 0) ≤
        128 * L^2 * count u v + (1024 * (M : ℝ)^2) * gcdCost u v +
          (32 * (n : ℝ)) * charCost u v := by
    by_cases gate : u*v ≤ M^2
    · simp only [gate, ite_true]
      unfold productStepBudget count gcdCost charCost
      simp only [gate, ite_true]
      have uPos : (0 : ℝ) < u := by exact_mod_cast (show 0 < u from (mem_Icc.mp hu).1)
      have vPos : (0 : ℝ) < v := by exact_mod_cast (show 0 < v from (mem_Icc.mp hv).1)
      have mPos : (0 : ℝ) < M := by exact_mod_cast Mp
      change 128 * (L^2 + (u.gcd v : ℝ) / ((u : ℝ) * v * radius M)) +
        _ ≤ _
      unfold radius
      dsimp only [R]
      field_simp
      <;> ring_nf
      <;> norm_num
    · simp only [count, gate, ite_false, mul_zero, zero_add]
      unfold gcdCost charCost
      positivity
  have countBound : (∑ u ∈ S, ∑ v ∈ S, count u v) ≤ (M : ℝ)^2 * L := by
    refine (sum_step_product_count n (M^2)).trans ?_
    exact_mod_cast (show ((M^2 : ℕ) : ℝ) * A ≤ (M : ℝ)^2 * L from by push_cast; gcongr)
  have gcdBound : (∑ u ∈ S, ∑ v ∈ S, gcdCost u v) ≤ L^3 :=
    (gcd_reciprocal_sum_le n hn).trans (pow_le_pow_left₀ A0 AL _)
  have charBound : (∑ u ∈ S, ∑ v ∈ S, charCost u v) ≤ L^2 * ((n.divisors.card : ℝ) * (2/(R : ℝ))) :=
    (ramanujan_common_step_budget n R hn rp).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ A0 AL _) (by positivity))
  change (∑ u ∈ S, ∑ v ∈ S, if u*v ≤ M^2 then productStepBudget n u v else 0) ≤ _
  calc
    _ ≤ ∑ u ∈ S, ∑ v ∈ S, ((128*L^2)*count u v + (1024*(M : ℝ)^2)*gcdCost u v +
        (32*(n : ℝ))*charCost u v) :=
      sum_le_sum fun u hu => sum_le_sum fun v hv => mainPoint u v hu hv
    _ = (128*L^2) * (∑ u ∈ S, ∑ v ∈ S, count u v) +
        (1024*(M : ℝ)^2) * (∑ u ∈ S, ∑ v ∈ S, gcdCost u v) +
        (32*(n : ℝ)) * (∑ u ∈ S, ∑ v ∈ S, charCost u v) := by
      simp only [sum_add_distrib, ← mul_sum]
    _ ≤ (128*L^2)*((M : ℝ)^2*L) + (1024*(M : ℝ)^2)*L^3 +
        (32*(n : ℝ))*(L^2*((n.divisors.card : ℝ)*(2/(R : ℝ)))) := by
      gcongr
    _ = _ := by unfold L M R; ring

end

end B13NondividingResidueReductionProof

end

/- Joint short family -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

private theorem sum_step_columns {α β : Type*} (I : Finset α) (J : Finset β) (S : Finset ℕ)
    (u : α → ℕ) (v : β → ℕ) (a : α → ℝ) (b : β → ℝ) (F : ℕ → ℕ → ℝ)
    (uRange : ∀ i ∈ I, u i ∈ S) (vRange : ∀ j ∈ J, v j ∈ S) :
    (∑ i ∈ I, ∑ j ∈ J, a i * b j * F (u i) (v j)) =
      ∑ x ∈ S, ∑ y ∈ S, (∑ i ∈ I.filter (fun i => u i = x), a i) *
        (∑ j ∈ J.filter (fun j => v j = y), b j) * F x y := by
  calc
    _ = ∑ x ∈ S, ∑ i ∈ I.filter (fun i => u i = x), ∑ j ∈ J, a i * b j * F (u i) (v j) :=
      (sum_fiberwise_of_maps_to uRange _).symm
    _ = ∑ x ∈ S, ∑ y ∈ S, ∑ i ∈ I.filter (fun i => u i = x),
        ∑ j ∈ J.filter (fun j => v j = y), a i * b j * F (u i) (v j) := by
      refine sum_congr rfl fun x _ => ?_
      have split (i : α) : (∑ j ∈ J, a i * b j * F (u i) (v j)) =
          ∑ y ∈ S, ∑ j ∈ J.filter (fun j => v j = y), a i * b j * F (u i) (v j) :=
        (sum_fiberwise_of_maps_to vRange _).symm
      simp_rw [split]
      exact sum_comm
    _ = _ := by
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      rw [sum_mul_sum, sum_mul]
      refine sum_congr rfl fun i hi => ?_
      rw [sum_mul]
      refine sum_congr rfl fun j hj => ?_
      rw [(mem_filter.mp hi).2, (mem_filter.mp hj).2]

def shortProductFamily (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if u i * v j ≤ maximumStep n ^ 2 then
    a i * b j * productStepDeepIntegral n (u i) (v j) (l i) (r i) (p j) (s j) else 0

theorem norm_short_product_family_le (n : ℕ) (hn : 0 < n)
    (width : 4 * cutoffH n * maximumStep n ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) {W K : ℝ}
    (W0 : 0 ≤ W) (K0 : 0 ≤ K)
    (uRange : ∀ i ∈ I, u i ∈ Icc 1 n) (vRange : ∀ j ∈ J, v j ∈ Icc 1 n)
    (uEnds : ∀ i ∈ I, r i ≤ n / u i) (vEnds : ∀ j ∈ J, s j ≤ n / v j)
    (uBound : ∀ x ∈ Icc 1 n, (∑ i ∈ I.filter (fun i => u i = x), ‖a i‖) ≤ W)
    (vBound : ∀ y ∈ Icc 1 n, (∑ j ∈ J.filter (fun j => v j = y), ‖b j‖) ≤ K) :
    ‖shortProductFamily n I J u l r v p s a b‖ ≤
      (W * K) * (1152 * (maximumStep n : ℝ)^2 * logBudget n^3 +
        (64 * (n : ℝ) * (n.divisors.card : ℝ) * logBudget n^2) / cutoffR n) := by
  let F (x y : ℕ) := if x*y ≤ maximumStep n ^ 2 then productStepBudget n x y else 0
  have F0 (x y : ℕ) : 0 ≤ F x y := by
    unfold F
    split_ifs
    · exact product_step_budget_nonneg n x y
    · exact le_rfl
  have each (i : α) (hi : i ∈ I) (j : β) (hj : j ∈ J) :
      ‖if u i*v j ≤ maximumStep n^2 then
        a i * b j * productStepDeepIntegral n (u i) (v j) (l i) (r i) (p j) (s j) else 0‖ ≤
        ‖a i‖ * ‖b j‖ * F (u i) (v j) := by
    by_cases small : u i*v j ≤ maximumStep n^2
    · simp only [F, small, ite_true, norm_mul]
      obtain ⟨uPos,uN⟩ := mem_Icc.mp (uRange i hi)
      obtain ⟨vPos,vN⟩ := mem_Icc.mp (vRange j hj)
      exact mul_le_mul_of_nonneg_left (norm_product_step_deep_integral_le n (u i) (v j) (l i) (r i)
        (p j) (s j) hn uPos vPos uN vN small (uEnds i hi) (vEnds j hj) width) (by positivity)
    · simp [F, small]
  unfold shortProductFamily
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ‖if u i*v j ≤ maximumStep n^2 then
        a i * b j * productStepDeepIntegral n (u i) (v j) (l i) (r i) (p j) (s j) else 0‖ :=
      sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ‖a i‖ * ‖b j‖ * F (u i) (v j) :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => each i hi j hj
    _ = ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, (∑ i ∈ I.filter (fun i => u i = x), ‖a i‖) *
        (∑ j ∈ J.filter (fun j => v j = y), ‖b j‖) * F x y :=
      sum_step_columns I J (Icc 1 n) u v (fun i => ‖a i‖) (fun j => ‖b j‖) F uRange vRange
    _ ≤ ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, (W*K) * F x y := by
      refine sum_le_sum fun x hx => sum_le_sum fun y hy => ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul (uBound x hx) (vBound y hy)
        (sum_nonneg fun _ _ => norm_nonneg _) W0) (F0 x y)
    _ = (W*K) * ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, F x y := by simp only [← mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_product_step_budget_le n hn) (mul_nonneg W0 K0)

end

end B13NondividingResidueReductionProof

end

/- Joint actual waves -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4ArcDecomposition
open DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4MoebiusGauss
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

def bilateralLeftWaveItems (n : ℕ) : Finset (ℕ × ℕ) :=
  (leftLargeBilinearItems n).filter (fun i => leftBilinearStep i ≤ n)

theorem bilateral_left_wave_polynomial (n : ℕ) (t : ℝ) :
    leftBilinearPolynomial n (leftLargeBilinearItems n) t =
      leftBilinearPolynomial n (bilateralLeftWaveItems n) t := by
  unfold leftBilinearPolynomial bilateralLeftWaveItems
  symm
  refine sum_subset (filter_subset _ _) fun i hi outside => ?_
  have big : n < leftBilinearStep i := lt_of_not_ge fun small => outside (mem_filter.mpr ⟨hi,small⟩)
  simp [wave, Nat.div_eq_of_lt big]

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

end B13NondividingResidueReductionProof

end

/- Joint product partition -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4Scale
open DyadicMixedB4ArcDecomposition DyadicMixedB4OffWaveMoment DyadicMixedB4PairIntegral
open scoped Classical

noncomputable section

def longProductFamily (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if maximumStep n ^ 2 < u i * v j then
    a i * b j * productStepDeepIntegral n (u i) (v j) (l i) (r i) (p j) (s j) else 0

theorem two_wave_sums_partition (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) :
    (∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator
      (fun x => phase (((-(n : ℤ)) : ℝ)*x) *
        ((∑ i ∈ I, a i * wave (u i) (l i) (r i) x) *
          (∑ j ∈ J, b j * wave (v j) (p j) (s j) x))) t) =
      shortProductFamily n I J u l r v p s a b + longProductFamily n I J u l r v p s a b := by
  let domain := (wide n (cutoffB n) (cutoffH n))ᶜ
  let P (t : ℝ) := phase (((-(n : ℤ)) : ℝ)*t)
  let L (i : α) := wave (u i) (l i) (r i)
  let R (j : β) := wave (v j) (p j) (s j)
  let term (i : α) (j : β) (t : ℝ) :=
    a i * b j * domain.indicator (fun x => P x * (L i x * R j x)) t
  have pc : Continuous P := by unfold P phase; fun_prop
  have termInt (i : α) (j : β) : IntervalIntegrable (term i j) volume 0 1 :=
    (indicator_intervalIntegrable (pc.mul ((wave_continuous ..).mul (wave_continuous ..)))
      (wide_measurable ..).compl).const_mul _
  have rowInt (i : α) : IntervalIntegrable (fun t => ∑ j ∈ J, term i j t) volume 0 1 := by
    have good := IntervalIntegrable.sum J (fun j _ => termInt i j)
    convert good using 1
    funext t
    simp only [Finset.sum_apply]
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ i ∈ I, ∑ j ∈ J, term i j t := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      change domain.indicator (fun x => P x * ((∑ i ∈ I, a i * L i x) * (∑ j ∈ J, b j * R j x))) t = _
      by_cases inside : t ∈ domain
      · simp only [Set.indicator_of_mem inside, term]
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact sum_congr rfl fun j _ => by ring
      · simp [inside, term]
    _ = ∑ i ∈ I, ∑ j ∈ J,
        a i * b j * productStepDeepIntegral n (u i) (v j) (l i) (r i) (p j) (s j) := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => rowInt i)]
      refine sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finsetSum (fun j _ => termInt i j)]
      exact sum_congr rfl fun j _ => intervalIntegral.integral_const_mul ..
    _ = _ := by
      unfold shortProductFamily longProductFamily
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      by_cases short : u i * v j ≤ maximumStep n ^ 2
      · simp [short, not_lt_of_ge short]
      · simp [short, lt_of_not_ge short]

private def shortAgainstRight (n : ℕ) {ι : Type*} (items : Finset ι) (g l r : ι → ℕ) (w : ι → ℂ) : ℂ :=
  shortProductFamily n (bilateralLeftWaveItems n) items
    leftBilinearStep (fun i => cutoffU n/i.2) (fun i => n/leftBilinearStep i) g l r
    (leftBilinearWeight n) w

private def longAgainstRight (n : ℕ) {ι : Type*} (items : Finset ι) (g l r : ι → ℕ) (w : ι → ℂ) : ℂ :=
  longProductFamily n (bilateralLeftWaveItems n) items
    leftBilinearStep (fun i => cutoffU n/i.2) (fun i => n/leftBilinearStep i) g l r
    (leftBilinearWeight n) w

def bilateralShortProductContribution (n : ℕ) : ℂ :=
  shortAgainstRight n (rightLowWaveItems n) rightLowWaveStep (fun i => cutoffB n/i.2)
    (rightLowWaveUpper n) rightLowWaveWeight +
  shortAgainstRight n (rightHighWaveItems n) rightHighWaveStep (rightHighWaveLower n)
    (fun i => n/rightHighWaveStep i) (rightHighWaveWeight n)

def bilateralLongProductRemainder (n : ℕ) : ℂ :=
  longAgainstRight n (rightLowWaveItems n) rightLowWaveStep (fun i => cutoffB n/i.2)
    (rightLowWaveUpper n) rightLowWaveWeight +
  longAgainstRight n (rightHighWaveItems n) rightHighWaveStep (rightHighWaveLower n)
    (fun i => n/rightHighWaveStep i) (rightHighWaveWeight n)

theorem bilateralLargeLeftRemainder_eq_product_cut {n : ℕ} (hn : 0 < n) :
    bilateralLargeLeftRemainder n = bilateralLongProductRemainder n + bilateralShortProductContribution n := by
  let domain := (wide n (cutoffB n) (cutoffH n))ᶜ
  let P (t : ℝ) := phase (((-(n : ℤ)) : ℝ)*t)
  let l := leftBilinearPolynomial n (bilateralLeftWaveItems n)
  let J (r : ℝ → ℂ) := domain.indicator (fun x => P x * (l x * r x))
  have eq : bilateralLargeLeftRemainder n =
      ∫ t in (0 : ℝ)..1, J (fun x => rightLowPolynomial n x + rightHighPolynomial n x) t := by
    unfold bilateralLargeLeftRemainder doubleVaughanAfterLeftCut
    refine intervalIntegral.integral_congr fun t _ => ?_
    by_cases inside : t ∈ domain
    · change domain.indicator (fun x => shiftedPolynomial n _ x *
          leftBilinearPolynomial n (leftLargeBilinearItems n) x) t = _
      dsimp only [J]
      simp only [Set.indicator_of_mem inside, shiftedPolynomial_eq,
        right_residual_polynomial_eq_waves n hn t, bilateral_left_wave_polynomial]
      dsimp only [l, P]
      push_cast
      ring
    · exact (Set.indicator_of_notMem inside _).trans (Set.indicator_of_notMem inside _).symm
  have int (r : ℝ → ℂ) (rc : Continuous r) : IntervalIntegrable (J r) volume 0 1 := by
    have pc : Continuous P := by unfold P phase; fun_prop
    have lc : Continuous l := by
      unfold l leftBilinearPolynomial
      exact continuous_finsetSum _ (fun i _ => continuous_const.mul (wave_continuous ..))
    exact indicator_intervalIntegrable (pc.mul (lc.mul rc)) (wide_measurable ..).compl
  have lowC : Continuous (rightLowPolynomial n) := by
    unfold rightLowPolynomial
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (wave_continuous ..))
  have highC : Continuous (rightHighPolynomial n) := by
    unfold rightHighPolynomial
    exact continuous_finsetSum _ (fun i _ => continuous_const.mul (wave_continuous ..))
  have separate : (∫ t in (0 : ℝ)..1, J (fun x => rightLowPolynomial n x + rightHighPolynomial n x) t) =
      (∫ t in (0 : ℝ)..1, J (rightLowPolynomial n) t) +
        (∫ t in (0 : ℝ)..1, J (rightHighPolynomial n) t) := by
    rw [← intervalIntegral.integral_add (int _ lowC) (int _ highC)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    by_cases ht : t ∈ domain <;> simp [J, ht, mul_add]
  have low := two_wave_sums_partition n (bilateralLeftWaveItems n) (rightLowWaveItems n)
    leftBilinearStep (fun i => cutoffU n/i.2) (fun i => n/leftBilinearStep i)
    rightLowWaveStep (fun i => cutoffB n/i.2) (rightLowWaveUpper n)
    (leftBilinearWeight n) rightLowWaveWeight
  have high := two_wave_sums_partition n (bilateralLeftWaveItems n) (rightHighWaveItems n)
    leftBilinearStep (fun i => cutoffU n/i.2) (fun i => n/leftBilinearStep i)
    rightHighWaveStep (rightHighWaveLower n) (fun i => n/rightHighWaveStep i)
    (leftBilinearWeight n) (rightHighWaveWeight n)
  rw [eq, separate]
  unfold bilateralLongProductRemainder bilateralShortProductContribution longAgainstRight shortAgainstRight
  change (∫ t in (0 : ℝ)..1, J (rightLowPolynomial n) t) +
    (∫ t in (0 : ℝ)..1, J (rightHighPolynomial n) t) = _
  have lowEq : (∫ t in (0 : ℝ)..1, J (rightLowPolynomial n) t) = _ := low
  have highEq : (∫ t in (0 : ℝ)..1, J (rightHighPolynomial n) t) = _ := high
  rw [lowEq, highEq]
  abel

end

end B13NondividingResidueReductionProof

end

/- Joint product limit -/
section

namespace B13NondividingResidueReductionProof

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

end B13NondividingResidueReductionProof

end

/- Long lattice -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open DyadicMixedB4Fourier DyadicMixedB4ArcDecomposition DyadicMixedB4OffWaveMoment
open DyadicMixedB4Scale
open scoped Classical

noncomputable section

def progressionPairSolutions (n u v l r p s : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc l r ×ˢ Ioc p s).filter (fun i => u*i.1 + v*i.2 = n)

def productStepWideIntegral (n u v l r p s : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n)).indicator
    (fun x => phase (((-(n : ℤ)) : ℝ) * x) * (wave u l r x * wave v p s x)) t

private theorem integral_product_phase (n a b : ℕ) :
    (∫ t in (0 : ℝ)..1, phase (((-(n : ℤ)) : ℝ)*t) * (phase ((a:ℝ)*t) * phase ((b:ℝ)*t))) =
      if a+b=n then 1 else 0 := by
  let k : ℤ := (a : ℤ) + b - n
  have kZero : k = 0 ↔ a+b=n := by unfold k; omega
  have f (t : ℝ) : phase (((-(n : ℤ)) : ℝ)*t) * (phase ((a:ℝ)*t) * phase ((b:ℝ)*t)) = mode k t := by
    rw [← phase_add, ← phase_add]
    have same : ((-(n : ℤ) : ℤ) : ℝ)*t + ((a:ℝ)*t + (b:ℝ)*t) = (k : ℝ)*t := by
      dsimp [k]
      push_cast
      ring
    simp only [Int.cast_neg, Int.cast_natCast] at same ⊢
    rw [same]
    unfold phase mode frequency
    push_cast
    congr 1
    ring
  simp_rw [f]
  simp only [mode_integral, kZero]

theorem full_wave_pair_eq_count (n u v l r p s : ℕ) :
    (∫ t in (0 : ℝ)..1, phase (((-(n : ℤ)) : ℝ)*t) * (wave u l r t * wave v p s t)) =
      ((progressionPairSolutions n u v l r p s).card : ℂ) := by
  let term (a b : ℕ) (t : ℝ) := phase (((-(n : ℤ)) : ℝ)*t) *
    (phase ((((u*a : ℕ) : ℝ))*t) * phase ((((v*b : ℕ) : ℝ))*t))
  have tc (a b : ℕ) : Continuous (term a b) := by unfold term phase; fun_prop
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ i ∈ Ioc l r ×ˢ Ioc p s, term i.1 i.2 t := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [wave, wave, Finset.sum_product, Finset.sum_mul_sum, Finset.mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    _ = ∑ i ∈ Ioc l r ×ˢ Ioc p s, if u*i.1 + v*i.2 = n then (1 : ℂ) else 0 := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => (tc i.1 i.2).intervalIntegrable 0 1)]
      exact sum_congr rfl fun i _ => integral_product_phase n (u*i.1) (v*i.2)
    _ = _ := by
      unfold progressionPairSolutions
      rw [← sum_filter, sum_const]
      simp

theorem deep_wave_pair_eq_count_sub_wide (n u v l r p s : ℕ) :
    productStepDeepIntegral n u v l r p s =
      ((progressionPairSolutions n u v l r p s).card : ℂ) - productStepWideIntegral n u v l r p s := by
  let W := wide n (cutoffB n) (cutoffH n)
  let F (t : ℝ) := phase (((-(n : ℤ)) : ℝ)*t) * (wave u l r t * wave v p s t)
  have pc : Continuous (fun t : ℝ => phase (((-(n : ℤ)) : ℝ)*t)) := by unfold phase; fun_prop
  have fc : Continuous F := pc.mul ((wave_continuous ..).mul (wave_continuous ..))
  have split : (∫ t in (0 : ℝ)..1, Wᶜ.indicator F t) + (∫ t in (0 : ℝ)..1, W.indicator F t) =
      ∫ t in (0 : ℝ)..1, F t := by
    rw [← intervalIntegral.integral_add (indicator_intervalIntegrable fc (wide_measurable ..).compl)
      (indicator_intervalIntegrable fc (wide_measurable ..))]
    refine intervalIntegral.integral_congr fun t _ => ?_
    by_cases h : t ∈ W <;> simp [h]
  unfold productStepDeepIntegral productStepWideIntegral
  exact eq_sub_of_add_eq (split.trans (full_wave_pair_eq_count n u v l r p s))

theorem progression_pair_empty_of_not_gcd_dvd {n u v l r p s : ℕ} (hn : ¬u.gcd v ∣ n) :
    progressionPairSolutions n u v l r p s = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  have eq := (mem_filter.mp hi).2
  exact hn (eq ▸ dvd_add ((Nat.gcd_dvd_left u v).trans (dvd_mul_right u i.1))
    ((Nat.gcd_dvd_right u v).trans (dvd_mul_right v i.2)))

end

end B13NondividingResidueReductionProof

end

/- Residue count -/
section

namespace B13NondividingResidueReductionProof

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

end B13NondividingResidueReductionProof

end

/- Residue error -/
section

namespace B13NondividingResidueReductionProof

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

end

end B13NondividingResidueReductionProof

end

/- Wide noncommon point -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Geometric DyadicMixedB4GcdHarmonic
open scoped Classical

noncomputable section

private theorem two_mul_min_le_sin_pi {x : ℝ} (x0 : 0 ≤ x) (x1 : x ≤ 1) :
    2*min x (1-x) ≤ Real.sin (Real.pi*x) := by
  let y := min x (1-x)
  have y0 : 0 ≤ y := le_min x0 (sub_nonneg.mpr x1)
  have y1 : y ≤ 1/2 := by
    have a : y ≤ x := min_le_left _ _
    have b : y ≤ 1-x := min_le_right _ _
    linarith only [a,b]
  have same : Real.sin (Real.pi*x) = Real.sin (Real.pi*y) := by
    by_cases side : x ≤ 1-x
    · rw [show y = x from min_eq_left side]
    · rw [show y = 1-x from min_eq_right (le_of_not_ge side),mul_sub,mul_one,Real.sin_pi_sub]
  rw [same]
  change 2*y ≤ Real.sin (Real.pi*y)
  calc
    _ = 2/Real.pi*(Real.pi*y) := by field_simp
    _ ≤ _ := Real.mul_le_sin (mul_nonneg Real.pi_pos.le y0)
      (by nlinarith only [y1,Real.pi_pos])

theorem norm_wave_near_nondividing_rational_le {q a u l r : ℕ} (hq : 0 < q)
    {t : ℝ} (hclose : |(u : ℝ)*(t-(a : ℝ)/q)| ≤ 1/(2*(q : ℝ)))
    (hres : (u*a)%q ≠ 0) :
    ‖wave u l r t‖ ≤ (q : ℝ)/min ((u*a)%q) (q-(u*a)%q) := by
  let j := (u*a)/q
  let k := (u*a)%q
  let V : ℝ := (u : ℝ)*(t-(a : ℝ)/q)
  let x : ℝ := (k : ℝ)/q + V
  let D : ℝ := (min k (q-k) : ℕ)
  have qr : (0 : ℝ) < q := by exact_mod_cast hq
  have kNat := Nat.mod_lt (u*a) hq
  have k1 : (1 : ℝ) ≤ k := by
    change (1 : ℝ) ≤ (((u*a)%q : ℕ) : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero hres
  have k2 : (k : ℝ)+1 ≤ (q : ℝ) := by
    change (((u*a)%q : ℕ) : ℝ)+1 ≤ (q : ℝ)
    exact_mod_cast Nat.succ_le_of_lt kNat
  have Dp : 0 < D := by
    unfold D
    exact_mod_cast (lt_min (Nat.pos_of_ne_zero hres) (Nat.sub_pos_of_lt kNat))
  have sum : (u : ℝ)*t = (j : ℝ)+x := by
    have decomp : (q : ℝ)*(j : ℝ)+(k : ℝ) = (u : ℝ)*a := by
      unfold j k
      exact_mod_cast Nat.div_add_mod (u*a) q
    have decomp' : (u : ℝ)*a/q = (j : ℝ)+(k : ℝ)/q := by
      apply (div_eq_iff qr.ne').mpr
      field_simp
      linear_combination -decomp
    unfold x V
    rw [mul_sub,← mul_div_assoc,decomp']
    ring
  have close := abs_le.mp hclose
  have lower : (k : ℝ)/(2*(q : ℝ)) ≤ x := by
    have half : (k : ℝ)/(2*(q : ℝ)) + 1/(2*(q : ℝ)) ≤ (k : ℝ)/q := by
      rw [← add_div]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*q)).mpr
      have e : (k : ℝ)/q*(2*(q : ℝ)) = 2*(k : ℝ) := by field_simp
      rw [e]
      linarith only [k1]
    linarith only [half,close.1]
  have upper : ((q : ℝ)-(k : ℝ))/(2*(q : ℝ)) ≤ 1-x := by
    have half : ((q : ℝ)-(k : ℝ))/(2*(q : ℝ)) + 1/(2*(q : ℝ)) ≤ 1-(k : ℝ)/q := by
      rw [← add_div]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*q)).mpr
      have e : (1-(k : ℝ)/q)*(2*(q : ℝ)) = 2*((q : ℝ)-(k : ℝ)) := by field_simp
      rw [e]
      linarith only [k2]
    linarith only [half,close.2]
  have x0 : 0 ≤ x := (by positivity : 0 ≤ (k : ℝ)/(2*(q : ℝ))).trans lower
  have x1 : x ≤ 1 := by
    have qk : 0 ≤ (q : ℝ)-(k : ℝ) := by linarith only [k2]
    exact sub_nonneg.mp ((div_nonneg qk (by positivity)).trans upper)
  have sinLower : D/(q : ℝ) ≤ Real.sin (Real.pi*x) := by
    have bound : D/(2*(q : ℝ)) ≤ min x (1-x) := by
      unfold D
      rw [Nat.cast_min,Nat.cast_sub kNat.le,← min_div_div_right (by positivity : (0 : ℝ) ≤ 2*q)]
      exact le_min ((min_le_left _ _).trans lower) ((min_le_right _ _).trans upper)
    have id : D/(q : ℝ) = 2*(D/(2*(q : ℝ))) := by ring
    rw [id]
    exact (mul_le_mul_of_nonneg_left bound (by norm_num)).trans (two_mul_min_le_sin_pi x0 x1)
  have period : |Real.sin (Real.pi*((u : ℝ)*t))| = |Real.sin (Real.pi*x)| := by
    rw [sum,mul_add,add_comm,mul_comm Real.pi (j : ℝ),Real.sin_add_nat_mul_pi,abs_mul,abs_pow]
    simp
  have positive : 0 < D/(q : ℝ) := div_pos Dp qr
  have needed : 0 < |Real.sin (Real.pi*((u : ℝ)*t))| := by
    rw [period]
    exact positive.trans_le (sinLower.trans (le_abs_self _))
  refine (wave_sin u l r t (abs_pos.mp needed)).trans ?_
  rw [period]
  calc
    _ ≤ 1/(D/(q : ℝ)) := div_le_div_of_nonneg_left zero_le_one positive (sinLower.trans (le_abs_self _))
    _ = _ := by unfold D k; rw [one_div,inv_div]

end

end B13NondividingResidueReductionProof

end

/- Wide noncommon rows -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Geometric DyadicMixedB4GcdHarmonic
open scoped Classical

noncomputable section

private theorem sum_inverse_reflected_min_le (q : ℕ) :
    (∑ r ∈ Icc 1 (q-1), (1 : ℝ)/min r (q-r)) ≤ 2*(1+Real.log (q : ℝ)) := by
  let S := Icc 1 (q-1)
  have h r (hr : r ∈ S) : (1 : ℝ)/min r (q-r) ≤ 1/(r : ℝ) + 1/((q-r : ℕ) : ℝ) := by
    by_cases order : r ≤ q-r
    · rw [min_eq_left order]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right (le_of_not_ge order)]
      exact le_add_of_nonneg_left (by positivity)
  have mirror : (∑ r ∈ S, (1 : ℝ)/((q-r : ℕ) : ℝ)) = ∑ r ∈ S, (1 : ℝ)/r := by
    apply sum_bij (fun r _ => q-r)
    · intro r hr
      obtain ⟨low,high⟩ := mem_Icc.mp hr
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    · intro a ha b hb same
      have ha' := (mem_Icc.mp ha).2
      have hb' := (mem_Icc.mp hb).2
      omega
    · intro r hr
      obtain ⟨low,high⟩ := mem_Icc.mp hr
      exact ⟨q-r, mem_Icc.mpr ⟨by omega,by omega⟩, by omega⟩
    · intro r hr
      rfl
  refine (sum_le_sum h).trans ?_
  rw [sum_add_distrib,mirror]
  have one : (∑ r ∈ S,(1 : ℝ)/r) ≤ 1+Real.log (q : ℝ) := by
    simpa only [one_div] using
      (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.sub_le q 1))
        (fun r _ _ => inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) r))).trans (sum_inverse_Icc_le q)
  linarith only [one]

private theorem rational_residue_fiber_card_le {A q a r : ℕ} (qPos : 0 < q) (cop : a.Coprime q) :
    ((Icc 1 A).filter (fun u => (u*a)%q = r)).card ≤ A/q + 1 := by
  let S := (Icc 1 A).filter (fun u => (u*a)%q = r)
  have count : S.card ≤ (range (A/q+1)).card := by
    apply card_le_card_of_injOn (fun u => u/q)
    · intro u hu
      exact mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hu).1).2))
    · intro u hu v hv quotient
      change u / q = v / q at quotient
      have congruent : a*u ≡ a*v [MOD q] := by
        change (a*u)%q = (a*v)%q
        rw [Nat.mul_comm a u,Nat.mul_comm a v,(mem_filter.mp hu).2,(mem_filter.mp hv).2]
      have mod : u % q = v % q := by
        have reduced := Nat.ModEq.cancel_left_div_gcd qPos congruent
        simpa only [Nat.gcd_comm q a,cop.gcd_eq_one,Nat.div_one,Nat.ModEq] using reduced
      have uRepr := Nat.div_add_mod u q
      have vRepr := Nat.div_add_mod v q
      rw [quotient,mod,vRepr] at uRepr
      exact uRepr.symm
  simpa only [card_range] using count

theorem sum_nondividing_rational_bounds_le (A q a : ℕ) (qPos : 0 < q) (cop : a.Coprime q) :
    (∑ u ∈ (Icc 1 A).filter (fun u => (u*a)%q ≠ 0),
      (q : ℝ)/min ((u*a)%q) (q-(u*a)%q)) ≤
      2*((A : ℝ)+q)*(1+Real.log (q : ℝ)) := by
  let S := (Icc 1 A).filter (fun u => (u*a)%q ≠ 0)
  let G := Icc 1 (q-1)
  let f (r : ℕ) := (1 : ℝ)/min r (q-r)
  have f0 r : 0 ≤ f r := by unfold f; positivity
  have qr : (0 : ℝ) < q := by exact_mod_cast qPos
  have hr u (hu : u ∈ S) : (u*a)%q ∈ G := by
    obtain ⟨_,nonzero⟩ := mem_filter.mp hu
    have lt := Nat.mod_lt (u*a) qPos
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have subset r : S.filter (fun u => (u*a)%q=r) ⊆ (Icc 1 A).filter (fun u => (u*a)%q=r) :=
    filter_subset_filter _ (filter_subset _ _)
  have bound (r : ℕ) (rMem : r ∈ G) :
      (∑ u ∈ S.filter (fun u => (u*a)%q = r), (q : ℝ)*f ((u*a)%q)) ≤
        ((A : ℝ)+q)*f r := by
    have uniform : (∑ u ∈ S.filter (fun u => (u*a)%q = r), (q : ℝ)*f ((u*a)%q)) =
        (∑ _ ∈ S.filter (fun u => (u*a)%q = r), (q : ℝ)*f r) := by
      exact sum_congr rfl fun u hu => by rw [(mem_filter.mp hu).2]
    rw [uniform,sum_const,nsmul_eq_mul,← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (f0 r)
    have card : ((S.filter (fun u => (u*a)%q = r)).card : ℝ) ≤ ((A/q + 1 : ℕ) : ℝ) := by
      exact_mod_cast (card_le_card (subset r)).trans (rational_residue_fiber_card_le qPos cop)
    calc
      _ ≤ ((A/q+1 : ℕ) : ℝ)*(q : ℝ) := mul_le_mul_of_nonneg_right card qr.le
      _ ≤ ((A : ℝ)/q+1)*(q : ℝ) := by
        rw [Nat.cast_add,Nat.cast_one]
        exact mul_le_mul_of_nonneg_right (add_le_add (Nat.cast_div_le (α := ℝ)) le_rfl) qr.le
      _ = _ := by field_simp
  calc
    _ = ∑ u ∈ S, (q : ℝ)*f ((u*a)%q) := by
      unfold S f
      refine sum_congr rfl fun u _ => ?_
      ring
    _ = ∑ r ∈ G, ∑ u ∈ S.filter (fun u => (u*a)%q = r), (q : ℝ)*f ((u*a)%q) :=
      (sum_fiberwise_of_maps_to hr _).symm
    _ ≤ ∑ r ∈ G, ((A : ℝ)+q)*f r := sum_le_sum bound
    _ = ((A : ℝ)+q) * ∑ r ∈ G, f r := (mul_sum ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (sum_inverse_reflected_min_le q) (by positivity)).trans_eq (by ring)

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

end B13NondividingResidueReductionProof

end

/- Wide noncommon weighted -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Geometric DyadicMixedB4ArcCenters
open scoped Classical

noncomputable section

def waveNormRow {ι : Type*} (I : Finset ι) (g l r : ι → ℕ) (c : ι → ℂ)
    (predicate : ℕ → Prop) [DecidablePred predicate] (t : ℝ) : ℝ :=
  ∑ i ∈ I.filter (fun i => predicate (g i)), ‖c i‖ * ‖wave (g i) (l i) (r i) t‖

private theorem norm_row_le_of_bound {ι : Type*} (I : Finset ι) (S : Finset ℕ) (g l r : ι → ℕ)
    (c : ι → ℂ) (P : ℕ → Prop) [DecidablePred P] (F : ℕ → ℝ) (t : ℝ) {W : ℝ}
    (range : ∀ i ∈ I.filter (fun i => P (g i)), g i ∈ S)
    (each : ∀ i ∈ I.filter (fun i => P (g i)), ‖wave (g i) (l i) (r i) t‖ ≤ F (g i))
    (f0 : ∀ u ∈ S, 0 ≤ F u)
    (mass : ∀ u ∈ S, (∑ i ∈ I.filter (fun i => g i=u), ‖c i‖) ≤ W) :
    waveNormRow I g l r c P t ≤ W * ∑ u ∈ S, F u := by
  let J := I.filter fun i => P (g i)
  unfold waveNormRow
  calc
    _ ≤ ∑ i ∈ J, ‖c i‖ * F (g i) :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (each i hi) (norm_nonneg _)
    _ = ∑ u ∈ S, (∑ i ∈ J.filter (fun i => g i=u), ‖c i‖) * F u := by
      rw [← sum_fiberwise_of_maps_to range (fun i => ‖c i‖*F (g i))]
      refine sum_congr rfl fun u _ => ?_
      rw [sum_mul]
      exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
    _ ≤ ∑ u ∈ S, W*F u := by
      refine sum_le_sum fun u hu => mul_le_mul_of_nonneg_right ?_ (f0 u hu)
      exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
        (fun _ _ _ => norm_nonneg _)).trans (mass u hu)
    _ = _ := (mul_sum ..).symm

theorem wave_norm_row_nondividing_le (n A H q a : ℕ)
    (hn : 0 < n) (hq : 0 < q) (cop : a.Coprime q) (geometric : 2*H*A ≤ n)
    {ι : Type*} (I : Finset ι) (g l r : ι → ℕ) (c : ι → ℂ)
    (steps : ∀ i ∈ I, g i ∈ Icc 1 A)
    {W : ℝ} (W0 : 0 ≤ W)
    (mass : ∀ u ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => g i=u), ‖c i‖) ≤ W)
    {t : ℝ} (ht : |t-(a : ℝ)/q| ≤ (H : ℝ)/((q : ℝ)*n)) :
    waveNormRow I g l r c (fun u => ¬q∣u) t ≤ W * (2*((A : ℝ)+q)*(1+Real.log (q : ℝ))) := by
  let S := (Icc 1 A).filter fun u => (u*a)%q ≠ 0
  let F (u : ℕ) := (q : ℝ)/min ((u*a)%q) (q-(u*a)%q)
  have hres (u : ℕ) (hu : ¬ q∣u) : (u*a)%q ≠ 0 := by
    intro zero
    have h := Nat.dvd_of_mod_eq_zero zero
    exact hu (cop.symm.dvd_of_dvd_mul_right h)
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have qr : (0 : ℝ) < q := by exact_mod_cast hq
  have good (i : ι) (hi : i ∈ I.filter (fun i => ¬q∣g i)) :
      ‖wave (g i) (l i) (r i) t‖ ≤ F (g i) := by
    have step : (g i : ℝ) ≤ A := by exact_mod_cast (mem_Icc.mp (steps i (mem_filter.mp hi).1)).2
    have cap : 2*(H : ℝ)*(g i : ℝ) ≤ n :=
      (mul_le_mul_of_nonneg_left step (by positivity : (0 : ℝ) ≤ 2*H)).trans (by exact_mod_cast geometric)
    apply norm_wave_near_nondividing_rational_le hq ?_ (hres _ (mem_filter.mp hi).2)
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    refine (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (g i))).trans ?_
    calc
      _ = (2*(H : ℝ)*(g i : ℝ))/(2*(q : ℝ)*(n : ℝ)) := by ring
      _ ≤ (n : ℝ)/(2*(q : ℝ)*(n : ℝ)) := div_le_div_of_nonneg_right cap (by positivity)
      _ = _ := by field_simp
  have estimate := norm_row_le_of_bound I S g l r c (fun u => ¬q∣u) F t
    (fun i hi => mem_filter.mpr ⟨steps i (mem_filter.mp hi).1,hres _ (mem_filter.mp hi).2⟩)
    good (fun _ _ => by unfold F; positivity) (fun u hu => mass u (mem_filter.mp hu).1)
  exact estimate.trans (mul_le_mul_of_nonneg_left (sum_nondividing_rational_bounds_le A q a hq cop) W0)

theorem wave_norm_row_dividing_le (n A q : ℕ) (hq : 0 < q)
    {ι : Type*} (I : Finset ι) (g l r : ι → ℕ) (c : ι → ℂ)
    (steps : ∀ i ∈ I, g i ∈ Icc 1 A) (endpoints : ∀ i ∈ I, r i ≤ n/g i)
    {W : ℝ} (W0 : 0 ≤ W)
    (mass : ∀ u ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => g i=u), ‖c i‖) ≤ W) (t : ℝ) :
    waveNormRow I g l r c (fun u => q∣u) t ≤ W * ((n : ℝ)/q*(1+Real.log (A : ℝ))) := by
  have estimate := norm_row_le_of_bound I ((Icc 1 A).filter (fun u => q∣u)) g l r c
    (fun u => q∣u) (fun u => (n : ℝ)/u) t
    (fun i hi => mem_filter.mpr ⟨steps i (mem_filter.mp hi).1,(mem_filter.mp hi).2⟩)
    (fun i hi => (wave_cap ..).trans ((by exact_mod_cast endpoints i (mem_filter.mp hi).1 :
      (r i : ℝ) ≤ ((n/g i : ℕ) : ℝ)).trans Nat.cast_div_le))
    (fun _ _ => by positivity) (fun u hu => mass u (mem_filter.mp hu).1)
  exact estimate.trans (mul_le_mul_of_nonneg_left (sum_dividing_rational_bounds_le n A q hq) W0)

end

end B13NondividingResidueReductionProof

end

/- Wide arc partition -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open DyadicMixedB4ArcDecomposition DyadicMixedB4OffWaveMoment
open scoped Classical

noncomputable section

def wideArc (n H q a : ℕ) : Set ℝ :=
  {t | |t-(a : ℝ)/q| ≤ (H : ℝ)/((q : ℝ)*n)}

theorem wide_arc_measurable (n H q a : ℕ) : MeasurableSet (wideArc n H q a) :=
  measurableSet_le (continuous_id.sub continuous_const).abs.measurable measurable_const

private theorem mem_wide_iff_arc (n B H : ℕ) (t : ℝ) :
    t ∈ wide n B H ↔ ∃ q ∈ Icc 1 B, ∃ a ∈ numSet q, t ∈ wideArc n H q a := by
  constructor
  · rintro ⟨q,a,q1,qB,aBound,coprime,near⟩
    exact ⟨q,mem_Icc.mpr ⟨q1,qB⟩,a,mem_filter.mpr
      ⟨mem_range.mpr (Nat.lt_succ_of_le aBound),coprime⟩,near⟩
  · rintro ⟨q,qMem,a,aMem,near⟩
    obtain ⟨q1,qB⟩ := mem_Icc.mp qMem
    obtain ⟨aRange,coprime⟩ := mem_filter.mp aMem
    exact ⟨q,a,q1,qB,Nat.le_of_lt_succ (mem_range.mp aRange),coprime,near⟩

private theorem rational_centers_separated {a b q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (different : a*r ≠ b*q) : 1/((q : ℝ)*r) ≤ |(a : ℝ)/q-(b : ℝ)/r| := by
  have qr : (0 : ℝ) < q := by exact_mod_cast hq
  have rr : (0 : ℝ) < r := by exact_mod_cast hr
  rw [show (a : ℝ)/q-(b : ℝ)/r = ((a : ℝ)*r-(b : ℝ)*q)/((q : ℝ)*r) by field_simp,
    abs_div, abs_of_pos (mul_pos qr rr)]
  apply (div_le_div_iff_of_pos_right (mul_pos qr rr)).mpr
  rcases lt_or_gt_of_ne different with ab | ba
  · have gap : (a : ℝ)*r+1 ≤ (b : ℝ)*q := by exact_mod_cast Nat.succ_le_of_lt ab
    linarith only [gap,neg_le_abs ((a : ℝ)*r-(b : ℝ)*q)]
  · have gap : (b : ℝ)*q+1 ≤ (a : ℝ)*r := by exact_mod_cast Nat.succ_le_of_lt ba
    linarith only [gap,le_abs_self ((a : ℝ)*r-(b : ℝ)*q)]

private theorem wide_arcs_unique {n B H q a r b : ℕ} (hn : 0 < n) (thin : 4*H*B ≤ n)
    (hq : q ∈ Icc 1 B) (hr : r ∈ Icc 1 B) (ha : a ∈ numSet q) (hb : b ∈ numSet r)
    {t : ℝ} (hitq : t ∈ wideArc n H q a) (hitr : t ∈ wideArc n H r b) :
    q=r ∧ a=b := by
  have qp : 0 < q := (mem_Icc.mp hq).1
  have rp : 0 < r := (mem_Icc.mp hr).1
  have qr : (0 : ℝ) < q := by exact_mod_cast qp
  have rr : (0 : ℝ) < r := by exact_mod_cast rp
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have hThin (v : ℕ) (bound : v ≤ B) : 4*(H : ℝ)*(v : ℝ) ≤ n := by
    exact_mod_cast (Nat.mul_le_mul_left (4*H) bound).trans thin
  have dl : |t-(a : ℝ)/q| ≤ 1/(4*(q : ℝ)*r) := by
    refine hitq.trans ?_
    apply (div_le_div_iff₀ (mul_pos qr nr) (by positivity)).mpr
    have eq : (H : ℝ)*(4*(q : ℝ)*r) = (q : ℝ)*(4*(H : ℝ)*r) := by ring
    rw [eq,one_mul]
    exact mul_le_mul_of_nonneg_left (hThin r (mem_Icc.mp hr).2) qr.le
  have dr : |t-(b : ℝ)/r| ≤ 1/(4*(q : ℝ)*r) := by
    refine hitr.trans ?_
    apply (div_le_div_iff₀ (mul_pos rr nr) (by positivity)).mpr
    have eq : (H : ℝ)*(4*(q : ℝ)*r) = (r : ℝ)*(4*(H : ℝ)*q) := by ring
    rw [eq,one_mul]
    exact mul_le_mul_of_nonneg_left (hThin q (mem_Icc.mp hq).2) rr.le
  have same : a*r=b*q := by
    by_contra apart
    have separation := rational_centers_separated qp rp apart
    have triangle := abs_sub_le ((a : ℝ)/q) t ((b : ℝ)/r)
    rw [abs_sub_comm ((a : ℝ)/q) t] at triangle
    have scale : 1/((q : ℝ)*r) = 4*(1/(4*(q : ℝ)*r)) := by ring
    rw [scale] at separation
    linarith only [separation,triangle,dl,dr,show 0 < 1/(4*(q : ℝ)*r) by positivity]
  have left : q∣a*r := same ▸ Nat.dvd_mul_left q b
  have right : r∣b*q := same.symm ▸ Nat.dvd_mul_left r a
  have eq := Nat.dvd_antisymm ((mem_filter.mp ha).2.symm.dvd_of_dvd_mul_left left)
    ((mem_filter.mp hb).2.symm.dvd_of_dvd_mul_left right)
  subst r
  exact ⟨rfl,Nat.eq_of_mul_eq_mul_right qp same⟩

theorem wide_indicator_eq_arcs {n B H : ℕ} (hn : 0 < n) (thin : 4*H*B ≤ n)
    (F : ℝ → ℂ) (t : ℝ) :
    (wide n B H).indicator F t = ∑ q ∈ Icc 1 B, ∑ a ∈ numSet q, (wideArc n H q a).indicator F t := by
  have describe := mem_wide_iff_arc n B H t
  by_cases hit : t ∈ wide n B H
  · obtain ⟨q,qMem,a,aMem,inside⟩ := describe.mp hit
    rw [Set.indicator_of_mem hit, sum_eq_single_of_mem q qMem]
    · rw [sum_eq_single_of_mem a aMem, Set.indicator_of_mem inside]
      intro b bMem ne
      exact Set.indicator_of_notMem (fun hitB => ne (wide_arcs_unique hn thin qMem qMem bMem aMem hitB inside).2) _
    · intro r rMem ne
      exact sum_eq_zero fun b bMem =>
        Set.indicator_of_notMem (fun hitB => ne (wide_arcs_unique hn thin rMem qMem bMem aMem hitB inside).1) _
  · rw [Set.indicator_of_notMem hit]
    symm
    exact sum_eq_zero fun q qMem => sum_eq_zero fun a aMem =>
      Set.indicator_of_notMem (fun near => hit (describe.mpr ⟨q,qMem,a,aMem,near⟩)) _

theorem wide_integral_eq_arcs {n B H : ℕ} (hn : 0 < n) (thin : 4*H*B ≤ n)
    {F : ℝ → ℂ} (fc : Continuous F) :
    (∫ t in (0 : ℝ)..1, (wide n B H).indicator F t) =
      ∑ q ∈ Icc 1 B, ∑ a ∈ numSet q, ∫ t in (0 : ℝ)..1, (wideArc n H q a).indicator F t := by
  simp_rw [wide_indicator_eq_arcs hn thin]
  have each (q a : ℕ) : IntervalIntegrable ((wideArc n H q a).indicator F) volume 0 1 :=
    indicator_intervalIntegrable fc (wide_arc_measurable ..)
  have row (q : ℕ) : IntervalIntegrable (fun t => ∑ a ∈ numSet q, (wideArc n H q a).indicator F t) volume 0 1 := by
    have eq : (∑ a ∈ numSet q, (wideArc n H q a).indicator F) =
        fun t => ∑ a ∈ numSet q, (wideArc n H q a).indicator F t := by
      funext t
      let evaluation : (ℝ → ℂ) →+ ℂ := ⟨⟨fun f => f t, rfl⟩, fun _ _ => rfl⟩
      exact map_sum evaluation (fun a => (wideArc n H q a).indicator F) (numSet q)
    rw [← eq]
    exact IntervalIntegrable.sum (numSet q) (fun a _ => each q a)
  rw [intervalIntegral.integral_finsetSum (fun q _ => row q)]
  exact sum_congr rfl fun q _ => intervalIntegral.integral_finsetSum (fun a _ => each q a)

end

end B13NondividingResidueReductionProof

end

/- Wide noncommon pair -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open DyadicMixedB4OffWaveMoment DyadicMixedB4ArcDecomposition DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def noncommonWaveProduct (n q : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ)
    (gate : α → β → Prop) (t : ℝ) : ℂ :=
  phase (((-(n : ℤ)) : ℝ)*t) * ∑ i ∈ I, ∑ j ∈ J, if gate i j ∧ ¬(q∣u i ∧ q∣v j) then
    (a i * wave (u i) (l i) (r i) t) * (b j * wave (v j) (p j) (s j) t) else 0

theorem noncommon_wave_product_continuous (n q : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) :
    Continuous (noncommonWaveProduct n q I J u l r v p s a b gate) := by
  have pc : Continuous (fun t : ℝ => phase (((-(n : ℤ)) : ℝ)*t)) := by unfold phase; fun_prop
  apply pc.mul
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  by_cases h : gate i j ∧ ¬(q∣u i ∧ q∣v j)
  · simp only [ite_eq_left h]
    change Continuous (((fun _ : ℝ => a i) * wave (u i) (l i) (r i)) *
      ((fun _ : ℝ => b j) * wave (v j) (p j) (s j)))
    exact (continuous_const.mul (wave_continuous ..)).mul (continuous_const.mul (wave_continuous ..))
  · simp only [ite_eq_right h]
    exact continuous_const

theorem norm_noncommon_wave_product_le (n q : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) (t : ℝ) :
    ‖noncommonWaveProduct n q I J u l r v p s a b gate t‖ ≤
      waveNormRow I u l r a (fun x => ¬q∣x) t *
        (waveNormRow J v p s b (fun x => ¬q∣x) t + waveNormRow J v p s b (fun x => q∣x) t) +
      waveNormRow I u l r a (fun x => q∣x) t * waveNormRow J v p s b (fun x => ¬q∣x) t := by
  let P (i : α) := ‖a i‖ * ‖wave (u i) (l i) (r i) t‖
  let Q (j : β) := ‖b j‖ * ‖wave (v j) (p j) (s j) t‖
  let I1 := I.filter (fun i => q∣u i)
  let I0 := I.filter (fun i => ¬q∣u i)
  let J1 := J.filter (fun j => q∣v j)
  let J0 := J.filter (fun j => ¬q∣v j)
  unfold noncommonWaveProduct
  rw [norm_mul,norm_phase',one_mul]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun _ _ => norm_sum_le _ _).trans ?_)
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, if ¬(q∣u i ∧ q∣v j) then P i*Q j else 0 := by
      refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
      by_cases ok : gate i j <;> by_cases qd : q∣u i ∧ q∣v j <;>
        simp [P,Q,ok,qd,mul_nonneg]
    _ = ∑ i ∈ I, if q∣u i then P i*(∑ j ∈ J0,Q j) else P i*(∑ j ∈ J,Q j) := by
      refine sum_congr rfl fun i _ => ?_
      by_cases div : q∣u i
      · simp only [div,true_and,ite_true,J0,mul_sum,sum_filter]
        exact sum_congr rfl fun j _ => by by_cases dvd : q∣v j <;> simp [dvd]
      · simp only [div,false_and,not_false_eq_true,ite_true,ite_false,mul_sum]
    _ = ((∑ i ∈ I0,P i)*(∑ j ∈ J,Q j)) + ((∑ i ∈ I1,P i)*(∑ j ∈ J0,Q j)) := by
      rw [sum_mul,sum_mul]
      simp only [I0,I1,sum_filter,← sum_add_distrib]
      exact sum_congr rfl fun i _ => by by_cases hi : q∣u i <;> simp [hi]
    _ = _ := by
      unfold waveNormRow
      have split : (∑ j ∈ J,Q j) = (∑ j ∈ J0,Q j)+(∑ j ∈ J1,Q j) :=
        (sum_filter_add_sum_filter_not J (fun j => q∣v j) Q).symm.trans (add_comm _ _)
      rw [split]

private theorem wave_norm_row_nonnegative {ι : Type*} (S : Finset ι) (g f h : ι → ℕ)
    (w : ι → ℂ) (P : ℕ → Prop) [DecidablePred P] (t : ℝ) : 0 ≤ waveNormRow S g f h w P t := by
  unfold waveNormRow
  positivity

theorem norm_noncommon_wave_product_on_arc_le (n A H q a : ℕ) (hn : 0 < n) (hq : 0 < q)
    (Apos : 0 < A) (An : A ≤ n) (qn : q ≤ n) (cop : a.Coprime q) (geometric : 2*H*A ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (c : α → ℂ) (d : β → ℂ) (gate : α → β → Prop)
    {W : ℝ} (W0 : 0 ≤ W) (uSteps : ∀ i ∈ I, u i ∈ Icc 1 A) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 A)
    (uEnds : ∀ i ∈ I, r i ≤ n/u i) (vEnds : ∀ j ∈ J, s j ≤ n/v j)
    (uWeights : ∀ x ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i = x), ‖c i‖) ≤ W)
    (vWeights : ∀ x ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j = x), ‖d j‖) ≤ W)
    {t : ℝ} (ht : t ∈ wideArc n H q a) :
    ‖noncommonWaveProduct n q I J u l r v p s c d gate t‖ ≤
      W^2*logBudget n^2 * (4*((A : ℝ)+q)^2 + 4*((A : ℝ)+q)*((n : ℝ)/q)) := by
  let L := logBudget n
  let U := W*(2*((A : ℝ)+q)*L)
  let D := W*((n : ℝ)/q*L)
  have log_le (x : ℕ) (xp : 0 < x) (xn : x ≤ n) : 1+Real.log (x : ℝ) ≤ L := by
    unfold L logBudget
    have h := Real.log_le_log (show (0 : ℝ) < x from by exact_mod_cast xp)
      (show (x : ℝ) ≤ (n : ℝ)+2 from by
        have le : (x : ℝ) ≤ n := by exact_mod_cast xn
        linarith)
    linarith only [h]
  have nonBound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (log_le q hq qn) (by positivity : 0 ≤ 2*((A : ℝ)+q))) W0
  have divBound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (log_le A Apos An) (by positivity : 0 ≤ (n : ℝ)/q)) W0
  have l0 := (wave_norm_row_nondividing_le n A H q a hn hq cop geometric I u l r c uSteps W0 uWeights ht).trans nonBound
  have r0 := (wave_norm_row_nondividing_le n A H q a hn hq cop geometric J v p s d vSteps W0 vWeights ht).trans nonBound
  have l1 := (wave_norm_row_dividing_le n A q hq I u l r c uSteps uEnds W0 uWeights t).trans divBound
  have r1 := (wave_norm_row_dividing_le n A q hq J v p s d vSteps vEnds W0 vWeights t).trans divBound
  have lNon : 0 ≤ waveNormRow I u l r c (fun x => ¬q∣x) t := wave_norm_row_nonnegative ..
  have lDiv : 0 ≤ waveNormRow I u l r c (fun x => q∣x) t := wave_norm_row_nonnegative ..
  have rNon : 0 ≤ waveNormRow J v p s d (fun x => ¬q∣x) t := wave_norm_row_nonnegative ..
  have rDiv : 0 ≤ waveNormRow J v p s d (fun x => q∣x) t := wave_norm_row_nonnegative ..
  refine (norm_noncommon_wave_product_le n q I J u l r v p s c d gate t).trans ?_
  calc
    _ ≤ U*(U+D)+D*U := by
      exact add_le_add (mul_le_mul l0 (add_le_add r0 r1) (add_nonneg rNon rDiv) (lNon.trans l0))
        (mul_le_mul l1 r0 rNon (lDiv.trans l1))
    _ = _ := by unfold U D L; ring

end

end B13NondividingResidueReductionProof

end

/- Wide noncommon integral -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4ArcDecomposition
open DyadicMixedB4EnergyTail DyadicMixedB4GcdHarmonic
open scoped Classical

noncomputable section

def noncommonWideFamily (n B H : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) : ℂ :=
  ∑ q ∈ Icc 1 B, ∑ j ∈ numSet q,
    ∫ t in (0 : ℝ)..1, (wideArc n H q j).indicator (noncommonWaveProduct n q I J u l r v p s a b gate) t

theorem norm_arc_integral_le {n H q a : ℕ} {f : ℝ → ℂ} (fc : Continuous f)
    {K : ℝ} (K0 : 0 ≤ K) (dom : ∀ t ∈ wideArc n H q a, ‖f t‖ ≤ K) :
    ‖∫ t in (0 : ℝ)..1,(wideArc n H q a).indicator f t‖ ≤
      2*((H : ℝ)/((q : ℝ)*n))*K := by
  let h := (H : ℝ)/((q : ℝ)*n)
  let c := (a : ℝ)/q
  let D := (wideArc n H q a) ∩ Set.Icc (0 : ℝ) 1
  have hp : 0 ≤ h := by unfold h; positivity
  have hd : MeasurableSet D := (wide_arc_measurable ..).inter measurableSet_Icc
  have arc : D ⊆ Set.Icc (c-h) (c+h) := by
    intro t ht
    have abs := abs_le.mp (show |t-c| ≤ h from ht.1)
    change c-h ≤ t ∧ t ≤ c+h
    exact ⟨by linarith only [abs.1],by linarith only [abs.2]⟩
  have eq : (∫ t in (0 : ℝ)..1, (wideArc n H q a).indicator f t) = ∫ t in D,f t := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      setIntegral_indicator (wide_arc_measurable ..)]
    unfold D
    rw [Set.inter_comm]
  rw [eq]
  have iK : IntegrableOn (fun _ : ℝ => K) (Set.Icc (c-h) (c+h)) volume :=
    (continuous_const : Continuous (fun _ : ℝ => K)).continuousOn.integrableOn_Icc
  have iF : IntegrableOn (fun t => ‖f t‖) D volume := fc.norm.continuousOn.integrableOn_Icc.mono_set arc
  calc
    _ ≤ ∫ t in D, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ in D,K := setIntegral_mono_on iF (iK.mono_set arc) hd (fun t ht => dom t ht.1)
    _ ≤ ∫ _ in Set.Icc (c-h) (c+h),K :=
      setIntegral_mono_set iK (Filter.Eventually.of_forall (fun _ => K0)) (Filter.Eventually.of_forall arc)
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [hp]),
        intervalIntegral.integral_const,smul_eq_mul]
      unfold h
      ring

theorem norm_noncommon_wide_family_le (n A B H : ℕ) (hn : 0 < n)
    (Apos : 0 < A) (An : A ≤ n) (Bn : B ≤ n) (geometric : 2*H*A ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (c : α → ℂ) (d : β → ℂ) (gate : α → β → Prop)
    {W : ℝ} (W0 : 0 ≤ W) (uSteps : ∀ i ∈ I, u i ∈ Icc 1 A) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 A)
    (uEnds : ∀ i ∈ I, r i ≤ n/u i) (vEnds : ∀ j ∈ J, s j ≤ n/v j)
    (uWeights : ∀ x ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i = x), ‖c i‖) ≤ W)
    (vWeights : ∀ x ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j = x), ‖d j‖) ≤ W) :
    ‖noncommonWideFamily n B H I J u l r v p s c d gate‖ ≤
      16*W^2*logBudget n^2 *
        ((H : ℝ)*B*((A : ℝ)+B)^2/n + (H : ℝ)*((A : ℝ)+B)*(1+Real.log (B : ℝ))) := by
  let L := logBudget n
  let C (q : ℕ) := W^2*L^2 * (4*((A : ℝ)+q)^2 + 4*((A : ℝ)+q)*((n : ℝ)/q))
  let X := (A : ℝ)+B
  have c0 (q : ℕ) : 0 ≤ C q := by unfold C; positivity
  have each (q a : ℕ) (hq : q ∈ Icc 1 B) (ha : a ∈ numSet q) :
      ‖∫ t in (0 : ℝ)..1,(wideArc n H q a).indicator
        (noncommonWaveProduct n q I J u l r v p s c d gate) t‖ ≤
        2*((H : ℝ)/((q : ℝ)*n))*C q :=
    norm_arc_integral_le (noncommon_wave_product_continuous ..) (c0 q) fun t ht =>
      norm_noncommon_wave_product_on_arc_le n A H q a hn (mem_Icc.mp hq).1 Apos An
        ((mem_Icc.mp hq).2.trans Bn) (mem_filter.mp ha).2 geometric
        I J u l r v p s c d gate W0 uSteps vSteps uEnds vEnds uWeights vWeights ht
  have row (q : ℕ) (hq : q ∈ Icc 1 B) :
      ∑ a ∈ numSet q, ‖∫ t in (0 : ℝ)..1,(wideArc n H q a).indicator
        (noncommonWaveProduct n q I J u l r v p s c d gate) t‖ ≤
        16*W^2*L^2 * ((H : ℝ)*X^2/n + (H : ℝ)*X/q) := by
    have qr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q from (mem_Icc.mp hq).1)
    have nr : (0 : ℝ) < n := by exact_mod_cast hn
    have card : (numSet q).card ≤ 2*q := by
      refine (card_le_card (filter_subset _ _)).trans ?_
      rw [card_range]
      have _ := (mem_Icc.mp hq).1
      omega
    have aq : (A : ℝ)+q ≤ X := by unfold X; gcongr; exact_mod_cast (mem_Icc.mp hq).2
    calc
      _ ≤ ∑ _ ∈ numSet q, 2*((H : ℝ)/((q : ℝ)*n))*C q := sum_le_sum fun a ha => each q a hq ha
      _ = ((numSet q).card : ℝ) * (2*((H : ℝ)/((q : ℝ)*n))*C q) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ (2*(q : ℝ)) * (2*((H : ℝ)/((q : ℝ)*n))*C q) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by positivity) (c0 q))
        exact_mod_cast card
      _ = 16*W^2*L^2 * ((H : ℝ)*((A : ℝ)+q)^2/n + (H : ℝ)*((A : ℝ)+q)/q) := by
        unfold C
        field_simp
        ring
      _ ≤ _ := by gcongr
  unfold noncommonWideFamily
  refine (norm_sum_le _ _).trans ((sum_le_sum fun q hq => (norm_sum_le _ _).trans (row q hq)).trans ?_)
  let S := Icc (1 : ℕ) B
  have rearrange :
      (∑ q ∈ S,16*W^2*L^2*((H : ℝ)*X^2/n + (H : ℝ)*X/(q : ℝ))) =
        16*W^2*L^2 * ((H : ℝ)*B*X^2/n + (H : ℝ)*X*(∑ q ∈ S, (q : ℝ)⁻¹)) := by
    simp only [div_eq_mul_inv,← mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,S,Nat.card_Icc,
      Nat.add_sub_cancel]
    ring
  rw [rearrange]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (sum_inverse_Icc_le B) (by unfold X; positivity))) (by positivity)

end

end B13NondividingResidueReductionProof

end

/- Common wide point -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcCenters DyadicMixedB4ProgressionApprox
open DyadicMixedB4OffWaveMoment DyadicMixedB4WindowKernel
open scoped Classical

noncomputable section

private theorem norm_bin_average_le_one (u : ℕ) (hu : 0 < u) (t : ℝ) :
    ‖binAverage u t‖ ≤ 1 := by
  have ur : (0 : ℝ) < u := by exact_mod_cast hu
  have order : -(u : ℝ)/2 ≤ (u : ℝ)/2 := by linarith only [ur]
  have h : ‖∫ x in -(u : ℝ)/2..(u : ℝ)/2, phase (x*t)‖ ≤ (u : ℝ) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (f := fun x => phase (x*t)) order).trans_eq ?_
    simp only [norm_phase', intervalIntegral.integral_const,smul_eq_mul,mul_one]
    ring
  unfold binAverage
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ur.le)).trans_eq (inv_mul_cancel₀ ur.ne')

theorem norm_progression_average_le_wave {u : ℕ} (hu : 0 < u) (l r : ℕ) (t : ℝ) :
    ‖progressionAverage u l r t‖ ≤ ‖wave u l r t‖ := by
  rw [progressionAverage_eq,norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_bin_average_le_one u hu t) (norm_nonneg _)).trans_eq (mul_one _)

theorem norm_shifted_waves_sub_average_le (n H q a u v l r p s : ℕ) (hn : 0 < n) (hq : 0 < q)
    (hu : 0 < u) (hv : 0 < v) (threadU : q∣u) (threadV : q∣v) (rBound : r ≤ n/u) (sBound : s ≤ n/v)
    (nearU : 2*H*u ≤ n) (nearV : 2*H*v ≤ n) {t : ℝ} (ht : t ∈ wideArc n H q a) :
    ‖wave u l r t * wave v p s t -
        progressionAverage u l r (t-(a : ℝ)/q) * progressionAverage v p s (t-(a : ℝ)/q)‖ ≤
      2*Real.pi*((n : ℝ)/u + (n : ℝ)/v) := by
  let β := t-(a : ℝ)/q
  have qr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have bt : |β| ≤ (H : ℝ)/((q : ℝ)*n) := ht
  have us : wave u l r t = wave u l r β := by
    have eq : β+(a : ℝ)/q=t := by unfold β; ring
    rw [← eq, wave_at_cell_center hq threadU]
  have vs : wave v p s t = wave v p s β := by
    have eq : β+(a : ℝ)/q=t := by unfold β; ring
    rw [← eq, wave_at_cell_center hq threadV]
  have near (w : ℕ) (hw : 2*H*w ≤ n) : (w : ℝ)*|β| ≤ 1/2 := by
    have prod : 2*(H : ℝ)*(w : ℝ) ≤ n := by exact_mod_cast hw
    have qn : (n : ℝ) ≤ (q : ℝ)*n := by simpa only [one_mul] using mul_le_mul_of_nonneg_right qr nr.le
    refine (mul_le_mul_of_nonneg_left bt (Nat.cast_nonneg w)).trans ?_
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2)).2
    rw [show (w : ℝ)*((H : ℝ)/((q : ℝ)*n))*2 =
      (2*(H : ℝ)*(w : ℝ))/((q : ℝ)*n) by ring]
    exact (div_le_one (by positivity)).2 (prod.trans qn)
  have uCap : ‖wave u l r β‖ ≤ (n : ℝ)/u :=
    (wave_cap ..).trans ((show (r : ℝ) ≤ ((n/u : ℕ) : ℝ) by exact_mod_cast rBound).trans Nat.cast_div_le)
  have vCap : ‖wave v p s β‖ ≤ (n : ℝ)/v :=
    (wave_cap ..).trans ((show (s : ℝ) ≤ ((n/v : ℕ) : ℝ) by exact_mod_cast sBound).trans Nat.cast_div_le)
  let U := wave u l r β
  let V := wave v p s β
  let U' := progressionAverage u l r β
  let V' := progressionAverage v p s β
  rw [us,vs]
  change ‖U*V-U'*V'‖ ≤ _
  have eq : U*V-U'*V' = (U-U')*V+U'*(V-V') := by ring
  rw [eq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul,norm_mul]
  have h1 := mul_le_mul (norm_wave_sub_average_le l r hu (near _ nearU)) vCap
    (norm_nonneg _) (by positivity : 0 ≤ 2*Real.pi)
  have h2 := mul_le_mul ((norm_progression_average_le_wave hu l r β).trans uCap)
    (norm_wave_sub_average_le p s hv (near _ nearV)) (norm_nonneg _) (by positivity : 0 ≤ (n : ℝ)/u)
  exact (add_le_add h1 h2).trans_eq (by ring)

end

end B13NondividingResidueReductionProof

end

/- Common wide mass -/
section

namespace B13NondividingResidueReductionProof

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

end B13NondividingResidueReductionProof

end

/- Wide medium budget -/
section

namespace B13NondividingResidueReductionProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

private theorem cutoff_h_power_le {n : ℕ} (hn : 2 ≤ n) :
    (cutoffH n : ℝ) ≤ 4096*(n : ℝ)^(1/3 : ℝ)*logBudget n^2 := by
  have hp : 0 < n := by omega
  have b : (cutoffB n : ℝ) ≤ (n : ℝ)^(1/3 : ℝ) := Nat.floor_le (by positivity)
  have logB : (Nat.log 2 (n+2) : ℝ) ≤ 4*logBudget n :=
    (log2_le_four_log n hn).trans (mul_le_mul_of_nonneg_left (log_le_logBudget hp le_rfl) (by norm_num))
  calc
    _ = 256*(cutoffB n : ℝ)*(Nat.log 2 (n+2) : ℝ)^2 := by unfold cutoffH; push_cast; ring
    _ ≤ 256*(n : ℝ)^(1/3 : ℝ)*(4*logBudget n)^2 := by gcongr
    _ = _ := by ring

theorem cutoff_h_le_power_log {n : ℕ} (hn : 2 ≤ n) :
    (cutoffH n : ℝ) ≤ 4096*(n : ℝ)^(1/3 : ℝ)*logBudget n^2 :=
  cutoff_h_power_le hn

end

end B13NondividingResidueReductionProof

end

/- Divisible step energy -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcCenters DyadicMixedB4PairIntegral DyadicMixedB4ArcDecomposition
open DyadicMixedB4OffWaveMoment
open scoped Classical

noncomputable section

private theorem wave_eq_residue_polynomial (n g l r : ℕ) (hg : 0 < g) (hr : r ≤ n/g) (t : ℝ) :
    wave g l r t = ∑ m ∈ range (n+1), if g ∣ m ∧ m/g ∈ Ioc l r then phase ((m : ℝ)*t) else 0 := by
  unfold wave
  rw [← sum_filter]
  apply sum_bij (fun k _ => g*k)
  · intro k hk
    have within := (Nat.le_div_iff_mul_le hg).mp ((mem_Ioc.mp hk).2.trans hr)
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (by rwa [Nat.mul_comm])),
      dvd_mul_right _ _, by simpa only [Nat.mul_div_cancel_left _ hg]⟩
  · intro a _ b _ eq
    exact Nat.eq_of_mul_eq_mul_left hg eq
  · intro m hm
    have pair := (mem_filter.mp hm).2
    exact ⟨m/g,pair.2,Nat.mul_div_cancel' pair.1⟩
  · intro k _
    rfl

def divisibleStepPolynomial (e : ℕ) {ι : Type*} (I : Finset ι)
    (g l r : ι → ℕ) (c : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i ∈ I.filter (fun i => e ∣ g i), c i * wave (g i) (l i) (r i) t

def divisibleStepCoefficient (e : ℕ) {ι : Type*} (I : Finset ι)
    (g l r : ι → ℕ) (c : ι → ℂ) (m : ℕ) : ℂ :=
  ∑ i ∈ I.filter (fun i => e ∣ g i), if g i ∣ m ∧ m/g i ∈ Ioc (l i) (r i) then c i else 0

theorem divisible_step_polynomial_plain (n e : ℕ) {ι : Type*} (I : Finset ι)
    (g l r : ι → ℕ) (c : ι → ℂ)
    (steps : ∀ i ∈ I, g i ∈ Icc 1 n) (ends : ∀ i ∈ I, r i ≤ n/g i) (t : ℝ) :
    divisibleStepPolynomial e I g l r c t = plainPolynomial n (divisibleStepCoefficient e I g l r c) t := by
  unfold divisibleStepPolynomial plainPolynomial
  calc
    _ = ∑ i ∈ I.filter (fun i => e ∣ g i), ∑ m ∈ range (n+1),
        (if g i ∣ m ∧ m/g i ∈ Ioc (l i) (r i) then c i else 0) * phase ((m : ℝ)*t) := by
      refine sum_congr rfl fun i hi => ?_
      have h := (mem_filter.mp hi).1
      rw [wave_eq_residue_polynomial n _ _ _ (mem_Icc.mp (steps i h)).1 (ends i h), mul_sum]
      refine sum_congr rfl fun m _ => ?_
      by_cases hm : g i ∣ m ∧ m/g i ∈ Ioc (l i) (r i) <;> simp [hm]
    _ = _ := by unfold divisibleStepCoefficient; simp_rw [sum_mul]; exact sum_comm

theorem divisible_step_polynomial_periodic (e : ℕ) (he : 0 < e) {ι : Type*} (I : Finset ι)
    (g l r : ι → ℕ) (c : ι → ℂ) (j : ℕ) (t : ℝ) :
    divisibleStepPolynomial e I g l r c (t+(j : ℝ)/e) =
      divisibleStepPolynomial e I g l r c t := by
  unfold divisibleStepPolynomial
  refine sum_congr rfl fun i hi => ?_
  rw [wave_at_cell_center he (mem_filter.mp hi).2]

private theorem divisible_step_coefficient_zero_of_gate (e : ℕ) {ι : Type*} (I : Finset ι)
    (g l r : ι → ℕ) (c : ι → ℂ) (m : ℕ) (gate : m = 0 ∨ ¬ e ∣ m) :
    divisibleStepCoefficient e I g l r c m = 0 := by
  unfold divisibleStepCoefficient
  refine sum_eq_zero fun i hi => ?_
  rcases gate with zero | notDivides
  · simp [zero]
  · have no : ¬ g i ∣ m := fun yes => notDivides ((mem_filter.mp hi).2.trans yes)
    simp [no]

private theorem norm_divisible_step_coefficient_le {n m : ℕ} (hm : 0 < m) (e : ℕ) {ι : Type*}
    (I : Finset ι) (g l r : ι → ℕ) (c : ι → ℂ) {W : ℝ}
    (steps : ∀ i ∈ I, g i ∈ Icc 1 n)
    (weights : ∀ u ∈ Icc 1 n, (∑ i ∈ I.filter (fun i => g i = u), ‖c i‖) ≤ W) (W0 : 0 ≤ W) :
    ‖divisibleStepCoefficient e I g l r c m‖ ≤ (m.divisors.card : ℝ) * W := by
  let w (u : ℕ) := ∑ i ∈ I.filter (fun i => g i = u), ‖c i‖
  unfold divisibleStepCoefficient
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ I.filter (fun i => e ∣ g i), if g i ∣ m then ‖c i‖ else 0 := by
      refine sum_le_sum fun i _ => ?_
      by_cases h : g i ∣ m
      · by_cases gate : m/g i ∈ Ioc (l i) (r i) <;> simp [h,gate]
      · simp [h]
    _ ≤ ∑ i ∈ I, if g i ∣ m then ‖c i‖ else 0 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => by split_ifs <;> positivity)
    _ = ∑ u ∈ Icc 1 n, if u ∣ m then w u else 0 := by
      rw [← sum_fiberwise_of_maps_to steps (fun i => if g i ∣ m then ‖c i‖ else 0)]
      refine sum_congr rfl fun u _ => ?_
      have same := fun i (hi : i ∈ I.filter (fun i => g i = u)) => (mem_filter.mp hi).2
      by_cases dvd : u ∣ m
      · rw [if_pos dvd]
        exact sum_congr rfl fun i hi => by rw [same i hi, if_pos dvd]
      · rw [if_neg dvd]
        exact sum_eq_zero fun i hi => by rw [same i hi, if_neg dvd]
    _ ≤ ∑ _ ∈ m.divisors, W := by
      rw [← sum_filter]
      have subset : (Icc 1 n).filter (fun u => u ∣ m) ⊆ m.divisors :=
        fun u hu => Nat.mem_divisors.mpr ⟨(mem_filter.mp hu).2,hm.ne'⟩
      refine (sum_le_sum fun u hu => weights u (mem_filter.mp hu).1).trans ?_
      exact sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => W0)
    _ = _ := by rw [sum_const,nsmul_eq_mul]

theorem divisible_step_energy_le (n e : ℕ) {ι : Type*} (I : Finset ι)
    (g l r : ι → ℕ) (c : ι → ℂ) {W T : ℝ} (W0 : 0 ≤ W) (T0 : 0 ≤ T)
    (steps : ∀ i ∈ I, g i ∈ Icc 1 n) (ends : ∀ i ∈ I, r i ≤ n/g i)
    (weights : ∀ u ∈ Icc 1 n, (∑ i ∈ I.filter (fun i => g i = u), ‖c i‖) ≤ W)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    (∫ t in (0 : ℝ)..1, ‖divisibleStepPolynomial e I g l r c t‖^2) ≤
      (n : ℝ)/e * (W*T)^2 := by
  let A := divisibleStepCoefficient e I g l r c
  let P := (Icc 1 n).filter (fun m => e ∣ m)
  have sub : P ⊆ range (n+1) := by
    intro m hm
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp (mem_filter.mp hm).1).2)
  have count : P.card ≤ n/e := by
    have eq := Nat.card_multiples' n e
    have same : P = (range (n+1)).filter (fun m => m ≠ 0 ∧ e ∣ m) := by
      ext m
      simp only [P, mem_Icc, mem_range, mem_filter]
      omega
    rw [same]
    exact eq.le
  simp_rw [divisible_step_polynomial_plain n e I g l r c steps ends, ← norm_shiftedPolynomial_eq,
    shiftedPolynomial_parseval]
  change ∑ m ∈ range (n+1), ‖A m‖^2 ≤ _
  have remove : (∑ m ∈ P, ‖A m‖^2) = ∑ m ∈ range (n+1), ‖A m‖^2 := by
    refine sum_subset sub fun m hm outside => ?_
    have within : m ≤ n := Nat.le_of_lt_succ (mem_range.mp hm)
    have gate : m = 0 ∨ ¬ e ∣ m := by
      by_cases zero : m = 0
      · exact Or.inl zero
      · exact Or.inr fun dvd => outside (mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr zero,within⟩,dvd⟩)
    have zero : A m = 0 := divisible_step_coefficient_zero_of_gate e I g l r c m gate
    simp [zero]
  rw [← remove]
  calc
    _ ≤ ∑ _ ∈ P, (W*T)^2 := by
      refine sum_le_sum fun m hm => ?_
      obtain ⟨mp,mn⟩ := mem_Icc.mp (mem_filter.mp hm).1
      apply pow_le_pow_left₀ (norm_nonneg _)
      refine (norm_divisible_step_coefficient_le mp e I g l r c steps weights W0).trans ?_
      rw [mul_comm W T]
      exact mul_le_mul_of_nonneg_right (divisorBound m mn) W0
    _ = (P.card : ℝ)*(W*T)^2 := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ((n/e : ℕ) : ℝ)*(W*T)^2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast count) (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right Nat.cast_div_le (sq_nonneg _)

end

end B13NondividingResidueReductionProof

end

/- Endpoint energy -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open DyadicMixedB4Scale DyadicMixedB4ArcDecomposition DyadicMixedB4YoungIntegral DyadicMixedB4OffWaveMoment
open scoped Classical

noncomputable section

def waveFamilyPolynomial {ι : Type*} (I : Finset ι) (g l r : ι → ℕ)
    (c : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i ∈ I, c i * wave (g i) (l i) (r i) t

theorem wave_family_continuous {ι : Type*} (I : Finset ι) (g l r : ι → ℕ) (c : ι → ℂ) :
    Continuous (waveFamilyPolynomial I g l r c) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (wave_continuous ..)

private theorem wave_family_eq_divisible {ι : Type*} (I : Finset ι) (g l r : ι → ℕ) (c : ι → ℂ) :
    waveFamilyPolynomial I g l r c = divisibleStepPolynomial 1 I g l r c := by
  funext t
  simp [waveFamilyPolynomial, divisibleStepPolynomial]

private theorem wave_eq_zero_of_right_zero (g l : ℕ) (t : ℝ) : wave g l 0 t = 0 := by
  exact sum_eq_zero fun k hk => by have := mem_Ioc.mp hk; omega

theorem wave_family_frequency_energy_le {n N : ℕ} (hN : N ≤ n) {ι : Type*} (I : Finset ι)
    (g l r : ι → ℕ) (c : ι → ℂ) {W T : ℝ} (W0 : 0 ≤ W) (T0 : 0 ≤ T)
    (steps : ∀ i ∈ I, g i ∈ Icc 1 n)
    (freq : ∀ i ∈ I, g i * r i ≤ N)
    (weights : ∀ u ∈ Icc 1 n, (∑ i ∈ I.filter (fun i => g i = u), ‖c i‖) ≤ W)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    (∫ t in (0 : ℝ)..1, ‖waveFamilyPolynomial I g l r c t‖^2) ≤ (N : ℝ)*(W*T)^2 := by
  let J := I.filter fun i => g i ≤ N
  have same : waveFamilyPolynomial I g l r c = waveFamilyPolynomial J g l r c := by
    funext t
    symm
    unfold waveFamilyPolynomial
    refine sum_subset (filter_subset _ _) fun i hi outside => ?_
    have gt : N < g i := lt_of_not_ge fun within => outside (mem_filter.mpr ⟨hi,within⟩)
    have rightZero : r i = 0 := by
      by_contra nonzero
      have grow := Nat.mul_le_mul_left (g i) (show 1 ≤ r i from Nat.pos_of_ne_zero nonzero)
      have le : g i ≤ g i * r i := by simpa only [mul_one] using grow
      exact (not_lt_of_ge (le.trans (freq i hi))) gt
    rw [rightZero, wave_eq_zero_of_right_zero, mul_zero]
  have jSteps : ∀ i ∈ J, g i ∈ Icc 1 N := fun i hi =>
    mem_Icc.mpr ⟨(mem_Icc.mp (steps i (mem_filter.mp hi).1)).1,(mem_filter.mp hi).2⟩
  have jEnds : ∀ i ∈ J, r i ≤ N/g i := by
    intro i hi
    apply (Nat.le_div_iff_mul_le (mem_Icc.mp (jSteps i hi)).1).mpr
    simpa only [mul_comm (r i) (g i)] using freq i (mem_filter.mp hi).1
  have jWeights : ∀ u ∈ Icc 1 N, (∑ i ∈ J.filter (fun i => g i = u), ‖c i‖) ≤ W := by
    intro u hu
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun i _ _ => norm_nonneg (c i))).trans ?_
    exact weights u (Icc_subset_Icc_right hN hu)
  rw [same, wave_family_eq_divisible]
  simpa only [Nat.cast_one, div_one] using
    divisible_step_energy_le N 1 J g l r c W0 T0 jSteps jEnds jWeights
      (fun m hm => divisorBound m (hm.trans hN))

theorem wave_family_energy_le {n : ℕ} {ι : Type*} (I : Finset ι)
    (g l r : ι → ℕ) (c : ι → ℂ) {W T : ℝ} (W0 : 0 ≤ W) (T0 : 0 ≤ T)
    (steps : ∀ i ∈ I, g i ∈ Icc 1 n)
    (ends : ∀ i ∈ I, r i ≤ n/g i)
    (weights : ∀ u ∈ Icc 1 n, (∑ i ∈ I.filter (fun i => g i = u), ‖c i‖) ≤ W)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    (∫ t in (0 : ℝ)..1, ‖waveFamilyPolynomial I g l r c t‖^2) ≤ (n : ℝ)*(W*T)^2 := by
  rw [wave_family_eq_divisible]
  simpa only [Nat.cast_one, div_one] using
    divisible_step_energy_le n 1 I g l r c W0 T0 steps ends weights divisorBound

theorem wave_family_prefix_split {ι : Type*} (I : Finset ι) (g l r : ι → ℕ) (c : ι → ℂ) (t : ℝ) :
    waveFamilyPolynomial I g (fun _ => 0) r c t =
      waveFamilyPolynomial I g l r c t + waveFamilyPolynomial I g (fun _ => 0) (fun i => min (l i) (r i)) c t := by
  unfold waveFamilyPolynomial
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_add]
  congr 1
  unfold wave
  have intervals : Ioc 0 (r i) = (Ioc (l i) (r i)) ∪ (Ioc 0 (min (l i) (r i))) := by
    ext k
    simp only [mem_Ioc, mem_union, le_min_iff]
    omega
  have disjoint : Disjoint (Ioc (l i) (r i)) (Ioc 0 (min (l i) (r i))) := by
    rw [disjoint_left]
    intro k hk hk'
    have lt := (mem_Ioc.mp hk).1
    have le := (mem_Ioc.mp hk').2.trans (min_le_left _ _)
    omega
  rw [intervals, sum_union disjoint]

def maskedWaveProduct (n : ℕ) (f g : ℝ → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator
    (fun x => phase (((-(n : ℤ)) : ℝ)*x) * (f x * g x)) t

theorem masked_wave_product_comm (n : ℕ) (f g : ℝ → ℂ) :
    maskedWaveProduct n f g = maskedWaveProduct n g f := by
  unfold maskedWaveProduct
  exact intervalIntegral.integral_congr fun t _ => by
    by_cases ht : t ∈ (wide n (cutoffB n) (cutoffH n))ᶜ <;> simp [ht, mul_comm (f t)]

theorem masked_wave_product_add_right (n : ℕ) {f g h : ℝ → ℂ}
    (fc : Continuous f) (gc : Continuous g) (hc : Continuous h) :
    maskedWaveProduct n f (fun t => g t + h t) =
      maskedWaveProduct n f g + maskedWaveProduct n f h := by
  have pc : Continuous (fun t : ℝ => phase (((-(n : ℤ)) : ℝ)*t)) := by unfold phase; fun_prop
  have integrable {k : ℝ → ℂ} (kc : Continuous k) : IntervalIntegrable
      ((wide n (cutoffB n) (cutoffH n))ᶜ.indicator
        (fun x => phase (((-(n : ℤ)) : ℝ)*x) * (f x * k x))) volume 0 1 :=
    indicator_intervalIntegrable (pc.mul (fc.mul kc)) (wide_measurable n (cutoffB n) (cutoffH n)).compl
  unfold maskedWaveProduct
  rw [← intervalIntegral.integral_add (integrable gc) (integrable hc)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases ht : t ∈ (wide n (cutoffB n) (cutoffH n))ᶜ <;> simp [ht,mul_add]

theorem norm_masked_wave_product_le {n : ℕ} {f g : ℝ → ℂ} (fc : Continuous f) (gc : Continuous g)
    {c : ℝ} (hc : 0 < c) :
    ‖maskedWaveProduct n f g‖ ≤
      (c * (∫ t in (0 : ℝ)..1, ‖f t‖^2) + c⁻¹ * (∫ t in (0 : ℝ)..1, ‖g t‖^2))/2 := by
  let P (t : ℝ) := phase (((-(n : ℤ)) : ℝ)*t)
  have pc : Continuous P := by unfold P phase; fun_prop
  have normP : ∀ t : ℝ, ‖P t * f t‖^2 = ‖f t‖^2 := by intro t; simp [P, norm_phase']
  have fc' : Continuous (fun t => P t * f t) := pc.mul fc
  have eq : maskedWaveProduct n f g =
    ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator
      (fun x => (P x * f x)*g x) t := by
    simp only [maskedWaveProduct, P, ← mul_assoc]
  rw [eq]
  refine (norm_indicator_product_le hc (wide_measurable ..).compl fc'.measurable gc.measurable
    ((fc'.norm.pow 2).intervalIntegrable 0 1) ((gc.norm.pow 2).intervalIntegrable 0 1)).trans_eq ?_
  simp_rw [normP]
  ring

end

end B13NondividingResidueReductionProof

end

/- Endpoint saving -/
section

namespace B13NondividingResidueReductionProof

open Finset Filter Topology MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open DyadicMixedB4PairIntegral
open scoped Classical

noncomputable section

private def endpointCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (7/8 : ℝ)⌋₊

private theorem endpoint_cap_le {n : ℕ} (hn : 0 < n) : endpointCap n ≤ n :=
  Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num))

private theorem norm_endpoint_pair_le {n : ℕ} (hn : 0 < n) {f g : ℝ → ℂ}
    (fc : Continuous f) (gc : Continuous g) {D : ℝ}
    (fEnergy : (∫ t in (0 : ℝ)..1, ‖f t‖^2) ≤ (n : ℝ)*D^2)
    (gEnergy : (∫ t in (0 : ℝ)..1, ‖g t‖^2) ≤ (endpointCap n : ℝ)*D^2) :
    ‖maskedWaveProduct n f g‖ ≤ (n : ℝ)^(15/16 : ℝ)*D^2 := by
  let c := (n : ℝ)^(-(1/16) : ℝ)
  let P := (n : ℝ)^(15/16 : ℝ)
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have cp : 0 < c := Real.rpow_pos_of_pos nr _
  have fScale : c * (n : ℝ) = P := by
    unfold c P
    calc
      _ = (n : ℝ)^(-(1/16) : ℝ) * (n : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add nr]; norm_num
  have gScale : c⁻¹ * (n : ℝ)^(7/8 : ℝ) = P := by
    unfold c P
    rw [Real.rpow_neg nr.le, inv_inv, ← Real.rpow_add nr]
    norm_num
  have cap : (endpointCap n : ℝ) ≤ (n : ℝ)^(7/8 : ℝ) := Nat.floor_le (by positivity)
  refine (norm_masked_wave_product_le fc gc cp).trans ?_
  calc
    _ ≤ (c * ((n : ℝ)*D^2) + c⁻¹ * ((n : ℝ)^(7/8 : ℝ)*D^2))/2 :=
      div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left fEnergy cp.le)
        (mul_le_mul_of_nonneg_left (gEnergy.trans (mul_le_mul_of_nonneg_right cap (sq_nonneg _)))
          (inv_nonneg.mpr cp.le))) (by norm_num)
    _ = _ := by rw [← mul_assoc, ← mul_assoc, fScale, gScale]; unfold P; ring

private def openLeftPolynomial (n : ℕ) : ℝ → ℂ :=
  waveFamilyPolynomial (bilateralLeftWaveItems n) leftBilinearStep (fun _ => 0)
    (fun i => n/leftBilinearStep i) (leftBilinearWeight n)

private def leftEndpointPolynomial (n : ℕ) : ℝ → ℂ :=
  waveFamilyPolynomial (bilateralLeftWaveItems n) leftBilinearStep (fun _ => 0)
    (fun i => min (cutoffU n/i.2) (n/leftBilinearStep i)) (leftBilinearWeight n)

private def openRightLowPolynomial (n : ℕ) : ℝ → ℂ :=
  waveFamilyPolynomial (rightLowWaveItems n) rightLowWaveStep (fun _ => 0)
    (rightLowWaveUpper n) rightLowWaveWeight

private def rightLowEndpointPolynomial (n : ℕ) : ℝ → ℂ :=
  waveFamilyPolynomial (rightLowWaveItems n) rightLowWaveStep (fun _ => 0)
    (fun i => min (cutoffB n/i.2) (rightLowWaveUpper n i)) rightLowWaveWeight

private theorem left_endpoint_frequency {n : ℕ} (hn : 0 < n)
    (i : ℕ × ℕ) (hi : i ∈ bilateralLeftWaveItems n) :
    leftBilinearStep i * min (cutoffU n/i.2) (n/leftBilinearStep i) ≤ endpointCap n := by
  have members := (mem_filter.mp (mem_filter.mp hi).1).1
  have leftBound := (mem_Ioc.mp (mem_product.mp members).1).2
  have budget : leftBilinearStep i * min (cutoffU n/i.2) (n/leftBilinearStep i) ≤ lowCut n * cutoffU n := by
    calc
      _ ≤ leftBilinearStep i * (cutoffU n/i.2) := Nat.mul_le_mul_left _ (min_le_left _ _)
      _ = i.1 * ((cutoffU n/i.2)*i.2) := by unfold leftBilinearStep; ring
      _ ≤ _ := Nat.mul_le_mul leftBound (Nat.div_mul_le_self ..)
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have nr := zero_lt_one.trans_le n1
  refine budget.trans (Nat.le_floor ?_)
  push_cast
  calc
    _ ≤ (n : ℝ)^(1/4 : ℝ) * (n : ℝ)^(1/16 : ℝ) := by
      have l : (lowCut n : ℝ) ≤ (n : ℝ)^(1/4 : ℝ) := Nat.floor_le (by positivity)
      have u : (cutoffU n : ℝ) ≤ (n : ℝ)^(1/16 : ℝ) := Nat.floor_le (by positivity)
      exact mul_le_mul l u (Nat.cast_nonneg _) (by positivity)
    _ ≤ _ := by rw [← Real.rpow_add nr]; exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)

private theorem right_low_endpoint_frequency {n : ℕ} (hn : 0 < n)
    (i : RightLowWaveIndex) (hi : i ∈ rightLowWaveItems n) :
    rightLowWaveStep i * min (cutoffB n/i.2) (rightLowWaveUpper n i) ≤ endpointCap n := by
  have bBound := (mem_Ioc.mp (mem_sigma.mp hi).1).2.trans (min_le_right _ _)
  have budget : rightLowWaveStep i * min (cutoffB n/i.2) (rightLowWaveUpper n i) ≤
      rightLargeCofactorCut n * cutoffB n := by
    calc
      _ ≤ rightLowWaveStep i * (cutoffB n/i.2) := Nat.mul_le_mul_left _ (min_le_left _ _)
      _ = i.1 * ((cutoffB n/i.2)*i.2) := by unfold rightLowWaveStep; ring
      _ ≤ _ := Nat.mul_le_mul bBound (Nat.div_mul_le_self ..)
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have nr := zero_lt_one.trans_le n1
  refine budget.trans (Nat.le_floor ?_)
  push_cast
  calc
    _ ≤ (n : ℝ)^(33/64 : ℝ) * (n : ℝ)^(1/3 : ℝ) := by
      have k : (rightLargeCofactorCut n : ℝ) ≤ (n : ℝ)^(33/64 : ℝ) := Nat.floor_le (by positivity)
      have b : (cutoffB n : ℝ) ≤ (n : ℝ)^(1/3 : ℝ) := Nat.floor_le (by positivity)
      exact mul_le_mul k b (Nat.cast_nonneg _) (by positivity)
    _ ≤ _ := by rw [← Real.rpow_add nr]; exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)

private def endpointContribution (n : ℕ) : ℂ :=
  maskedWaveProduct n (rightLowPolynomial n) (leftEndpointPolynomial n) +
  maskedWaveProduct n (rightHighPolynomial n) (leftEndpointPolynomial n) +
  maskedWaveProduct n (openLeftPolynomial n) (rightLowEndpointPolynomial n)

def bilateralOpenPrefixRemainder (n : ℕ) : ℂ :=
  maskedWaveProduct n (openLeftPolynomial n) (openRightLowPolynomial n) +
  maskedWaveProduct n (openLeftPolynomial n) (rightHighPolynomial n)

private theorem bilateral_open_prefix_eq {n : ℕ} (hn : 0 < n) :
    bilateralOpenPrefixRemainder n = bilateralLargeLeftRemainder n + endpointContribution n := by
  let L := leftBilinearPolynomial n (bilateralLeftWaveItems n)
  let Y := rightLowPolynomial n
  let Z := rightHighPolynomial n
  have Lc : Continuous L := wave_family_continuous ..
  have Yc : Continuous Y := wave_family_continuous ..
  have Zc : Continuous Z := wave_family_continuous ..
  have Ll : Continuous (leftEndpointPolynomial n) := wave_family_continuous ..
  have Yl : Continuous (rightLowEndpointPolynomial n) := wave_family_continuous ..
  have Lp : Continuous (openLeftPolynomial n) := wave_family_continuous ..
  have lEq : openLeftPolynomial n = fun t => L t + leftEndpointPolynomial n t := by
    funext t
    exact wave_family_prefix_split ..
  have yEq : openRightLowPolynomial n = fun t => Y t + rightLowEndpointPolynomial n t := by
    funext t
    exact wave_family_prefix_split ..
  have original : bilateralLargeLeftRemainder n = maskedWaveProduct n L Y + maskedWaveProduct n L Z := by
    rw [bilateralLargeLeftRemainder_eq_product_cut hn]
    have low := two_wave_sums_partition n (bilateralLeftWaveItems n) (rightLowWaveItems n)
      leftBilinearStep (fun i => cutoffU n/i.2) (fun i => n/leftBilinearStep i)
      rightLowWaveStep (fun i => cutoffB n/i.2) (rightLowWaveUpper n) (leftBilinearWeight n) rightLowWaveWeight
    have high := two_wave_sums_partition n (bilateralLeftWaveItems n) (rightHighWaveItems n)
      leftBilinearStep (fun i => cutoffU n/i.2) (fun i => n/leftBilinearStep i)
      rightHighWaveStep (rightHighWaveLower n) (fun i => n/rightHighWaveStep i)
      (leftBilinearWeight n) (rightHighWaveWeight n)
    have y : maskedWaveProduct n L Y = _ := low
    have z : maskedWaveProduct n L Z = _ := high
    rw [y,z]
    let sl := shortProductFamily n (bilateralLeftWaveItems n) (rightLowWaveItems n)
      leftBilinearStep (fun i => cutoffU n/i.2) (fun i => n/leftBilinearStep i)
      rightLowWaveStep (fun i => cutoffB n/i.2) (rightLowWaveUpper n) (leftBilinearWeight n) rightLowWaveWeight
    let ll := longProductFamily n (bilateralLeftWaveItems n) (rightLowWaveItems n)
      leftBilinearStep (fun i => cutoffU n/i.2) (fun i => n/leftBilinearStep i)
      rightLowWaveStep (fun i => cutoffB n/i.2) (rightLowWaveUpper n) (leftBilinearWeight n) rightLowWaveWeight
    let sh := shortProductFamily n (bilateralLeftWaveItems n) (rightHighWaveItems n)
      leftBilinearStep (fun i => cutoffU n/i.2) (fun i => n/leftBilinearStep i)
      rightHighWaveStep (rightHighWaveLower n) (fun i => n/rightHighWaveStep i)
      (leftBilinearWeight n) (rightHighWaveWeight n)
    let lh := longProductFamily n (bilateralLeftWaveItems n) (rightHighWaveItems n)
      leftBilinearStep (fun i => cutoffU n/i.2) (fun i => n/leftBilinearStep i)
      rightHighWaveStep (rightHighWaveLower n) (fun i => n/rightHighWaveStep i)
      (leftBilinearWeight n) (rightHighWaveWeight n)
    change ll + lh + (sl+sh) = sl+ll+(sh+lh)
    abel
  unfold bilateralOpenPrefixRemainder endpointContribution
  rw [yEq, masked_wave_product_add_right n Lp Yc Yl,
    masked_wave_product_comm n (openLeftPolynomial n) Y,
    masked_wave_product_comm n (openLeftPolynomial n) Z, lEq,
    masked_wave_product_add_right n Yc Lc Ll, masked_wave_product_add_right n Zc Lc Ll, original,
    masked_wave_product_comm n L Y, masked_wave_product_comm n L Z]
  abel

private theorem norm_endpoint_contribution_le {n : ℕ} (hn : 0 < n) {T : ℝ} (T1 : 1 ≤ T)
    (dBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖endpointContribution n‖ ≤ 3 * (n : ℝ)^(15/16 : ℝ) * (T^4*logBudget n)^2 := by
  let W := T^3*logBudget n
  have T0 := zero_le_one.trans T1
  have W0 : 0 ≤ W := mul_nonneg (pow_nonneg T0 _) (zero_le_one.trans (one_le_logBudget n))
  have leftSteps : ∀ i ∈ bilateralLeftWaveItems n, leftBilinearStep i ∈ Icc 1 n :=
    fun _ h => bilateral_left_step_range h
  have lowSteps : ∀ i ∈ rightLowWaveItems n, rightLowWaveStep i ∈ Icc 1 n :=
    fun _ h => bilateral_right_low_step_range h
  have highSteps : ∀ i ∈ rightHighWaveItems n, rightHighWaveStep i ∈ Icc 1 n :=
    fun _ h => bilateral_right_high_step_range h
  have leftWeights := norm_bilateral_left_step_mass hn T0 dBound
  have lowWeights := norm_bilateral_right_low_step_mass T1 dBound
  have highWeights := norm_bilateral_right_high_step_mass T0 dBound
  have L : (∫ t in (0 : ℝ)..1, ‖openLeftPolynomial n t‖^2) ≤ (n : ℝ)*(W*T)^2 :=
    wave_family_energy_le _ _ _ _ _ W0 T0 leftSteps (fun _ _ => le_rfl) leftWeights dBound
  have l : (∫ t in (0 : ℝ)..1, ‖leftEndpointPolynomial n t‖^2) ≤ (endpointCap n : ℝ)*(W*T)^2 :=
    wave_family_frequency_energy_le (endpoint_cap_le hn) _ _ _ _ _ W0 T0
      leftSteps (left_endpoint_frequency hn) leftWeights dBound
  have Y : (∫ t in (0 : ℝ)..1, ‖rightLowPolynomial n t‖^2) ≤ (n : ℝ)*(W*T)^2 :=
    wave_family_energy_le _ _ _ _ _ W0 T0 lowSteps (fun _ _ => min_le_right _ _) lowWeights dBound
  have y : (∫ t in (0 : ℝ)..1, ‖rightLowEndpointPolynomial n t‖^2) ≤ (endpointCap n : ℝ)*(W*T)^2 :=
    wave_family_frequency_energy_le (endpoint_cap_le hn) _ _ _ _ _ W0 T0
      lowSteps (right_low_endpoint_frequency hn) lowWeights dBound
  have Z : (∫ t in (0 : ℝ)..1, ‖rightHighPolynomial n t‖^2) ≤ (n : ℝ)*(W*T)^2 :=
    wave_family_energy_le _ _ _ _ _ W0 T0 highSteps (fun _ _ => le_rfl) highWeights dBound
  have B₁ := norm_endpoint_pair_le hn (wave_family_continuous ..) (wave_family_continuous ..) Y l
  have B₂ := norm_endpoint_pair_le hn (wave_family_continuous ..) (wave_family_continuous ..) Z l
  have B₃ := norm_endpoint_pair_le hn (wave_family_continuous ..) (wave_family_continuous ..) L y
  unfold endpointContribution
  refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add B₁ B₂)) B₃).trans_eq ?_)
  unfold W
  ring

private theorem endpoint_contribution_saving : saving endpointContribution := by
  intro e he
  obtain ⟨D, D1, dBound⟩ := divisor_envelope
  let C := 3 * D^8
  have limit : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(54 / 1024) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 54 / 1024)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(54 / 1024) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have estimates : ∀ᶠ n : ℕ in atTop, ‖endpointContribution n‖ ≤ e * (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, eventually_log_budget_le, scaled.eventually_lt_const he]
      with n hn logBound small
    have nPos : 0 < n := by omega
    have nr : (0 : ℝ) < n := by exact_mod_cast nPos
    let X := (n : ℝ) ^ (1 / 1024 : ℝ)
    let T := D * X
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1
      (Real.one_le_rpow (by exact_mod_cast nPos) (by norm_num))
    have exp : (n : ℝ) ^ (15 / 16 : ℝ) * X^10 =
        (n : ℝ) ^ (-(54 / 1024) : ℝ) * (n : ℝ) := by
      unfold X
      rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le, ← Real.rpow_add nr]
      calc
        _ = (n : ℝ) ^ (-(54 / 1024) + 1 : ℝ) := by congr 1; norm_num
        _ = (n : ℝ) ^ (-(54 / 1024) : ℝ) * (n : ℝ) ^ (1 : ℝ) := Real.rpow_add nr _ _
        _ = _ := by rw [Real.rpow_one]
    refine (norm_endpoint_contribution_le nPos T1 (dBound n)).trans ?_
    calc
      _ ≤ 3*(n : ℝ)^(15/16 : ℝ) * (T^4*X)^2 := by
        have T0 := zero_le_one.trans T1
        have L0 := zero_le_one.trans (one_le_logBudget n)
        gcongr
      _ = C * ((n : ℝ) ^ (15 / 16 : ℝ) * X^10) := by unfold C T; ring
      _ = (C * (n : ℝ) ^ (-(54 / 1024) : ℝ)) * (n : ℝ) := by rw [exp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
  obtain ⟨N, bound⟩ := eventually_atTop.mp estimates
  exact ⟨N, fun n hn _ => bound n hn⟩

theorem frozen_iff_open_prefix : frozenGoal ↔ saving bilateralOpenPrefixRemainder := by
  rw [frozen_iff_bilateral_large_left]
  constructor <;> intro initial e he <;>
    obtain ⟨N, h⟩ := initial (e/2) (by positivity) <;>
    obtain ⟨M, hs⟩ := endpoint_contribution_saving (e/2) (by positivity) <;>
    refine ⟨max 1 (max N M), fun n hn even => ?_⟩
  · rw [bilateral_open_prefix_eq (by omega : 0 < n)]
    refine (norm_add_le _ _).trans ?_
    linarith only [h n (by omega) even, hs n (by omega) even]
  · have diff : bilateralLargeLeftRemainder n = bilateralOpenPrefixRemainder n - endpointContribution n := by
      rw [bilateral_open_prefix_eq (by omega : 0 < n)]
      abel
    rw [diff]
    refine (norm_sub_le _ _).trans ?_
    linarith only [h n (by omega) even, hs n (by omega) even]

end

end B13NondividingResidueReductionProof

end

/- Wide orbit -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry
open scoped Classical

noncomputable section

private theorem natural_interval_card_le (S : Finset ℕ) (c b : ℝ) (hb : 0 ≤ b)
    (within : ∀ j ∈ S, |(j : ℝ)-c| ≤ b) : (S.card : ℝ) ≤ 2*b+1 := by
  by_cases nonempty : S.Nonempty
  · let lo := S.min' nonempty
    let hi := S.max' nonempty
    have loMem := min'_mem S nonempty
    have hiMem := max'_mem S nonempty
    have subset : S ⊆ Icc lo hi := fun j hj => mem_Icc.mpr ⟨min'_le _ _ hj, le_max' _ _ hj⟩
    have ord : lo ≤ hi := (mem_Icc.mp (subset loMem)).2
    have boundLo := abs_le.mp (within lo loMem)
    have boundHi := abs_le.mp (within hi hiMem)
    calc
      _ ≤ ((Icc lo hi).card : ℝ) := by exact_mod_cast card_le_card subset
      _ = (hi : ℝ) + 1 - lo := by rw [Nat.card_Icc, Nat.cast_sub (ord.trans (Nat.le_succ _))]; push_cast; rfl
      _ ≤ _ := by linarith only [boundLo.1, boundHi.2]
  · have empty : S = ∅ := not_nonempty_iff_eq_empty.mp nonempty
    simp [empty]
    linarith only [hb]

def orbitArcPairs (q e : ℕ) (t b : ℝ) : Finset (ℕ × ℕ) :=
  (centers q e).filter (fun z => |t + (z.2 : ℝ)/e - (z.1 : ℝ)/q| ≤ b/q)

theorem orbit_arc_pairs_card_le {q e : ℕ} (hq : 0 < q) (he : 0 < e) (t b : ℝ) (hb : 0 ≤ b) :
    ((orbitArcPairs q e t b).card : ℝ) ≤ 8 * (e : ℝ) * b + 4 * (q.gcd e : ℝ) := by
  let d := q.gcd e
  let U := q/d
  let V := e/d
  have dp : 0 < d := Nat.gcd_pos_of_pos_left e hq
  have qD : d*U = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have eD : d*V = e := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have up : 0 < U := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left _ _)) dp
  have vp : 0 < V := Nat.div_pos (Nat.le_of_dvd he (Nat.gcd_dvd_right _ _)) dp
  have cc : U.Coprime V := Nat.coprime_div_gcd_div_gcd dp
  let C := (d : ℝ)*U*V
  let B := (V : ℝ)*b
  let f (m : ℕ) : ℝ := if abs ((m : ℝ) - abs (C*t)) ≤ B then 1 else 0
  have Cp : 0 < C := by
    unfold C
    exact mul_pos (mul_pos (by exact_mod_cast dp) (by exact_mod_cast up)) (by exact_mod_cast vp)
  have B0 : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hb
  have one (z : ℕ × ℕ) (hz : z ∈ orbitArcPairs q e t b) :
      f (delta U V z).natAbs = 1 := by
    have hit := (mem_filter.mp hz).2
    have deltaEq : ((delta U V z : ℤ) : ℝ) =
        (d : ℝ)*U*V * ((z.1 : ℝ)/q - (z.2 : ℝ)/e) := by
      have dPos : (0 : ℝ) < d := by exact_mod_cast dp
      have uPos : (0 : ℝ) < U := by exact_mod_cast up
      have vPos : (0 : ℝ) < V := by exact_mod_cast vp
      rw [← qD, ← eD]
      simp only [delta, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
      field_simp <;> ring
    have exactAbs :
        |((delta U V z : ℤ) : ℝ) - C*t| =
          C * |t + (z.2 : ℝ)/e - (z.1 : ℝ)/q| := by
      rw [deltaEq]
      change |C * ((z.1 : ℝ)/q - (z.2 : ℝ)/e) - C*t| = _
      rw [← mul_sub, abs_mul, abs_of_nonneg Cp.le]
      congr 1
      rw [abs_sub_comm]
      congr 1
      ring
    have multiplied : |((delta U V z : ℤ) : ℝ) - C*t| ≤ B := by
      rw [exactAbs]
      refine (mul_le_mul_of_nonneg_left hit Cp.le).trans_eq ?_
      unfold C B
      rw [← qD, Nat.cast_mul]
      have dPos : (0 : ℝ) < d := by exact_mod_cast dp
      have uPos : (0 : ℝ) < U := by exact_mod_cast up
      field_simp <;> ring
    have bound : abs (((delta U V z).natAbs : ℝ) - abs (C*t)) ≤ B := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact (abs_abs_sub_abs_le_abs_sub _ _).trans multiplied
    exact if_pos bound
  have f0 (m : ℕ) : 0 ≤ f m := by unfold f; split_ifs <;> norm_num
  have transfer : ((orbitArcPairs q e t b).card : ℝ) ≤
      ∑ z ∈ centers (d*U) (d*V), f (delta U V z).natAbs := by
    rw [qD,eD]
    calc
      _ = ∑ _ ∈ orbitArcPairs q e t b, (1 : ℝ) := by simp
      _ = ∑ z ∈ orbitArcPairs q e t b, f (delta U V z).natAbs :=
        sum_congr rfl fun z hz => (one z hz).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => f0 _)
  have bins : (∑ m ∈ range (d*U*V+1), f m) ≤ 2*B+1 := by
    unfold f
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    exact natural_interval_card_le _ _ _ B0 (fun m hm => (mem_filter.mp hm).2)
  have dor : (1 : ℝ) ≤ d := by exact_mod_cast dp
  calc
    _ ≤ 2*((d : ℝ)+1) * ∑ m ∈ range (d*U*V+1), f m :=
      transfer.trans (latticeSum d U V dp up vp cc f f0)
    _ ≤ (2*((d : ℝ)+1))*(2*B+1) := mul_le_mul_of_nonneg_left bins (by positivity)
    _ ≤ (4*(d : ℝ))*(2*B+1) :=
      mul_le_mul_of_nonneg_right (by linarith only [dor]) (by positivity)
    _ = _ := by
      have eEq : (e : ℝ) = (d : ℝ)*V := by exact_mod_cast eD.symm
      rw [eEq]
      unfold B d
      ring

private theorem gcd_orbit_sum_le (Q e : ℕ) (he : 0 < e) :
    (∑ q ∈ Icc 1 Q, (q.gcd e : ℝ)) ≤ (Q : ℝ) * e.divisors.card := by
  let term (d q : ℕ) : ℝ := if d ∣ q then d else 0
  have point (q : ℕ) : (q.gcd e : ℝ) ≤ ∑ d ∈ e.divisors, term d q := by
    have mem : q.gcd e ∈ e.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,he.ne'⟩
    refine (show (q.gcd e : ℝ) = term (q.gcd e) q from (if_pos (Nat.gcd_dvd_left _ _)).symm).le.trans ?_
    exact single_le_sum (f := fun d => term d q) (fun d _ => by unfold term; split_ifs <;> positivity) mem
  have row (d : ℕ) (hd : d ∈ e.divisors) : (∑ q ∈ Icc 1 Q, term d q) ≤ (Q : ℝ) := by
    let S := (Icc 1 Q).filter (fun q => d ∣ q)
    have dp := Nat.pos_of_mem_divisors hd
    have bound : S.card ≤ Q/d := by
      calc
        _ ≤ (Icc 1 (Q/d)).card := by
          apply card_le_card_of_injOn (fun q => q/d)
          · intro q hq
            have hq' : q ∈ S := hq
            have ⟨inside,div⟩ := mem_filter.mp hq'
            have qPos : 0 < q := (mem_Icc.mp inside).1
            have qDiv := Nat.div_pos (Nat.le_of_dvd qPos div) dp
            exact mem_Icc.mpr ⟨qDiv, Nat.div_le_div_right (mem_Icc.mp inside).2⟩
          · intro q hq w hw agree
            have hq' : q ∈ S := hq
            have hw' : w ∈ S := hw
            exact (Nat.div_mul_cancel (mem_filter.mp hq').2).symm.trans
              ((congrArg (fun k : ℕ => k*d) agree).trans (Nat.div_mul_cancel (mem_filter.mp hw').2))
        _ = _ := by simp
    unfold term
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    exact_mod_cast (Nat.mul_le_mul_right d bound).trans (Nat.div_mul_le_self Q d)
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ∑ d ∈ e.divisors, term d q := sum_le_sum fun q _ => point q
    _ = ∑ d ∈ e.divisors, ∑ q ∈ Icc 1 Q, term d q := sum_comm
    _ ≤ ∑ _ ∈ e.divisors, (Q : ℝ) := sum_le_sum row
    _ = _ := by rw [sum_const,nsmul_eq_mul,mul_comm]

theorem wide_orbit_hits_le (n Q H e : ℕ) (hn : 0 < n) (he : 0 < e) (t : ℝ) :
    (((range e).filter (fun j : ℕ => t + (j : ℝ)/(e : ℝ) ∈ wide n Q H)).card : ℝ) ≤
      8 * (e : ℝ) * ((H : ℝ)/(n : ℝ)) * Q + 4 * (Q : ℝ) * e.divisors.card := by
  let S := (range e).filter (fun j : ℕ => t + (j : ℝ)/(e : ℝ) ∈ wide n Q H)
  let b := (H : ℝ)/(n : ℝ)
  let hit (q : ℕ) := (orbitArcPairs q e t b).image Prod.snd
  have sub : S ⊆ (Icc 1 Q).biUnion hit := by
    intro j hj
    obtain ⟨index, q, a, qPos, qBound, aBound, _, close⟩ := mem_filter.mp hj
    refine mem_biUnion.mpr ⟨q,mem_Icc.mpr ⟨qPos,qBound⟩, mem_image.mpr ⟨(a,j), ?_, rfl⟩⟩
    have scaled : (H : ℝ) / ((q : ℝ)*n) = b/(q : ℝ) := by unfold b; ring
    rw [scaled] at close
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le aBound),
      mem_range.mpr ((mem_range.mp index).trans (Nat.lt_succ_self e))⟩, close⟩
  have csum : S.card ≤ ∑ q ∈ Icc 1 Q, (hit q).card :=
    (card_le_card sub).trans card_biUnion_le
  have every (q : ℕ) (hq : q ∈ Icc 1 Q) :
      ((hit q).card : ℝ) ≤ 8*(e : ℝ)*b + 4*(q.gcd e : ℝ) :=
    (show ((hit q).card : ℝ) ≤ (orbitArcPairs q e t b).card by exact_mod_cast card_image_le).trans
      (orbit_arc_pairs_card_le (mem_Icc.mp hq).1 he t b (by unfold b; positivity))
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ((hit q).card : ℝ) := by exact_mod_cast csum
    _ ≤ ∑ q ∈ Icc 1 Q, (8*(e : ℝ)*b + 4*(q.gcd e : ℝ)) := sum_le_sum every
    _ = (Q : ℝ)*(8*(e : ℝ)*b) + 4*∑ q ∈ Icc 1 Q, (q.gcd e : ℝ) := by
      simp only [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← mul_sum]
    _ ≤ (Q : ℝ)*(8*(e : ℝ)*b) + 4*((Q : ℝ)*e.divisors.card) :=
      (add_le_add) le_rfl (mul_le_mul_of_nonneg_left (gcd_orbit_sum_le Q e he) (by norm_num))
    _ = _ := by unfold b; ring

end

end B13NondividingResidueReductionProof

end

/- Wide periodic energy -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open scoped Classical

noncomputable section

private theorem unit_integral_eq_shifted_cells {e : ℕ} (he : 0 < e) (f : ℝ → ℝ)
    (int : ∀ a b : ℝ, a ≤ b → IntervalIntegrable f volume a b) :
    (∫ t in (0 : ℝ)..1, f t) =
      ∑ j ∈ range e, ∫ t in (0 : ℝ)..(1/(e : ℝ)), f (t+(j : ℝ)/e) := by
  have er : (0 : ℝ) < e := by exact_mod_cast he
  let endpoint (j : ℕ) := (j : ℝ)/e
  have h (j : ℕ) (_ : j < e) : IntervalIntegrable f volume (endpoint j) (endpoint (j+1)) := by
    apply int
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) er.le
  calc
    _ = ∑ j ∈ range e, ∫ t in endpoint j..endpoint (j+1), f t := by
      simpa only [endpoint, Nat.cast_zero, zero_div, div_self er.ne'] using
        (intervalIntegral.sum_integral_adjacent_intervals (a := endpoint) h).symm
    _ = _ := by
      refine sum_congr rfl fun j _ => ?_
      have upper : endpoint (j+1) = 1/(e : ℝ) + (j : ℝ)/e := by
        unfold endpoint
        push_cast
        ring
      rw [upper]
      simpa only [endpoint, zero_add] using
        (intervalIntegral.integral_comp_add_right f ((j : ℝ)/e) (a := 0) (b := 1/(e : ℝ))).symm

theorem wide_periodic_energy_le (n Q H e : ℕ) (hn : 0 < n) (he : 0 < e) (F : ℝ → ℂ)
    (fc : Continuous F) (shift : ∀ (j : ℕ) (t : ℝ), F (t+(j : ℝ)/e) = F t) :
    (∫ t in (0 : ℝ)..1, (wide n Q H).indicator (fun x => ‖F x‖^2) t) ≤
      (8 * (Q : ℝ) * ((H : ℝ)/(n : ℝ)) +
        4 * (Q : ℝ) * (e.divisors.card : ℝ) / e) *
        (∫ t in (0 : ℝ)..1, ‖F t‖^2) := by
  let len := 1/(e : ℝ)
  let W := wide n Q H
  let P (t : ℝ) := ‖F t‖^2
  let f := W.indicator P
  let C := 8 * (e : ℝ) * ((H : ℝ)/(n : ℝ)) * Q + 4 * (Q : ℝ) * e.divisors.card
  have er : (0 : ℝ) < e := by exact_mod_cast he
  have len0 : 0 ≤ len := by unfold len; positivity
  have pc : Continuous P := fc.norm.pow 2
  have fInt (a b : ℝ) (ord : a ≤ b) : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ord]
    exact (pc.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator (wide_measurable ..)
  have shiftInt (j : ℕ) : IntervalIntegrable (fun t => f (t+(j : ℝ)/e)) volume 0 len := by
    let c := (j : ℝ)/e
    have int := (fInt c (len+c) (by linarith only [len0])).comp_add_right c
    simpa only [sub_self, add_sub_cancel_right] using int
  have count (t : ℝ) :
      (∑ j ∈ range e, f (t+(j : ℝ)/e)) =
        (((range e).filter (fun j : ℕ => t+(j : ℝ)/e ∈ W)).card : ℝ) * P t := by
    calc
      _ = ∑ j ∈ range e, if t+(j : ℝ)/e ∈ W then P t else 0 := by
        refine sum_congr rfl fun j _ => ?_
        by_cases hit : t+(j : ℝ)/e ∈ W <;> simp [f,hit,P,shift]
      _ = _ := by rw [← sum_filter, sum_const, nsmul_eq_mul]
  have whole : (∫ t in (0 : ℝ)..1, P t) = (e : ℝ) * (∫ t in (0 : ℝ)..len, P t) := by
    rw [unit_integral_eq_shifted_cells he P (fun a b _ => pc.intervalIntegrable a b)]
    change (∑ j ∈ range e, ∫ t in (0 : ℝ)..len, P (t+(j : ℝ)/e)) = _
    have each (j : ℕ) : (∫ t in (0 : ℝ)..len, P (t+(j : ℝ)/e)) =
        ∫ t in (0 : ℝ)..len, P t :=
      intervalIntegral.integral_congr fun t _ => by simp [P,shift]
    simp only [each,sum_const,card_range,nsmul_eq_mul]
  change (∫ t in (0 : ℝ)..1, f t) ≤ _
  calc
    _ = ∫ t in (0 : ℝ)..len, ∑ j ∈ range e, f (t+(j : ℝ)/e) := by
      rw [unit_integral_eq_shifted_cells he f fInt,
        intervalIntegral.integral_finsetSum (fun j _ => shiftInt j)]
    _ ≤ ∫ t in (0 : ℝ)..len, C * P t := by
      apply intervalIntegral.integral_mono_on len0
      · have int := IntervalIntegrable.sum (range e) (fun j _ => shiftInt j)
        convert int using 1
        funext t
        simp only [Finset.sum_apply]
      · exact (pc.intervalIntegrable 0 len).const_mul _
      · intro t _
        rw [count]
        exact mul_le_mul_of_nonneg_right (wide_orbit_hits_le n Q H e hn he t) (sq_nonneg _)
    _ = C * ∫ t in (0 : ℝ)..len, P t := intervalIntegral.integral_const_mul ..
    _ = (8 * (Q : ℝ) * ((H : ℝ)/(n : ℝ)) +
        4 * (Q : ℝ) * (e.divisors.card : ℝ) / e) * ((e : ℝ) * (∫ t in (0 : ℝ)..len, P t)) := by
      unfold C
      field_simp
    _ = _ := by rw [← whole]

end

end B13NondividingResidueReductionProof

end

/- Large gcd weights -/
section

namespace B13NondividingResidueReductionProof

open Finset
open ArithmeticFunction DyadicMixedB4MoebiusGauss
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def largeDivisorIndicator (D : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun e => if D < e then 1 else 0, by simp⟩

def largeGcdDivisorWeight (D : ℕ) : ArithmeticFunction ℝ :=
  largeDivisorIndicator D * (μ : ArithmeticFunction ℝ)

theorem large_gcd_divisor_weight_sum (D g : ℕ) :
    (∑ e ∈ g.divisors, largeGcdDivisorWeight D e) = if D < g then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply]
  change ((largeDivisorIndicator D * (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ) g) = _
  rw [mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  rfl

theorem large_gcd_divisor_weight_zero {D e : ℕ} (he : e ≤ D) : largeGcdDivisorWeight D e = 0 := by
  unfold largeGcdDivisorWeight
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b =>
    largeDivisorIndicator D a * ((μ : ArithmeticFunction ℝ) b))]
  refine sum_eq_zero fun d hd => ?_
  have bound := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.dvd_of_mem_divisors hd)
  simp [largeDivisorIndicator,not_lt_of_ge (bound.trans he)]

theorem norm_large_gcd_divisor_weight_le (D e : ℕ) :
    ‖(largeGcdDivisorWeight D e : ℂ)‖ ≤ e.divisors.card := by
  unfold largeGcdDivisorWeight
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b =>
    largeDivisorIndicator D a * ((μ : ArithmeticFunction ℝ) b)), Complex.ofReal_sum]
  calc
    _ ≤ ∑ d ∈ e.divisors, ‖((largeDivisorIndicator D d * ((μ : ArithmeticFunction ℝ) (e/d)) : ℝ) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ ∈ e.divisors, (1 : ℝ) := by
      refine sum_le_sum fun d _ => ?_
      rw [Complex.ofReal_mul, norm_mul]
      have A : ‖(largeDivisorIndicator D d : ℂ)‖ ≤ 1 := by
        unfold largeDivisorIndicator
        by_cases h : D < d <;> simp [h]
      have B : ‖(((μ : ArithmeticFunction ℝ) (e/d) : ℝ) : ℂ)‖ ≤ 1 := by
        simpa [moebiusComplex] using norm_moebiusComplex_le_one (e/d)
      exact (mul_le_mul A B (norm_nonneg _) zero_le_one).trans_eq (by ring)
    _ = _ := by simp

theorem large_gcd_gate_eq_sum {D n u v : ℕ} (hu : 0 < u) (uBound : u ≤ n) :
    (if D < u.gcd v then (1 : ℂ) else 0) =
      ∑ e ∈ Ioc D n, if e ∣ u ∧ e ∣ v then (largeGcdDivisorWeight D e : ℂ) else 0 := by
  have gPos : 0 < u.gcd v := Nat.gcd_pos_of_pos_left v hu
  have gBound : u.gcd v ≤ n := (Nat.gcd_le_left v hu).trans uBound
  have cut : (Ioc D n).filter (fun e => e ∣ u ∧ e ∣ v) =
      (u.gcd v).divisors.filter (fun e => D < e) := by
    ext e
    simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
    exact ⟨fun h => ⟨⟨Nat.dvd_gcd h.2.1 h.2.2,gPos.ne'⟩,h.1.1⟩,
      fun h => ⟨⟨h.2,(Nat.le_of_dvd gPos h.1.1).trans gBound⟩,
        h.1.1.trans (Nat.gcd_dvd_left _ _), h.1.1.trans (Nat.gcd_dvd_right _ _)⟩⟩
  have scalar := congrArg Complex.ofReal (large_gcd_divisor_weight_sum D (u.gcd v))
  simp only [Complex.ofReal_sum] at scalar
  simp only [← sum_filter, cut]
  have full : (∑ e ∈ (u.gcd v).divisors.filter (fun e => D < e), (largeGcdDivisorWeight D e : ℂ)) =
      ∑ e ∈ (u.gcd v).divisors, (largeGcdDivisorWeight D e : ℂ) := by
    refine sum_subset (filter_subset _ _) fun e he outside => ?_
    have small : e ≤ D := le_of_not_gt fun big => outside (mem_filter.mpr ⟨he,big⟩)
    rw [large_gcd_divisor_weight_zero small, Complex.ofReal_zero]
  rw [full, scalar]
  split_ifs <;> simp

end

end B13NondividingResidueReductionProof

end

/- Divisible minor energy -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4OffWaveMoment DyadicMixedB4Scale
open scoped Classical

noncomputable section

private def targetPhase (n : ℕ) (t : ℝ) : ℂ := phase (((-(n : ℤ)) : ℝ)*t)

private theorem target_phase_cont (n : ℕ) : Continuous (targetPhase n) := by
  unfold targetPhase phase
  fun_prop

private theorem norm_masked_wave_products_le (n : ℕ) (F G : ℝ → ℂ)
    (fc : Continuous F) (gc : Continuous G) {S : Set ℝ} (meas : MeasurableSet S) :
    ‖∫ t in (0 : ℝ)..1, S.indicator (fun x => targetPhase n x * (F x * G x)) t‖ ≤
      (1/2 : ℝ) * ((∫ t in (0 : ℝ)..1, S.indicator (fun x => ‖F x‖^2) t) +
        (∫ t in (0 : ℝ)..1, S.indicator (fun x => ‖G x‖^2) t)) := by
  let H := S.indicator (fun x => targetPhase n x * (F x * G x))
  let A := S.indicator (fun x => ‖F x‖^2)
  let B := S.indicator (fun x => ‖G x‖^2)
  have hInt : IntervalIntegrable H volume 0 1 :=
    indicator_intervalIntegrable ((target_phase_cont n).mul (fc.mul gc)) meas
  have intSq (f : ℝ → ℂ) (hf : Continuous f) :
      IntervalIntegrable (S.indicator (fun t => ‖f t‖^2)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact ((hf.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator meas
  have first := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := H)
    (show (0 : ℝ) ≤ 1 from zero_le_one)
  have bound : (∫ t in (0 : ℝ)..1, ‖H t‖) ≤ ∫ t in (0 : ℝ)..1, (1/2 : ℝ) * (A t + B t) := by
    apply intervalIntegral.integral_mono_on zero_le_one hInt.norm (((intSq F fc).add (intSq G gc)).const_mul _)
    intro t _
    by_cases hit : t ∈ S
    · simp only [H, A, B, Set.indicator_of_mem hit, targetPhase, norm_mul, norm_phase', one_mul]
      nlinarith only [sq_nonneg (‖F t‖ - ‖G t‖)]
    · simp [H,A,B,hit]
  change ‖∫ t in (0 : ℝ)..1, H t‖ ≤ (1/2 : ℝ)*((∫ t in (0 : ℝ)..1, A t) + ∫ t in (0 : ℝ)..1, B t)
  refine first.trans (bound.trans_eq ?_)
  rw [intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (intSq F fc) (intSq G gc)]
  <;> rfl

theorem divisible_wave_product_full_zero {n e : ℕ} (bad : ¬ e ∣ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) :
    (∫ t in (0 : ℝ)..1, targetPhase n t *
       (divisibleStepPolynomial e I u l r a t * divisibleStepPolynomial e J v p s b t)) = 0 := by
  let A := I.filter (fun i => e ∣ u i)
  let B := J.filter (fun j => e ∣ v j)
  let term (i : α) (j : β) (t : ℝ) := a i*b j *
    (targetPhase n t * (wave (u i) (l i) (r i) t * wave (v j) (p j) (s j) t))
  have int (i : α) (j : β) : IntervalIntegrable (term i j) volume 0 1 := by
    have cont : Continuous (fun t => targetPhase n t *
        (wave (u i) (l i) (r i) t * wave (v j) (p j) (s j) t)) :=
      (target_phase_cont n).mul ((wave_continuous ..).mul (wave_continuous ..))
    exact (cont.intervalIntegrable 0 1).const_mul _
  have row (i : α) : IntervalIntegrable (fun t => ∑ j ∈ B, term i j t) volume 0 1 := by
    have good := IntervalIntegrable.sum B (fun j _ => int i j)
    convert good using 1
    funext t
    simp only [Finset.sum_apply]
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ i ∈ A, ∑ j ∈ B, term i j t := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      unfold divisibleStepPolynomial
      change targetPhase n t * ((∑ i ∈ A, a i * wave (u i) (l i) (r i) t) *
        (∑ j ∈ B, b j * wave (v j) (p j) (s j) t)) = _
      rw [sum_mul_sum,mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by unfold term; ring
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => row i)]
      refine sum_eq_zero fun i hi => ?_
      rw [intervalIntegral.integral_finsetSum (fun j _ => int i j)]
      refine sum_eq_zero fun j hj => ?_
      have cgcd : e ∣ (u i).gcd (v j) := Nat.dvd_gcd (mem_filter.mp hi).2 (mem_filter.mp hj).2
      have no : ¬ (u i).gcd (v j) ∣ n := fun yes => bad (cgcd.trans yes)
      unfold term targetPhase
      rw [intervalIntegral.integral_const_mul, full_wave_pair_eq_count, progression_pair_empty_of_not_gcd_dvd no]
      simp

theorem norm_periodic_minor_integral_le {n B H e : ℕ} (hn : 0 < n) (he : 0 < e)
    (F G : ℝ → ℂ) (fc : Continuous F) (gc : Continuous G)
    (fShift : ∀ (j : ℕ) (t : ℝ), F (t+(j : ℝ)/e) = F t)
    (gShift : ∀ (j : ℕ) (t : ℝ), G (t+(j : ℝ)/e) = G t)
    (zeroFull : ¬e ∣ n → (∫ t in (0 : ℝ)..1, targetPhase n t * (F t * G t)) = 0)
    {E : ℝ} (fNorm : (∫ t in (0 : ℝ)..1, ‖F t‖^2) ≤ E) (gNorm : (∫ t in (0 : ℝ)..1, ‖G t‖^2) ≤ E) :
    ‖∫ t in (0 : ℝ)..1, (wide n B H)ᶜ.indicator (fun x => targetPhase n x * (F x * G x)) t‖ ≤
      ((if e ∣ n then 1 else 0) + 8 * (B : ℝ) * ((H : ℝ)/(n : ℝ)) +
        4 * (B : ℝ) * (e.divisors.card : ℝ) / e) * E := by
  let W := wide n B H
  let Fg (t : ℝ) := targetPhase n t * (F t * G t)
  let P := 8 * (B : ℝ) * ((H : ℝ)/(n : ℝ)) + 4 * (B : ℝ) * (e.divisors.card : ℝ) / e
  have pc : 0 ≤ P := by unfold P; positivity
  have cont : Continuous Fg := (target_phase_cont n).mul (fc.mul gc)
  have measW : MeasurableSet W := wide_measurable ..
  have eq : (∫ t in (0 : ℝ)..1, Wᶜ.indicator Fg t) + (∫ t in (0 : ℝ)..1, W.indicator Fg t) =
      ∫ t in (0 : ℝ)..1, Fg t := by
    rw [← intervalIntegral.integral_add (indicator_intervalIntegrable cont measW.compl)
      (indicator_intervalIntegrable cont measW)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    by_cases inside : t ∈ W <;> simp [inside]
  have big : ‖∫ t in (0 : ℝ)..1, Fg t‖ ≤ (if e ∣ n then (1:ℝ) else 0) * E := by
    by_cases divide : e ∣ n
    · simp only [divide, ite_true, one_mul]
      have estimate := norm_masked_wave_products_le n F G fc gc MeasurableSet.univ
      simp only [Set.indicator_univ] at estimate
      exact estimate.trans (by linarith only [fNorm,gNorm])
    · have zero : (∫ t in (0 : ℝ)..1, Fg t) = 0 := zeroFull divide
      simp [zero,divide]
  have small : ‖∫ t in (0 : ℝ)..1, W.indicator Fg t‖ ≤ P * E := by
    have f1 := (wide_periodic_energy_le n B H e hn he F fc fShift).trans
      (mul_le_mul_of_nonneg_left fNorm pc)
    have g1 := (wide_periodic_energy_le n B H e hn he G gc gShift).trans
      (mul_le_mul_of_nonneg_left gNorm pc)
    refine (norm_masked_wave_products_le n F G fc gc (wide_measurable ..)).trans ?_
    change _ ≤ P * E
    linarith only [f1,g1]
  change ‖∫ t in (0 : ℝ)..1, Wᶜ.indicator Fg t‖ ≤ _
  rw [eq_sub_of_add_eq eq]
  refine (norm_sub_le _ _).trans ((add_le_add big small).trans_eq ?_)
  unfold P
  ring

end

end B13NondividingResidueReductionProof

end

/- Large gcd family -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4Scale DyadicMixedB4OffWaveMoment
open scoped Classical

noncomputable section

def largeGcdFamily (n D : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if D < (u i).gcd (v j) then
    a i * b j * productStepDeepIntegral n (u i) (v j) (l i) (r i) (p j) (s j) else 0

private def divPair (n e : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (wide n (cutoffB n) (cutoffH n))ᶜ.indicator
    (fun x => phase (((-(n : ℤ)) : ℝ)*x) *
      (divisibleStepPolynomial e I u l r a x * divisibleStepPolynomial e J v p s b x)) t

private theorem divPair_eq_sum (n e : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) :
    divPair n e I J u l r v p s a b =
      ∑ i ∈ I.filter (fun i => e ∣ u i), ∑ j ∈ J.filter (fun j => e ∣ v j),
        a i * b j * productStepDeepIntegral n (u i) (v j) (l i) (r i) (p j) (s j) := by
  unfold divPair divisibleStepPolynomial
  rw [two_wave_sums_partition]
  unfold shortProductFamily longProductFamily
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases small : u i * v j ≤ maximumStep n^2
  · simp [small,not_lt_of_ge small]
  · simp [small,lt_of_not_ge small]

private theorem large_gcd_family_eq_divPairs (n D : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ)
    (uRange : ∀ i ∈ I, u i ∈ Icc 1 n) :
    largeGcdFamily n D I J u l r v p s a b =
      ∑ e ∈ Ioc D n, (largeGcdDivisorWeight D e : ℂ) * divPair n e I J u l r v p s a b := by
  let X := Ioc D n
  let term (i : α) (j : β) := a i * b j * productStepDeepIntegral n (u i) (v j) (l i) (r i) (p j) (s j)
  let w (e : ℕ) := (largeGcdDivisorWeight D e : ℂ)
  let value (e : ℕ) (i : α) (j : β) := if e ∣ u i ∧ e ∣ v j then w e * term i j else 0
  unfold largeGcdFamily
  calc
    _ = ∑ i ∈ I, ∑ j ∈ J, ∑ e ∈ X, value e i j := by
      refine sum_congr rfl fun i hi => sum_congr rfl fun j _ => ?_
      have range := mem_Icc.mp (uRange i hi)
      calc
        _ = (if D < (u i).gcd (v j) then (1:ℂ) else 0) * term i j := by split_ifs <;> simp [term]
        _ = _ := by
          rw [large_gcd_gate_eq_sum range.1 range.2, sum_mul]
          refine sum_congr rfl fun e _ => ?_
          by_cases h : e ∣ u i ∧ e ∣ v j <;> simp [h,w,value]
    _ = ∑ i ∈ I, ∑ e ∈ X, ∑ j ∈ J, value e i j := sum_congr rfl fun _ _ => sum_comm
    _ = ∑ e ∈ X, ∑ i ∈ I, ∑ j ∈ J, value e i j := sum_comm
    _ = _ := by
      refine sum_congr rfl fun e _ => ?_
      rw [divPair_eq_sum, mul_sum, sum_filter]
      refine sum_congr rfl fun i _ => ?_
      by_cases h : e ∣ u i
      · simp only [h, ite_true]
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun j _ => ?_
        by_cases gate : e ∣ v j <;> simp [value,term,w,h,gate]
      · simp [value,h]

theorem norm_large_gcd_family_le (n D : ℕ) (hn : 0 < n) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) {W T : ℝ}
    (W0 : 0 ≤ W) (T0 : 0 ≤ T)
    (uRange : ∀ i ∈ I, u i ∈ Icc 1 n) (vRange : ∀ j ∈ J, v j ∈ Icc 1 n)
    (uEnds : ∀ i ∈ I, r i ≤ n/u i) (vEnds : ∀ j ∈ J, s j ≤ n/v j)
    (uBound : ∀ x ∈ Icc 1 n, (∑ i ∈ I.filter (fun i => u i = x), ‖a i‖) ≤ W)
    (vBound : ∀ y ∈ Icc 1 n, (∑ j ∈ J.filter (fun j => v j = y), ‖b j‖) ≤ W)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖largeGcdFamily n D I J u l r v p s a b‖ ≤
      ∑ e ∈ Ioc D n, (e.divisors.card : ℝ) *
        (((if e ∣ n then 1 else 0) + 8 * (cutoffB n : ℝ) * ((cutoffH n : ℝ)/(n : ℝ)) +
          4 * (cutoffB n : ℝ) * e.divisors.card / e) * ((n : ℝ)/e * (W*T)^2)) := by
  rw [large_gcd_family_eq_divPairs n D I J u l r v p s a b uRange]
  refine (norm_sum_le _ _).trans (sum_le_sum fun e he => ?_)
  have ep : 0 < e := (Nat.zero_le _).trans_lt (mem_Ioc.mp he).1
  let F := divisibleStepPolynomial e I u l r a
  let G := divisibleStepPolynomial e J v p s b
  have fCont : Continuous F := by unfold F divisibleStepPolynomial
                                  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (wave_continuous ..))
  have gCont : Continuous G := by unfold G divisibleStepPolynomial
                                  exact continuous_finsetSum _ (fun j _ => continuous_const.mul (wave_continuous ..))
  have fNorm := divisible_step_energy_le n e I u l r a W0 T0 uRange uEnds uBound divisorBound
  have gNorm := divisible_step_energy_le n e J v p s b W0 T0 vRange vEnds vBound divisorBound
  have estimate := norm_periodic_minor_integral_le (B := cutoffB n) (H := cutoffH n) hn ep F G fCont gCont
    (divisible_step_polynomial_periodic e ep I u l r a)
    (divisible_step_polynomial_periodic e ep J v p s b)
    (fun no => divisible_wave_product_full_zero no I J u l r v p s a b) fNorm gNorm
  rw [norm_mul]
  refine mul_le_mul (norm_large_gcd_divisor_weight_le D e) estimate (norm_nonneg _) (Nat.cast_nonneg _)

end

end B13NondividingResidueReductionProof

end

/- Large gcd budget -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail
open DyadicMixedB4GcdHarmonic DyadicMixedB4ModulusTail
open scoped Classical

noncomputable section

private theorem gcd_reciprocal_divisor_tail_le (n M : ℕ) (mPos : 0 < M) (hn : 0 < n) :
    (∑ e ∈ Ioc M n, if e ∣ n then (e : ℝ)⁻¹ else 0) ≤ (n.divisors.card : ℝ) / M := by
  have mr : (0 : ℝ) < M := by exact_mod_cast mPos
  rw [← sum_filter]
  calc
    _ ≤ ∑ _ ∈ (Ioc M n).filter (fun e => e ∣ n), (M : ℝ)⁻¹ := by
      refine sum_le_sum fun e he => ?_
      have order : (M : ℝ) ≤ e := by exact_mod_cast (mem_Ioc.mp (mem_filter.mp he).1).1.le
      simpa only [one_div] using one_div_le_one_div_of_le mr order
    _ ≤ ∑ _ ∈ n.divisors, (M : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg
        (fun e he => Nat.mem_divisors.mpr ⟨(mem_filter.mp he).2,hn.ne'⟩) (fun _ _ _ => by positivity)
    _ = _ := by rw [sum_const,nsmul_eq_mul,div_eq_mul_inv]

private theorem gcd_reciprocal_all_tail_le (n M : ℕ) :
    (∑ e ∈ Ioc M n, (e : ℝ)⁻¹) ≤ 1+Real.log (n : ℝ) :=
  (sum_le_sum_of_subset_of_nonneg
    (fun e he => mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp he).1,(mem_Ioc.mp he).2⟩)
    (fun _ _ _ => by positivity)).trans (sum_inverse_Icc_le n)

private theorem gcd_inverse_square_tail_le (n M : ℕ) (mPos : 0 < M) :
    (∑ e ∈ Ioc M n, 1/(e : ℝ)^2) ≤ 2/(M : ℝ) := by
  have eq : Ioc M n = Icc (M+1) n := by ext e; simp only [mem_Ioc,mem_Icc]; omega
  have mr : (0 : ℝ) < M := by exact_mod_cast mPos
  rw [eq]
  exact (inverse_square_tail_Icc (M+1) n (Nat.succ_pos M)).trans
    (div_le_div_of_nonneg_left (by norm_num) mr (by exact_mod_cast Nat.le_succ M))

theorem gcd_minor_scalar_budget {n M B H : ℕ} (hn : 0 < n) (mPos : 0 < M) (bPos : 0 < B)
    {T W : ℝ} (T0 : 0 ≤ T) (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    (∑ e ∈ Ioc M n, (e.divisors.card : ℝ) *
      (((if e ∣ n then 1 else 0) + 8 * (B : ℝ) * ((H : ℝ)/(n : ℝ)) +
        4 * (B : ℝ) * e.divisors.card / e) * ((n : ℝ)/e * (W*T)^2))) ≤
      (W*T)^2 * (9 * (n : ℝ) * B * T^2 / M + 8*T*B*H*(1+Real.log (n : ℝ))) := by
  let S := Ioc M n
  let E := (W*T)^2
  let w (e : ℕ) : ℝ := if e ∣ n then (e : ℝ)⁻¹ else 0
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have mr : (0 : ℝ) < M := by exact_mod_cast mPos
  have br : (1 : ℝ) ≤ B := by exact_mod_cast bPos
  have h (e : ℕ) (he : e ∈ S) :
      (e.divisors.card : ℝ) *
        (((if e ∣ n then 1 else 0) + 8 * (B : ℝ) * ((H : ℝ)/(n : ℝ)) +
          4 * (B : ℝ) * e.divisors.card / e) * ((n : ℝ)/e * E)) ≤
        E * ((T*n)*w e + (8*T*B*H)*(e : ℝ)⁻¹ + (4*T^2*n*B)*(1/(e : ℝ)^2)) := by
    have er : (0 : ℝ) < e := by exact_mod_cast ((Nat.zero_le _).trans_lt (mem_Ioc.mp he).1)
    have db := divisorBound e (mem_Ioc.mp he).2
    have gate0 : 0 ≤ (if e ∣ n then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    calc
      _ ≤ T * (((if e ∣ n then 1 else 0) + 8 * (B : ℝ) * ((H : ℝ)/(n : ℝ)) +
          4 * (B : ℝ) * T / e) * ((n : ℝ)/e * E)) := by
        gcongr
      _ = _ := by by_cases h : e ∣ n <;> simp only [h, ite_true, ite_false, w] <;> field_simp <;> ring
  have t1 := (gcd_reciprocal_divisor_tail_le n M mPos hn).trans
    (div_le_div_of_nonneg_right (divisorBound n le_rfl) mr.le)
  have t2 := gcd_reciprocal_all_tail_le n M
  have t3 := gcd_inverse_square_tail_le n M mPos
  have join : (T*(n:ℝ))*(T/(M:ℝ)) + (4*T^2*(n:ℝ)*B)*(2/(M:ℝ)) ≤
      9*(n:ℝ)*B*T^2/M := by
    calc
      _ = (1+8*(B : ℝ)) * ((n : ℝ)*T^2/M) := by ring
      _ ≤ (9*(B : ℝ)) * ((n : ℝ)*T^2/M) :=
        mul_le_mul_of_nonneg_right (by linarith only [br]) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ e ∈ S, E * ((T*n)*w e + (8*T*B*H)*(e : ℝ)⁻¹ + (4*T^2*n*B)*(1/(e : ℝ)^2)) :=
      sum_le_sum h
    _ = E * ((T*n)*(∑ e ∈ S, w e) + (8*T*B*H)*(∑ e ∈ S, (e : ℝ)⁻¹) +
        (4*T^2*n*B)*(∑ e ∈ S, 1/(e : ℝ)^2)) := by
      simp only [← mul_sum, sum_add_distrib]
    _ ≤ E * ((T*n)*(T/(M:ℝ)) + (8*T*B*H)*(1+Real.log (n : ℝ)) +
        (4*T^2*n*B)*(2/(M:ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_left t1 (by positivity))
          (mul_le_mul_of_nonneg_left t2 (by positivity))) (mul_le_mul_of_nonneg_left t3 (by positivity)))
        (sq_nonneg _)
    _ = E * (((T*n)*(T/(M:ℝ)) + (4*T^2*n*B)*(2/(M:ℝ))) + (8*T*B*H)*(1+Real.log (n : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add join le_rfl) (sq_nonneg _)

theorem gcd_minor_budget_at_cutoffs (n : ℕ) (nLower : 2 ≤ n) {T : ℝ} (T1 : 1 ≤ T)
    (divisorBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    (∑ e ∈ Ioc (maximumStep n) n, (e.divisors.card : ℝ) *
      (((if e ∣ n then 1 else 0) + 8 * (cutoffB n : ℝ) * ((cutoffH n : ℝ)/(n : ℝ)) +
        4 * (cutoffB n : ℝ) * e.divisors.card / e) *
          ((n : ℝ)/e * ((T^3 * logBudget n)*T)^2))) ≤
      32804 * (n : ℝ) ^ (7/8 : ℝ) * T^10 * logBudget n^5 := by
  have hn : 0 < n := by omega
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have T0 := zero_le_one.trans T1
  have cut := cutoffs_ordered n hn
  have bPos : 0 < cutoffB n := cut.1.trans cut.2.1
  have mPos : 0 < maximumStep n := bPos.trans_le cut.2.2.1
  have mr : (0 : ℝ) < maximumStep n := by exact_mod_cast mPos
  let L := logBudget n
  have L1 : 1 ≤ L := one_le_logBudget n
  have L0 : 0 ≤ L := zero_le_one.trans L1
  have A : (1+Real.log (n : ℝ)) ≤ L := by unfold L logBudget; gcongr; linarith
  have bUpper : (cutoffB n : ℝ) ≤ (n : ℝ) ^ (1/3 : ℝ) :=
    Nat.floor_le (by positivity)
  have mLower := maximumStep_divisor_lower n hn
  have first : (n : ℝ)*cutoffB n / maximumStep n ≤ 4 * (n : ℝ) ^ (7/8 : ℝ) := by
    apply (div_le_iff₀ mr).mpr
    calc
      _ ≤ (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1/3 : ℝ) := by rw [Real.rpow_one]; gcongr
      _ = (n : ℝ) ^ (643/768 : ℝ) * (n : ℝ) ^ (127/256 : ℝ) := by
        rw [← Real.rpow_add nr, ← Real.rpow_add nr]
        congr 1
        norm_num
      _ = (4 * (n : ℝ) ^ (643/768 : ℝ)) * ((n : ℝ) ^ (127/256 : ℝ) / 4) := by ring
      _ ≤ (4 * (n : ℝ) ^ (643/768 : ℝ)) * maximumStep n := by gcongr
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le nOne (by norm_num)) (by norm_num)) mr.le
  have Hbound : (cutoffB n : ℝ) * cutoffH n ≤ 4096 * (n : ℝ) ^ (7/8 : ℝ) * L^2 := by
    have hLog : (Nat.log 2 (n+2) : ℝ) ≤ 4*L :=
      (log2_le_four_log n nLower).trans (mul_le_mul_of_nonneg_left (log_le_logBudget hn le_rfl) (by norm_num))
    have bSq : (cutoffB n : ℝ)^2 ≤ (n : ℝ) ^ (7/8 : ℝ) := by
      calc
        _ ≤ ((n : ℝ) ^ (1/3 : ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) bUpper _
        _ = (n : ℝ) ^ (2/3 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le]; norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le nOne (by norm_num)
    calc
      _ = 256 * (cutoffB n : ℝ)^2 * (Nat.log 2 (n+2) : ℝ)^2 := by unfold cutoffH; push_cast; ring
      _ ≤ 256 * (n : ℝ) ^ (7/8 : ℝ) * (4*L)^2 := by gcongr
      _ = _ := by ring
  have inner1 : 9*(n:ℝ)*cutoffB n*T^2/maximumStep n ≤ 36*(n:ℝ)^(7/8:ℝ)*T^2*L^3 := by
    calc
      _ = 9*T^2*((n:ℝ)*cutoffB n/maximumStep n) := by ring
      _ ≤ 9*T^2*(4*(n:ℝ)^(7/8:ℝ)) := by gcongr
      _ ≤ _ := by
        have p : 1 ≤ L^3 := one_le_pow₀ L1
        calc
          _ = (36*(n:ℝ)^(7/8:ℝ)*T^2)*1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left p (by positivity)
  have inner2 : 8*T*cutoffB n*cutoffH n*(1+Real.log (n:ℝ)) ≤ 32768*(n:ℝ)^(7/8:ℝ)*T^2*L^3 := by
    have a0 : 0 ≤ 1+Real.log (n:ℝ) := add_nonneg zero_le_one (Real.log_nonneg nOne)
    calc
      _ = (8*T)*((cutoffB n:ℝ)*cutoffH n)*(1+Real.log (n:ℝ)) := by ring
      _ ≤ (8*T^2)*(4096*(n:ℝ)^(7/8:ℝ)*L^2)*L := by
        have tPower : T ≤ T^2 := by simpa using pow_le_pow_right₀ T1 (by decide : 1 ≤ 2)
        gcongr
      _ = _ := by ring
  refine (gcd_minor_scalar_budget hn mPos bPos T0 divisorBound (W := T^3*L)).trans ?_
  refine (mul_le_mul_of_nonneg_left (add_le_add inner1 inner2) (sq_nonneg _)).trans_eq ?_
  unfold L
  ring

end

end B13NondividingResidueReductionProof

end

/- Open initial segment cutoffs -/
section

namespace B13NondividingResidueReductionProof

open Finset Filter MeasureTheory
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail
open DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def cutWaveFamily (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J,
    if maximumStep n^2 < u i*v j ∧ (u i).gcd (v j) ≤ maximumStep n then
      a i * b j * productStepDeepIntegral n (u i) (v j) (l i) (r i) (p j) (s j)
    else 0

def removedWaveFamily (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) : ℂ :=
  shortProductFamily n I J u l r v p s a b + largeGcdFamily n (maximumStep n) I J u l r v p s a b

theorem masked_wave_product_eq_cut (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ)
    (uPositive : ∀ i ∈ I, 0 < u i) (vPositive : ∀ j ∈ J, 0 < v j) :
    maskedWaveProduct n (waveFamilyPolynomial I u l r a) (waveFamilyPolynomial J v p s b) =
      cutWaveFamily n I J u l r v p s a b + removedWaveFamily n I J u l r v p s a b := by
  have longEq : longProductFamily n I J u l r v p s a b =
      cutWaveFamily n I J u l r v p s a b + largeGcdFamily n (maximumStep n) I J u l r v p s a b := by
    unfold longProductFamily cutWaveFamily largeGcdFamily
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    by_cases large : maximumStep n < (u i).gcd (v j)
    · have big : maximumStep n^2 < u i * v j :=
        (Nat.pow_lt_pow_left large (by decide : 2 ≠ 0)).trans_le (by
          rw [pow_two]
          exact Nat.mul_le_mul (Nat.gcd_le_left _ (uPositive i hi)) (Nat.gcd_le_right _ (vPositive j hj)))
      simp [large,big,not_le_of_gt large]
    · have small : (u i).gcd (v j) ≤ maximumStep n := le_of_not_gt large
      simp [large,small]
  have eq : maskedWaveProduct n (waveFamilyPolynomial I u l r a) (waveFamilyPolynomial J v p s b) =
      _ := two_wave_sums_partition n I J u l r v p s a b
  rw [eq,longEq,removedWaveFamily]
  abel

private theorem short_product_scalar_bound {n : ℕ} (hn : 0 < n) {T : ℝ} (T1 : 1 ≤ T)
    (dBound : (n.divisors.card : ℝ) ≤ T) :
    (T^3*logBudget n)*(T^3*logBudget n) *
      (1152*(maximumStep n : ℝ)^2*logBudget n^3 +
        (64*(n : ℝ)*(n.divisors.card : ℝ)*logBudget n^2)/cutoffR n) ≤
      1280*(n : ℝ)^(127/128 : ℝ)*T^7*logBudget n^5 := by
  let L := logBudget n
  let X := (n : ℝ)^(127/128 : ℝ)
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have T0 := zero_le_one.trans T1
  have L1 := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have mSquare : (maximumStep n : ℝ)^2 ≤ X := by
    calc
      _ ≤ ((n : ℝ)^(127/256 : ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (maximumStep_le_power n hn) 2
      _ = _ := by unfold X; rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le]; norm_num
  have rLower : (n : ℝ)^(1/9 : ℝ)/2 ≤ (cutoffR n : ℝ) := floor_half_le (Real.one_le_rpow n1 (by norm_num))
  have rr : (0 : ℝ) < cutoffR n := by
    exact_mod_cast (show 0 < cutoffR n from (cutoffs_ordered n hn).1)
  have nDiv : (n : ℝ)/cutoffR n ≤ 2*X := by
    apply (div_le_iff₀ rr).mpr
    calc
      (n : ℝ) = (n : ℝ)^(8/9 : ℝ)*(n : ℝ)^(1/9 : ℝ) := by rw [← Real.rpow_add nr]; norm_num
      _ = (2*(n : ℝ)^(8/9 : ℝ))*((n : ℝ)^(1/9 : ℝ)/2) := by ring
      _ ≤ (2*X)*(cutoffR n : ℝ) := by
        have xx : (n : ℝ)^(8/9 : ℝ) ≤ X := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
        gcongr
  have first : (maximumStep n : ℝ)^2*(T^6*L^5) ≤ X*(T^7*L^5) := by
    have t : T^6 ≤ T^7 := pow_le_pow_right₀ T1 (by decide)
    gcongr
  have other : ((n : ℝ)/cutoffR n)*((n.divisors.card : ℝ)*T^6*L^4) ≤ (2*X)*(T^7*L^5) := by
    calc
      _ ≤ (2*X)*(T*T^6*L^5) := by
        have l : L^4 ≤ L^5 := pow_le_pow_right₀ L1 (by decide)
        gcongr
      _ = _ := by ring
  change (T^3*L)*(T^3*L)*_ ≤ 1280*X*T^7*L^5
  calc
    _ = 1152*((maximumStep n : ℝ)^2*(T^6*L^5)) +
        64*(((n : ℝ)/cutoffR n)*((n.divisors.card : ℝ)*T^6*L^4)) := by unfold L; ring
    _ ≤ 1152*(X*(T^7*L^5)) + 64*((2*X)*(T^7*L^5)) := by gcongr
    _ = _ := by ring

theorem norm_removed_wave_family_le (n : ℕ) (hn : 2 ≤ n)
    (width : 4*cutoffH n*maximumStep n ≤ n) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) {T : ℝ} (T1 : 1 ≤ T)
    (uSteps : ∀ i ∈ I, u i ∈ Icc 1 n) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 n)
    (uEnds : ∀ i ∈ I, r i ≤ n/u i) (vEnds : ∀ j ∈ J, s j ≤ n/v j)
    (uWeights : ∀ x ∈ Icc 1 n, (∑ i ∈ I.filter (fun i => u i = x), ‖a i‖) ≤ T^3*logBudget n)
    (vWeights : ∀ y ∈ Icc 1 n, (∑ j ∈ J.filter (fun j => v j = y), ‖b j‖) ≤ T^3*logBudget n)
    (dBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖removedWaveFamily n I J u l r v p s a b‖ ≤ 34084*(finalScale n T)^2/(n : ℝ) := by
  have nPos : 0 < n := by omega
  have nr : (0 : ℝ) < n := by exact_mod_cast nPos
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast nPos
  have T0 := zero_le_one.trans T1
  have L1 := one_le_logBudget n
  have W0 : 0 ≤ T^3*logBudget n := mul_nonneg (pow_nonneg T0 _) (zero_le_one.trans L1)
  have short := (norm_short_product_family_le n nPos width I J u l r v p s a b W0 W0
    uSteps vSteps uEnds vEnds uWeights vWeights).trans (short_product_scalar_bound nPos T1 (dBound n le_rfl))
  have gcd := (norm_large_gcd_family_le n (maximumStep n) nPos I J u l r v p s a b W0 T0
    uSteps vSteps uEnds vEnds uWeights vWeights dBound).trans (gcd_minor_budget_at_cutoffs n hn T1 dBound)
  have longPower : (n : ℝ)^(7/8 : ℝ) ≤ (n : ℝ)^(127/128 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
  have Tpow : T^7 ≤ T^10 := pow_le_pow_right₀ T1 (by decide)
  have Lpow : logBudget n^5 ≤ logBudget n^14 := pow_le_pow_right₀ L1 (by decide)
  have scale : (finalScale n T)^2/(n : ℝ) =
      (n : ℝ)^(127/128 : ℝ)*T^10*logBudget n^14 := by
    unfold finalScale
    apply (div_eq_iff nr.ne').mpr
    have powEq : ((n : ℝ)^(255/256 : ℝ))^2 = (n : ℝ)^(127/128 : ℝ)*(n : ℝ) := by
      calc
        _ = (n : ℝ)^(255/128 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le]; norm_num
        _ = (n : ℝ)^(127/128 : ℝ)*(n : ℝ)^(1 : ℝ) := by rw [← Real.rpow_add nr]; norm_num
        _ = _ := by rw [Real.rpow_one]
    rw [mul_pow,mul_pow,powEq]
    ring
  unfold removedWaveFamily
  refine (norm_add_le _ _).trans ((add_le_add short gcd).trans ?_)
  rw [show 34084*(finalScale n T)^2/(n : ℝ) = 34084*((finalScale n T)^2/(n : ℝ)) by ring, scale]
  calc
    _ ≤ 1280*(n : ℝ)^(127/128 : ℝ)*T^10*logBudget n^14 +
        32804*(n : ℝ)^(127/128 : ℝ)*T^10*logBudget n^14 := by gcongr
    _ = _ := by ring

end

end B13NondividingResidueReductionProof

end

/- Residue bridge -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Scale
open scoped Classical

noncomputable section

def residueWindowPair (n u v l r p s : ℕ) : ℂ :=
  (pairResidueError n u v l r p s : ℂ) +
    ((pairVolume n u v l r p s : ℂ) - productStepWideIntegral n u v l r p s)

theorem deep_wave_pair_eq_residue_window {n u v l r p s : ℕ} (hu : 0 < u) (hv : 0 < v) :
    productStepDeepIntegral n u v l r p s = residueWindowPair n u v l r p s := by
  have eq := congrArg Complex.ofReal (progression_pair_count_eq_volume_add_error
    (n := n) (u := u) (v := v) (l := l) (r := r) (p := p) (s := s) hu hv)
  push_cast at eq
  rw [deep_wave_pair_eq_count_sub_wide, eq]
  unfold residueWindowPair
  abel

end

end B13NondividingResidueReductionProof

end

/- Open initial segment residue -/
section

namespace B13NondividingResidueReductionProof

open Finset Filter
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

private def prefixAgainstRight (n : ℕ) {ι : Type}
    (family : Finset (ℕ × ℕ) → Finset ι →
      ((ℕ × ℕ) → ℕ) → ((ℕ × ℕ) → ℕ) → ((ℕ × ℕ) → ℕ) →
      (ι → ℕ) → (ι → ℕ) → (ι → ℕ) → ((ℕ × ℕ) → ℂ) → (ι → ℂ) → ℂ)
    (items : Finset ι) (step lower upper : ι → ℕ) (weight : ι → ℂ) : ℂ :=
  family (bilateralLeftWaveItems n) items leftBilinearStep (fun _ => 0)
    (fun i => n/leftBilinearStep i) step lower upper (leftBilinearWeight n) weight

private def prefixCut (n : ℕ) : ℂ :=
  prefixAgainstRight n (cutWaveFamily n) (rightLowWaveItems n) rightLowWaveStep
    (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight +
  prefixAgainstRight n (cutWaveFamily n) (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun i => n/rightHighWaveStep i) (rightHighWaveWeight n)

private def prefixRemoved (n : ℕ) : ℂ :=
  prefixAgainstRight n (removedWaveFamily n) (rightLowWaveItems n) rightLowWaveStep
    (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight +
  prefixAgainstRight n (removedWaveFamily n) (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun i => n/rightHighWaveStep i) (rightHighWaveWeight n)

private theorem prefix_partition (n : ℕ) :
    bilateralOpenPrefixRemainder n = prefixCut n + prefixRemoved n := by
  have low := masked_wave_product_eq_cut n (bilateralLeftWaveItems n) (rightLowWaveItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) (leftBilinearWeight n) rightLowWaveWeight
    (fun _ h => (mem_Icc.mp (bilateral_left_step_range h)).1)
    (fun _ h => (mem_Icc.mp (bilateral_right_low_step_range h)).1)
  have high := masked_wave_product_eq_cut n (bilateralLeftWaveItems n) (rightHighWaveItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightHighWaveStep (rightHighWaveLower n) (fun i => n/rightHighWaveStep i)
    (leftBilinearWeight n) (rightHighWaveWeight n)
    (fun _ h => (mem_Icc.mp (bilateral_left_step_range h)).1)
    (fun _ h => (mem_Icc.mp (bilateral_right_high_step_range h)).1)
  refine (congrArg₂ (·+·) low high).trans ?_
  unfold prefixCut prefixRemoved prefixAgainstRight
  abel

private theorem norm_prefix_removed_le {n : ℕ} (hn : 2 ≤ n)
    (width : 4*cutoffH n*maximumStep n ≤ n)
    {T : ℝ} (T1 : 1 ≤ T) (dBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖prefixRemoved n‖ ≤ 68168*(finalScale n T)^2/(n : ℝ) := by
  have T0 := zero_le_one.trans T1
  have np : 0 < n := by omega
  have low := norm_removed_wave_family_le n hn width (bilateralLeftWaveItems n) (rightLowWaveItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) (leftBilinearWeight n) rightLowWaveWeight T1
    (fun _ h => bilateral_left_step_range h) (fun _ h => bilateral_right_low_step_range h)
    (fun _ _ => le_rfl) (fun _ _ => min_le_right _ _)
    (norm_bilateral_left_step_mass np T0 dBound) (norm_bilateral_right_low_step_mass T1 dBound) dBound
  have high := norm_removed_wave_family_le n hn width (bilateralLeftWaveItems n) (rightHighWaveItems n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightHighWaveStep (rightHighWaveLower n) (fun i => n/rightHighWaveStep i)
    (leftBilinearWeight n) (rightHighWaveWeight n) T1
    (fun _ h => bilateral_left_step_range h) (fun _ h => bilateral_right_high_step_range h)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (norm_bilateral_left_step_mass np T0 dBound) (norm_bilateral_right_high_step_mass T0 dBound) dBound
  unfold prefixRemoved prefixAgainstRight
  exact (norm_add_le _ _).trans ((add_le_add low high).trans_eq (by ring))

private theorem prefix_removed_saving : saving prefixRemoved := by
  intro e he
  let δ := min 1 (e/68168)
  have δp : 0 < δ := lt_min zero_lt_one (div_pos he (by norm_num))
  have δ1 : δ ≤ 1 := min_le_left _ _
  have δe : 68168*δ ≤ e := by
    have h : δ ≤ e/68168 := min_le_right _ _
    linarith only [h]
  have ev : ∀ᶠ n : ℕ in atTop, ‖prefixRemoved n‖ ≤ e*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, eventually_small_width,
      eventually_finalScale_le (C := 1) zero_le_one δp] with n hn width env
    obtain ⟨T,T1,dBound,bound⟩ := env
    have nr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have positive : 0 ≤ finalScale n T := by
      unfold finalScale
      exact mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans T1) _) (pow_nonneg
        (zero_le_one.trans (one_le_logBudget n)) _)) (Real.rpow_nonneg nr.le _)
    have first : finalScale n T ≤ δ*(n : ℝ) := by simpa only [one_mul] using bound
    have second : finalScale n T ≤ (n : ℝ) := first.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right δ1 nr.le)
    refine (norm_prefix_removed_le hn width T1 dBound).trans ?_
    rw [pow_two]
    calc
      _ ≤ 68168*((δ*(n : ℝ))*(n : ℝ))/(n : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul first second positive (mul_nonneg δp.le nr.le)) (by norm_num)) nr.le
      _ = (68168*δ)*(n : ℝ) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right δe nr.le
  obtain ⟨N, h⟩ := eventually_atTop.mp ev
  exact ⟨N, fun n hn _ => h n hn⟩

private def prefixResidueFamily (n : ℕ) {ι : Type} (I : Finset ι)
    (v l r : ι → ℕ) (w : ι → ℂ) : ℂ :=
  ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ I,
    if maximumStep n^2 < leftBilinearStep i*v j ∧ (leftBilinearStep i).gcd (v j) ≤ maximumStep n then
      leftBilinearWeight n i * w j * residueWindowPair n (leftBilinearStep i) (v j)
        0 (n/leftBilinearStep i) (l j) (r j)
    else 0

def bilateralOpenPrefixResidueRemainder (n : ℕ) : ℂ :=
  prefixResidueFamily n (rightLowWaveItems n) rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight +
  prefixResidueFamily n (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun i => n/rightHighWaveStep i) (rightHighWaveWeight n)

private theorem prefix_cut_eq_residue (n : ℕ) : prefixCut n = bilateralOpenPrefixResidueRemainder n := by
  have each {ι : Type} (I : Finset ι) (v l r : ι → ℕ) (w : ι → ℂ) (steps : ∀ j ∈ I, 0 < v j) :
      prefixAgainstRight n (cutWaveFamily n) I v l r w = prefixResidueFamily n I v l r w := by
    unfold prefixAgainstRight cutWaveFamily prefixResidueFamily
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    rw [deep_wave_pair_eq_residue_window (mem_Icc.mp (bilateral_left_step_range hi)).1 (steps j hj)]
  exact congrArg₂ (·+·)
    (each _ rightLowWaveStep _ (rightLowWaveUpper n) _ (fun _ h => (mem_Icc.mp (bilateral_right_low_step_range h)).1))
    (each _ rightHighWaveStep (rightHighWaveLower n) _ _ (fun _ h => (mem_Icc.mp (bilateral_right_high_step_range h)).1))

theorem frozen_iff_open_prefix_residue : frozenGoal ↔ saving bilateralOpenPrefixResidueRemainder := by
  rw [frozen_iff_open_prefix]
  have eq (n : ℕ) : bilateralOpenPrefixRemainder n =
      bilateralOpenPrefixResidueRemainder n + prefixRemoved n := by rw [prefix_partition, prefix_cut_eq_residue]
  constructor <;> intro initial e he <;>
    obtain ⟨N, h⟩ := initial (e/2) (by positivity) <;>
    obtain ⟨M, hs⟩ := prefix_removed_saving (e/2) (by positivity) <;>
    refine ⟨max N M, fun n hn even => ?_⟩
  · have diff : bilateralOpenPrefixResidueRemainder n = bilateralOpenPrefixRemainder n - prefixRemoved n := by
      rw [eq]
      abel
    rw [diff]
    refine (norm_sub_le _ _).trans ?_
    linarith only [h n (by omega) even, hs n (by omega) even]
  · rw [eq]
    refine (norm_add_le _ _).trans ?_
    linarith only [h n (by omega) even, hs n (by omega) even]

end

end B13NondividingResidueReductionProof

end

/- Initial segment dividing cofactors -/
section

namespace B13NondividingResidueReductionProof

open Finset Filter Topology MeasureTheory
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

private def prefixLeft (n : ℕ) : ℝ → ℂ :=
  waveFamilyPolynomial (bilateralLeftWaveItems n) leftBilinearStep (fun _ => 0)
    (fun i => n/leftBilinearStep i) (leftBilinearWeight n)

private def prefixRight (n : ℕ) (I : Finset RightLowWaveIndex) : ℝ → ℂ :=
  waveFamilyPolynomial I rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight

private def dividingCofactors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun b => cutoffU n < b

private def hasCofactor (n b : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter fun i => i.1 = b

private def lowNondividingItems (n : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter fun i => ¬i.1 ∣ n

private def dividingCofactorContribution (n : ℕ) : ℂ :=
  ∑ b ∈ dividingCofactors n, maskedWaveProduct n (prefixLeft n) (prefixRight n (hasCofactor n b))

private theorem mask_sum_right (n : ℕ) {ι : Type*} (S : Finset ι)
    {f : ℝ → ℂ} (fc : Continuous f) (g : ι → ℝ → ℂ) (gc : ∀ i, Continuous (g i)) :
    maskedWaveProduct n f (fun t => ∑ i ∈ S, g i t) = ∑ i ∈ S, maskedWaveProduct n f (g i) := by
  induction S using Finset.induction with
  | empty => simp [maskedWaveProduct]
  | insert i S hn ih =>
    simp only [sum_insert hn]
    rw [masked_wave_product_add_right n fc (gc i) (continuous_finsetSum _ fun j _ => gc j), ih]

private theorem prefix_right_partition {n : ℕ} (hn : 0 < n) (t : ℝ) :
    prefixRight n (rightLowWaveItems n) t =
      prefixRight n (lowNondividingItems n) t + ∑ b ∈ dividingCofactors n, prefixRight n (hasCofactor n b) t := by
  let I := rightLowWaveItems n
  let D := I.filter fun i => i.1 ∣ n
  let term (i : RightLowWaveIndex) :=
    rightLowWaveWeight i * DyadicMixedB4Geometric.wave (rightLowWaveStep i) 0 (rightLowWaveUpper n i) t
  have first : ∑ i ∈ I, term i = (∑ i ∈ lowNondividingItems n, term i) + ∑ i ∈ D, term i := by
    have eq := sum_filter_add_sum_filter_not I (fun i => i.1 ∣ n) term
    exact eq.symm.trans (add_comm _ _)
  have image : ∀ i ∈ D, i.1 ∈ dividingCofactors n := by
    intro i hi
    obtain ⟨item, div⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨div,hn.ne'⟩, (mem_Ioc.mp (mem_sigma.mp item).1).1⟩
  have each (b : ℕ) (hb : b ∈ dividingCofactors n) : D.filter (fun i => i.1 = b) = hasCofactor n b := by
    ext i
    simp only [D,I,hasCofactor, mem_filter]
    exact ⟨fun h => ⟨h.1.1,h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ Nat.dvd_of_mem_divisors (mem_filter.mp hb).1⟩,h.2⟩⟩
  change (∑ i ∈ I, term i) = (∑ i ∈ lowNondividingItems n, term i) +
    ∑ b ∈ dividingCofactors n, ∑ i ∈ hasCofactor n b, term i
  rw [first]
  congr 1
  rw [← sum_fiberwise_of_maps_to image term]
  exact sum_congr rfl fun b hb => by rw [each b hb]

private theorem norm_dividing_cofactor_contribution {n : ℕ} (hn : 0 < n) {T : ℝ} (T1 : 1 ≤ T)
    (dBound : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖dividingCofactorContribution n‖ ≤ (n : ℝ)^(31/32 : ℝ)*T^9*logBudget n^2 := by
  let W := T^3 * logBudget n
  let C := (W*T)^2
  let P := (n : ℝ)^(31/32 : ℝ)
  let c := (n : ℝ)^(-(1/32) : ℝ)
  have nr : (0 : ℝ) < n := by exact_mod_cast hn
  have T0 := zero_le_one.trans T1
  have W0 : 0 ≤ W := mul_nonneg (pow_nonneg T0 _) (zero_le_one.trans (one_le_logBudget n))
  have cp : 0 < c := Real.rpow_pos_of_pos nr _
  have lMass : (∫ t in (0 : ℝ)..1, ‖prefixLeft n t‖^2) ≤ (n : ℝ)*C :=
    wave_family_energy_le _ _ _ _ _ W0 T0 (fun _ h => bilateral_left_step_range h)
      (fun _ _ => le_rfl) (norm_bilateral_left_step_mass hn T0 dBound) dBound
  have each (b : ℕ) (hb : b ∈ dividingCofactors n) :
      ‖maskedWaveProduct n (prefixLeft n) (prefixRight n (hasCofactor n b))‖ ≤ P*C := by
    let I := hasCofactor n b
    have bp : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_mem_divisors (mem_filter.mp hb).1
    have realBelow : (n : ℝ)^(1/16 : ℝ) ≤ (b : ℝ) :=
      (Nat.floor_lt (by positivity : 0 ≤ (n : ℝ)^(1/16 : ℝ))).mp (mem_filter.mp hb).2 |>.le
    have every (i : RightLowWaveIndex) (hi : i ∈ I) : b ∣ rightLowWaveStep i := by
      change b ∣ i.2*i.1
      rw [(mem_filter.mp hi).2]
      exact dvd_mul_left _ _
    have filterEq : I.filter (fun i => b ∣ rightLowWaveStep i) = I := filter_eq_self.mpr every
    have eq : prefixRight n I =
        divisibleStepPolynomial b I rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight := by
      unfold prefixRight waveFamilyPolynomial divisibleStepPolynomial
      rw [filterEq]
    have wBound (u : ℕ) (hu : u ∈ Icc 1 n) :
        (∑ i ∈ I.filter (fun i => rightLowWaveStep i = u), ‖rightLowWaveWeight i‖) ≤ W :=
      (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
        (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_right_low_step_mass T1 dBound u hu)
    have rMass : (∫ t in (0 : ℝ)..1, ‖prefixRight n I t‖^2) ≤ (n : ℝ)^(15/16 : ℝ)*C := by
      rw [eq]
      refine (divisible_step_energy_le n b I _ _ _ _ W0 T0
        (fun _ h => bilateral_right_low_step_range (mem_filter.mp h).1) (fun _ _ => min_le_right _ _)
        wBound dBound).trans ?_
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply (div_le_iff₀ bp).mpr
      calc
        (n : ℝ) = (n : ℝ)^(15/16 : ℝ)*(n : ℝ)^(1/16 : ℝ) := by rw [← Real.rpow_add nr]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left realBelow (by positivity)
    have lh : c * (n : ℝ) = P := by
      unfold c P
      calc
        _ = (n : ℝ)^(-(1/32) : ℝ)*(n : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add nr]; norm_num
    have rh : c⁻¹ * (n : ℝ)^(15/16 : ℝ) = P := by
      unfold c P
      rw [Real.rpow_neg nr.le, inv_inv, ← Real.rpow_add nr]
      norm_num
    refine (norm_masked_wave_product_le (wave_family_continuous ..) (wave_family_continuous ..) cp).trans ?_
    refine (div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left lMass cp.le)
      (mul_le_mul_of_nonneg_left rMass (inv_nonneg.mpr cp.le))) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq ?_
    rw [← mul_assoc, ← mul_assoc, lh, rh]
    ring
  unfold dividingCofactorContribution
  refine (norm_sum_le _ _).trans ((sum_le_sum each).trans ?_)
  rw [sum_const,nsmul_eq_mul]
  have cards : ((dividingCofactors n).card : ℝ) ≤ T :=
    (show ((dividingCofactors n).card : ℝ) ≤ n.divisors.card by exact_mod_cast
      (card_le_card (filter_subset (fun b => cutoffU n < b) n.divisors))).trans (dBound n le_rfl)
  exact (mul_le_mul_of_nonneg_right cards (by unfold P C; positivity)).trans_eq (by unfold P C W; ring)

private theorem dividing_cofactor_contribution_saving : saving dividingCofactorContribution := by
  intro e he
  obtain ⟨D,D1,dBound⟩ := divisor_envelope
  let C := D^9
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-(21/1024) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 21/1024)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(21/1024) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have estimates : ∀ᶠ n : ℕ in atTop, ‖dividingCofactorContribution n‖ ≤ e*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, eventually_log_budget_le, scaled.eventually_lt_const he]
      with n hn logBound small
    have nPos : 0 < n := hn
    have nr : (0 : ℝ) < n := by exact_mod_cast nPos
    let X := (n : ℝ)^(1/1024 : ℝ)
    let T := D*X
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1
      (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))
    have exp : (n : ℝ)^(31/32 : ℝ)*X^11 = (n : ℝ)^(-(21/1024) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le, ← Real.rpow_add nr]
      calc
        _ = (n : ℝ)^(-(21/1024)+1 : ℝ) := by congr 1; norm_num
        _ = (n : ℝ)^(-(21/1024) : ℝ)*(n : ℝ)^(1 : ℝ) := Real.rpow_add nr _ _
        _ = _ := by rw [Real.rpow_one]
    refine (norm_dividing_cofactor_contribution nPos T1 (dBound n)).trans ?_
    calc
      _ ≤ (n : ℝ)^(31/32 : ℝ)*T^9*X^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (one_le_logBudget n)) logBound 2)
          (mul_nonneg (Real.rpow_nonneg nr.le _) (pow_nonneg (zero_le_one.trans T1) _))
      _ = C*((n : ℝ)^(31/32 : ℝ)*X^11) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(21/1024) : ℝ))*(n : ℝ) := by rw [exp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
  obtain ⟨N,h⟩ := eventually_atTop.mp estimates
  exact ⟨N, fun n hn _ => h n hn⟩

private def dividingSlice (n : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter fun i => i.1 ∣ n

private def dividingSliceCut (n : ℕ) : ℂ :=
  cutWaveFamily n (bilateralLeftWaveItems n) (dividingSlice n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) (leftBilinearWeight n) rightLowWaveWeight

private def dividingSliceRemoved (n : ℕ) : ℂ :=
  removedWaveFamily n (bilateralLeftWaveItems n) (dividingSlice n)
    leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) (leftBilinearWeight n) rightLowWaveWeight

private theorem dividing_slice_eq {n : ℕ} (hn : 0 < n) :
    dividingCofactorContribution n = dividingSliceCut n + dividingSliceRemoved n := by
  have fullC : Continuous (prefixLeft n) := wave_family_continuous ..
  have rightC (I : Finset RightLowWaveIndex) : Continuous (prefixRight n I) := wave_family_continuous ..
  have pol : prefixRight n (dividingSlice n) =
      fun t => ∑ b ∈ dividingCofactors n, prefixRight n (hasCofactor n b) t := by
    funext t
    have eq := prefix_right_partition hn t
    have words : prefixRight n (rightLowWaveItems n) t =
        prefixRight n (lowNondividingItems n) t + prefixRight n (dividingSlice n) t := by
      unfold prefixRight waveFamilyPolynomial dividingSlice lowNondividingItems
      exact (sum_filter_add_sum_filter_not _ (fun i : RightLowWaveIndex => i.1 ∣ n) _).symm.trans (add_comm _ _)
    rw [words] at eq
    exact add_left_cancel eq
  have same : maskedWaveProduct n (prefixLeft n) (prefixRight n (dividingSlice n)) =
      dividingCofactorContribution n := by
    rw [pol, mask_sum_right n _ fullC _ (fun b => rightC _)]
    rfl
  rw [← same]
  exact masked_wave_product_eq_cut n _ _ _ _ _ _ _ _ _ _
    (fun _ h => (mem_Icc.mp (bilateral_left_step_range h)).1)
    (fun _ h => (mem_Icc.mp (bilateral_right_low_step_range (mem_filter.mp h).1)).1)

private theorem dividing_slice_removed_saving : saving dividingSliceRemoved := by
  intro e he
  let δ := min 1 (e/34084)
  have δp : 0 < δ := lt_min zero_lt_one (div_pos he (by norm_num))
  have δe : 34084*δ ≤ e := by
    have h : δ ≤ e/34084 := min_le_right _ _
    linarith only [h]
  have estimates : ∀ᶠ n : ℕ in atTop, ‖dividingSliceRemoved n‖ ≤ e*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, eventually_small_width,
      eventually_finalScale_le (C := 1) zero_le_one δp] with n hn width env
    obtain ⟨T,T1,dBound,bound⟩ := env
    have np : 0 < n := by omega
    have nr : (0 : ℝ) < n := by exact_mod_cast np
    have T0 := zero_le_one.trans T1
    have pos : 0 ≤ finalScale n T := by
      unfold finalScale
      exact mul_nonneg (mul_nonneg (pow_nonneg T0 _) (pow_nonneg (zero_le_one.trans (one_le_logBudget n)) _))
        (Real.rpow_nonneg nr.le _)
    have first : finalScale n T ≤ δ*(n : ℝ) := by simpa only [one_mul] using bound
    have second : finalScale n T ≤ (n : ℝ) := first.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left 1 (e/34084)) nr.le)
    have weight (u : ℕ) (hu : u ∈ Icc 1 n) :
        (∑ i ∈ (dividingSlice n).filter (fun i => rightLowWaveStep i = u), ‖rightLowWaveWeight i‖) ≤
          T^3*logBudget n :=
      (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _)) (fun _ _ _ => norm_nonneg _)).trans
        (norm_bilateral_right_low_step_mass T1 dBound u hu)
    refine (norm_removed_wave_family_le n hn width (bilateralLeftWaveItems n) (dividingSlice n)
      leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i) rightLowWaveStep (fun _ => 0)
      (rightLowWaveUpper n) (leftBilinearWeight n) rightLowWaveWeight T1
      (fun _ h => bilateral_left_step_range h) (fun _ h => bilateral_right_low_step_range (mem_filter.mp h).1)
      (fun _ _ => le_rfl) (fun _ _ => min_le_right _ _)
      (norm_bilateral_left_step_mass np T0 dBound) weight dBound).trans ?_
    rw [pow_two]
    calc
      _ ≤ 34084*((δ*(n : ℝ))*(n : ℝ))/(n : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul first second pos (mul_nonneg δp.le nr.le)) (by norm_num)) nr.le
      _ = (34084*δ)*(n : ℝ) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right δe nr.le
  obtain ⟨N,h⟩ := eventually_atTop.mp estimates
  exact ⟨N, fun n hn _ => h n hn⟩

private theorem dividing_slice_cut_saving : saving dividingSliceCut := by
  intro e he
  obtain ⟨N,h⟩ := dividing_cofactor_contribution_saving (e/2) (by positivity)
  obtain ⟨M,hs⟩ := dividing_slice_removed_saving (e/2) (by positivity)
  refine ⟨max 1 (max N M), fun n hn even => ?_⟩
  have eq : dividingSliceCut n = dividingCofactorContribution n - dividingSliceRemoved n := by
    rw [dividing_slice_eq (by omega : 0 < n)]
    abel
  rw [eq]
  refine (norm_sub_le _ _).trans ?_
  linarith only [h n (by omega) even, hs n (by omega) even]

def bilateralNondividingResidueRemainder (n : ℕ) : ℂ :=
  bilateralOpenPrefixResidueRemainder n - dividingSliceCut n

theorem frozen_iff_nondividing_residue : frozenGoal ↔ saving bilateralNondividingResidueRemainder := by
  rw [frozen_iff_open_prefix_residue]
  constructor <;> intro initial e he <;>
    obtain ⟨N,h⟩ := initial (e/2) (by positivity) <;>
    obtain ⟨M,hs⟩ := dividing_slice_cut_saving (e/2) (by positivity) <;>
    refine ⟨max N M, fun n hn even => ?_⟩
  · unfold bilateralNondividingResidueRemainder
    refine (norm_sub_le _ _).trans ?_
    linarith only [h n (by omega) even, hs n (by omega) even]
  · have eq : bilateralOpenPrefixResidueRemainder n =
        bilateralNondividingResidueRemainder n + dividingSliceCut n := by
      unfold bilateralNondividingResidueRemainder
      abel
    rw [eq]
    refine (norm_add_le _ _).trans ?_
    linarith only [h n (by omega) even, hs n (by omega) even]

end

end B13NondividingResidueReductionProof

end

/- Wide family partition -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open DyadicMixedB4ArcDecomposition DyadicMixedB4OffWaveMoment
open scoped Classical

noncomputable section

def gatedWaveProduct (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ)
    (gate : α → β → Prop) (t : ℝ) : ℂ :=
  phase (((-(n : ℤ)) : ℝ)*t) * ∑ i ∈ I, ∑ j ∈ J, if gate i j then
    (a i * wave (u i) (l i) (r i) t) * (b j * wave (v j) (p j) (s j) t) else 0

private theorem gated_wave_summand_continuous {α β : Type*} (u l r : α → ℕ) (v p s : β → ℕ)
    (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) (i : α) (j : β) :
    Continuous (fun t => if gate i j then
      (a i * wave (u i) (l i) (r i) t) * (b j * wave (v j) (p j) (s j) t) else 0) := by
  by_cases h : gate i j
  · simp only [ite_eq_left h]
    change Continuous (((fun _ : ℝ => a i) * wave (u i) (l i) (r i)) *
      ((fun _ : ℝ => b j) * wave (v j) (p j) (s j)))
    exact (continuous_const.mul (wave_continuous ..)).mul (continuous_const.mul (wave_continuous ..))
  · simp only [ite_eq_right h]
    exact continuous_const

theorem gated_wave_product_continuous (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) :
    Continuous (gatedWaveProduct n I J u l r v p s a b gate) := by
  have pc : Continuous (fun t : ℝ => phase (((-(n : ℤ)) : ℝ)*t)) := by unfold phase; fun_prop
  apply pc.mul
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    gated_wave_summand_continuous u l r v p s a b gate i j

def commonWideFamily (n B H : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) : ℂ :=
  ∑ q ∈ Icc 1 B, ∑ z ∈ numSet q,
    ∫ t in (0 : ℝ)..1, (wideArc n H q z).indicator
      (gatedWaveProduct n I J u l r v p s a b (fun i j => gate i j ∧ q∣u i ∧ q∣v j)) t

def wideWaveFamily (n B H : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) : ℂ :=
  ∫ t in (0 : ℝ)..1,(wide n B H).indicator (gatedWaveProduct n I J u l r v p s a b gate) t

theorem wide_wave_family_eq_partition {n B H : ℕ} (hn : 0 < n) (thin : 4*H*B ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) :
    wideWaveFamily n B H I J u l r v p s a b gate =
      commonWideFamily n B H I J u l r v p s a b gate +
      noncommonWideFamily n B H I J u l r v p s a b gate := by
  unfold wideWaveFamily commonWideFamily noncommonWideFamily
  rw [wide_integral_eq_arcs hn thin (gated_wave_product_continuous ..), ← sum_add_distrib]
  refine sum_congr rfl fun q _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun z _ => ?_
  let G := gatedWaveProduct n I J u l r v p s a b (fun i j => gate i j ∧ q∣u i ∧ q∣v j)
  let F := noncommonWaveProduct n q I J u l r v p s a b gate
  have eq (t : ℝ) : gatedWaveProduct n I J u l r v p s a b gate t = G t + F t := by
    unfold G F gatedWaveProduct noncommonWaveProduct
    rw [← mul_add, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases good : gate i j <;> by_cases d : q∣u i ∧ q∣v j <;> simp [good,d]
  have gC : Continuous G := gated_wave_product_continuous ..
  have fC : Continuous F := noncommon_wave_product_continuous ..
  have meas := wide_arc_measurable n H q z
  have join : (∫ t in (0 : ℝ)..1,(wideArc n H q z).indicator G t) +
      (∫ t in (0 : ℝ)..1,(wideArc n H q z).indicator F t) =
      ∫ t in (0 : ℝ)..1,((wideArc n H q z).indicator G t + (wideArc n H q z).indicator F t) :=
    (intervalIntegral.integral_add (indicator_intervalIntegrable gC meas) (indicator_intervalIntegrable fC meas)).symm
  refine Eq.trans ?_ join.symm
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases h : t ∈ wideArc n H q z <;> simp [h,eq]

theorem wide_wave_family_eq_pair_sum (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) :
    wideWaveFamily n (DyadicMixedB4Scale.cutoffB n) (DyadicMixedB4Scale.cutoffH n) I J u l r v p s a b gate =
      ∑ i ∈ I, ∑ j ∈ J, if gate i j then a i*b j*
        productStepWideIntegral n (u i) (v j) (l i) (r i) (p j) (s j) else 0 := by
  let D := wide n (DyadicMixedB4Scale.cutoffB n) (DyadicMixedB4Scale.cutoffH n)
  let phaseAt (t : ℝ) := phase (((-(n : ℤ)) : ℝ)*t)
  let f (i : α) (j : β) (t : ℝ) :=
    if gate i j then a i*b j* D.indicator
      (fun x => phaseAt x * (wave (u i) (l i) (r i) x * wave (v j) (p j) (s j) x)) t else 0
  have pc : Continuous phaseAt := by unfold phaseAt phase; fun_prop
  have fInt (i : α) (j : β) : IntervalIntegrable (f i j) volume 0 1 := by
    by_cases cond : gate i j
    · simp only [f,ite_eq_left cond]
      exact (indicator_intervalIntegrable (pc.mul ((wave_continuous ..).mul (wave_continuous ..)))
        (wide_measurable ..)).const_mul _
    · simp only [f,ite_eq_right cond]
      exact intervalIntegrable_const
  have row (i : α) : IntervalIntegrable (fun t => ∑ j ∈ J,f i j t) volume 0 1 := by
    have eq : (∑ j ∈ J,f i j) = fun t => ∑ j ∈ J,f i j t := by
      funext t
      let evaluation : (ℝ → ℂ) →+ ℂ := ⟨⟨fun g => g t, rfl⟩, fun _ _ => rfl⟩
      exact map_sum evaluation (f i) J
    rw [← eq]
    exact IntervalIntegrable.sum _ fun j _ => fInt i j
  calc
    _ = ∫ t in (0 : ℝ)..1, ∑ i ∈ I, ∑ j ∈ J, f i j t := by
      unfold wideWaveFamily
      refine intervalIntegral.integral_congr fun t _ => ?_
      change D.indicator (gatedWaveProduct n I J u l r v p s a b gate) t = _
      by_cases inside : t ∈ D
      · simp only [Set.indicator_of_mem inside, gatedWaveProduct, Finset.mul_sum]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        by_cases cond : gate i j
        · simp [cond, f, inside, phaseAt]
          ring
        · simp [cond, f]
      · simp [inside, f]
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun i _ => row i)]
      refine sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finsetSum (fun j _ => fInt i j)]
      refine sum_congr rfl fun j _ => ?_
      by_cases cond : gate i j <;> simp [cond, f, phaseAt, D, productStepWideIntegral, intervalIntegral.integral_const_mul]

end

end B13NondividingResidueReductionProof

end

/- Common wide smoothing -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcCenters DyadicMixedB4ProgressionApprox
open DyadicMixedB4WindowKernel DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def commonAverageWaveProduct (n q z : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ)
    (gate : α → β → Prop) (t : ℝ) : ℂ :=
  phase (((-(n : ℤ)) : ℝ)*t) * ∑ i ∈ I, ∑ j ∈ J, if gate i j ∧ q∣u i ∧ q∣v j then
    (a i * progressionAverage (u i) (l i) (r i) (t-(z : ℝ)/q)) *
    (b j * progressionAverage (v j) (p j) (s j) (t-(z : ℝ)/q)) else 0

theorem common_average_wave_product_continuous (n q z : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) :
    Continuous (commonAverageWaveProduct n q z I J u l r v p s a b gate) := by
  have phaseC : Continuous (fun t : ℝ => phase (((-(n : ℤ)) : ℝ)*t)) := by unfold phase; fun_prop
  apply phaseC.mul
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  by_cases h : gate i j ∧ q∣u i ∧ q∣v j
  · simp only [ite_eq_left h]
    have cu := (progressionAverage_continuous (u i) (l i) (r i)).comp
      (continuous_id.sub (continuous_const (y := (z : ℝ)/q)))
    have cv := (progressionAverage_continuous (v j) (p j) (s j)).comp
      (continuous_id.sub (continuous_const (y := (z : ℝ)/q)))
    exact (continuous_const.mul cu).mul (continuous_const.mul cv)
  · simp only [ite_eq_right h]
    exact continuous_const

theorem norm_common_wave_product_sub_average_le (n A H q z : ℕ) (hn : 0 < n)
    (hq : 0 < q) (Apos : 0 < A) (small : 2*H*A ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    {W : ℝ} (W0 : 0 ≤ W)
    (uSteps : ∀ i ∈ I, u i ∈ Icc 1 A) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 A)
    (uEnds : ∀ i ∈ I, r i ≤ n/u i) (vEnds : ∀ j ∈ J, s j ≤ n/v j)
    (uWeights : ∀ x ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i=x), ‖a i‖) ≤ W)
    (vWeights : ∀ x ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j=x), ‖b j‖) ≤ W)
    {t : ℝ} (ht : t ∈ wideArc n H q z) :
    ‖gatedWaveProduct n I J u l r v p s a b (fun i j => gate i j ∧ q∣u i ∧ q∣v j) t -
      commonAverageWaveProduct n q z I J u l r v p s a b gate t‖ ≤
    16*W^2*(n : ℝ)*A*(1+Real.log (A : ℝ))/(q : ℝ)^2 := by
  let I' := I.filter (fun i => q∣u i)
  let J' := J.filter (fun j => q∣v j)
  let fu (i : α) := (n : ℝ)/(u i : ℝ)
  let fv (j : β) := (n : ℝ)/(v j : ℝ)
  let A1 := ∑ i ∈ I',‖a i‖
  let B1 := ∑ j ∈ J',‖b j‖
  let AU := ∑ i ∈ I',‖a i‖*fu i
  let BV := ∑ j ∈ J',‖b j‖*fv j
  let wt (i : α) (j : β) := ‖a i‖*‖b j‖*(2*Real.pi*(fu i+fv j))
  let β0 := t-(z : ℝ)/q
  unfold gatedWaveProduct commonAverageWaveProduct
  rw [← mul_sub,norm_mul,norm_phase',one_mul,← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, if q∣u i ∧ q∣v j then wt i j else 0 := by
      refine sum_le_sum fun i hi => ?_
      rw [← sum_sub_distrib]
      refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
      by_cases d : q∣u i ∧ q∣v j
      · rw [ite_eq_left d]
        by_cases g : gate i j
        · have active : gate i j ∧ q∣u i ∧ q∣v j := ⟨g,d⟩
          simp only [ite_eq_left active]
          have eq :
            (a i * wave (u i) (l i) (r i) t) * (b j * wave (v j) (p j) (s j) t) -
                (a i * progressionAverage (u i) (l i) (r i) β0) *
                  (b j * progressionAverage (v j) (p j) (s j) β0) =
              (a i*b j)*(wave (u i) (l i) (r i) t * wave (v j) (p j) (s j) t -
                progressionAverage (u i) (l i) (r i) β0 * progressionAverage (v j) (p j) (s j) β0) := by ring
          change ‖_ - (a i * progressionAverage (u i) (l i) (r i) β0) *
                  (b j * progressionAverage (v j) (p j) (s j) β0)‖ ≤ _
          rw [eq,norm_mul,norm_mul]
          exact mul_le_mul_of_nonneg_left
            (norm_shifted_waves_sub_average_le n H q z (u i) (v j) (l i) (r i) (p j) (s j) hn hq
              (mem_Icc.mp (uSteps i hi)).1 (mem_Icc.mp (vSteps j hj)).1 d.1 d.2 (uEnds i hi) (vEnds j hj)
              ((Nat.mul_le_mul_left _ (mem_Icc.mp (uSteps i hi)).2).trans small)
              ((Nat.mul_le_mul_left _ (mem_Icc.mp (vSteps j hj)).2).trans small) ht)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        · have no : ¬(gate i j ∧ q∣u i ∧ q∣v j) := fun active => g active.1
          simp only [ite_eq_right no,sub_self,norm_zero]
          unfold wt fu fv
          positivity
      · have no : ¬(gate i j ∧ q∣u i ∧ q∣v j) := fun active => d active.2
        simp only [ite_eq_right no,ite_eq_right d,sub_self,norm_zero,le_rfl]
    _ = ∑ i ∈ I', ∑ j ∈ J',wt i j := by
      unfold I' J'
      simp only [sum_filter]
      refine sum_congr rfl fun i _ => ?_
      by_cases h : q∣u i <;> simp [h]
    _ = 2*Real.pi*(AU*B1+A1*BV) := by
      unfold AU B1 A1 BV
      rw [sum_mul_sum,sum_mul_sum,← sum_add_distrib,mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib,mul_sum]
      exact sum_congr rfl fun j _ => by unfold wt; ring
    _ ≤ _ := by
      have a1 : A1 ≤ W*((A : ℝ)/q) := by
        have h := divisible_constant_step_mass_le A q I u a W0 uSteps uWeights
        simpa only [divisibleStepMass,mul_one] using h
      have b1 : B1 ≤ W*((A : ℝ)/q) := by
        have h := divisible_constant_step_mass_le A q J v b W0 vSteps vWeights
        simpa only [divisibleStepMass,mul_one] using h
      have aU : AU ≤ W*((n : ℝ)/q*(1+Real.log (A : ℝ))) :=
        divisible_inverse_step_mass_le n A q hq I u a W0 uSteps uWeights
      have bV : BV ≤ W*((n : ℝ)/q*(1+Real.log (A : ℝ))) :=
        divisible_inverse_step_mass_le n A q hq J v b W0 vSteps vWeights
      have x0 : 0 ≤ (1+Real.log (A : ℝ)) :=
        (add_nonneg) zero_le_one (Real.log_nonneg (by exact_mod_cast Apos))
      have fst : AU*B1 ≤ (W*((n : ℝ)/q*(1+Real.log (A : ℝ))))*(W*((A : ℝ)/q)) := by
        exact mul_le_mul aU b1 (by unfold B1; positivity) (by positivity)
      have snd : A1*BV ≤ (W*((A : ℝ)/q))*(W*((n : ℝ)/q*(1+Real.log (A : ℝ)))) := by
        exact mul_le_mul a1 bV (by unfold BV fv; positivity) (by positivity)
      calc
        _ ≤ 8*((W*((n : ℝ)/q*(1+Real.log (A : ℝ))))*(W*((A : ℝ)/q)) +
               (W*((A : ℝ)/q))*(W*((n : ℝ)/q*(1+Real.log (A : ℝ))))) := by
          have pi : 2*Real.pi ≤ 8 := by linarith only [Real.pi_lt_four]
          exact mul_le_mul pi (add_le_add fst snd) (by unfold AU A1 BV B1 fu fv; positivity) (by norm_num)
        _ = _ := by ring

end

end B13NondividingResidueReductionProof

end

/- Common wide average -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters DyadicMixedB4ArcDecomposition DyadicMixedB4ModulusTail
open scoped Classical

noncomputable section

def commonAverageWideFamily (n B H : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) : ℂ :=
  ∑ q ∈ Icc 1 B, ∑ z ∈ numSet q,
    ∫ t in (0 : ℝ)..1, (wideArc n H q z).indicator
      (commonAverageWaveProduct n q z I J u l r v p s a b gate) t

theorem norm_common_wide_family_sub_average_le (n A B H : ℕ) (hn : 0 < n)
    (Apos : 0 < A) (small : 2*H*A ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    {W : ℝ} (W0 : 0 ≤ W) (uSteps : ∀ i ∈ I, u i ∈ Icc 1 A) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 A)
    (uEnds : ∀ i ∈ I, r i ≤ n/u i) (vEnds : ∀ j ∈ J, s j ≤ n/v j)
    (uWeights : ∀ x ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i=x), ‖a i‖) ≤ W)
    (vWeights : ∀ x ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j=x), ‖b j‖) ≤ W) :
    ‖commonWideFamily n B H I J u l r v p s a b gate -
        commonAverageWideFamily n B H I J u l r v p s a b gate‖ ≤
      128*W^2*(H : ℝ)*A*(1+Real.log (A : ℝ)) := by
  let L := 1+Real.log (A : ℝ)
  let C := 64*W^2*(H : ℝ)*A*L
  let G (q : ℕ) := gatedWaveProduct n I J u l r v p s a b (fun i j => gate i j ∧ q∣u i ∧ q∣v j)
  let F (q z : ℕ) := commonAverageWaveProduct n q z I J u l r v p s a b gate
  let diff (q z : ℕ) := (∫ t in (0 : ℝ)..1,(wideArc n H q z).indicator (G q) t) -
    (∫ t in (0 : ℝ)..1,(wideArc n H q z).indicator (F q z) t)
  have nonnegative : 0 ≤ L := add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast Apos))
  have C0 : 0 ≤ C := by unfold C; positivity
  have each (q z : ℕ) (qMem : q ∈ Icc 1 B) :
      ‖diff q z‖ ≤ 2*((H : ℝ)/((q : ℝ)*n))*(16*W^2*(n : ℝ)*A*L/(q : ℝ)^2) := by
    have gc : Continuous (G q) := gated_wave_product_continuous ..
    have fc : Continuous (F q z) := common_average_wave_product_continuous ..
    have measurable := wide_arc_measurable n H q z
    have equality : diff q z =
        ∫ t in (0 : ℝ)..1,(wideArc n H q z).indicator (fun x => G q x - F q z x) t := by
      unfold diff
      rw [← intervalIntegral.integral_sub (indicator_intervalIntegrable gc measurable)
        (indicator_intervalIntegrable fc measurable)]
      refine intervalIntegral.integral_congr fun t _ => ?_
      by_cases hit : t ∈ wideArc n H q z <;> simp [hit]
    rw [equality]
    exact norm_arc_integral_le (gc.sub fc) (by positivity) fun t ht =>
      norm_common_wave_product_sub_average_le n A H q z hn (mem_Icc.mp qMem).1 Apos small
        I J u l r v p s a b gate W0 uSteps vSteps uEnds vEnds uWeights vWeights ht
  have row (q : ℕ) (qMem : q ∈ Icc 1 B) : (∑ z ∈ numSet q, ‖diff q z‖) ≤ C*(1/(q : ℝ)^2) := by
    have qp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q from (mem_Icc.mp qMem).1)
    have np : (0 : ℝ) < n := by exact_mod_cast hn
    have card : (numSet q).card ≤ 2*q := by
      refine (card_le_card (filter_subset _ _)).trans ?_
      rw [card_range]
      have := (mem_Icc.mp qMem).1
      omega
    calc
      _ ≤ ∑ _ ∈ numSet q, 2*((H : ℝ)/((q : ℝ)*n))*(16*W^2*(n : ℝ)*A*L/(q : ℝ)^2) :=
        sum_le_sum fun z _ => each q z qMem
      _ = ((numSet q).card : ℝ)*(2*((H : ℝ)/((q : ℝ)*n))*(16*W^2*(n : ℝ)*A*L/(q : ℝ)^2)) := by
        rw [sum_const,nsmul_eq_mul]
      _ ≤ 2*(q : ℝ)*(2*((H : ℝ)/((q : ℝ)*n))*(16*W^2*(n : ℝ)*A*L/(q : ℝ)^2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card
      _ = C*(1/(q : ℝ)^2) := by unfold C; field_simp; ring
  unfold commonWideFamily commonAverageWideFamily
  simp only [← sum_sub_distrib]
  change ‖∑ q ∈ Icc 1 B,∑ z ∈ numSet q,diff q z‖ ≤ _
  refine (norm_sum_le _ _).trans ((sum_le_sum fun q hq => (norm_sum_le _ _).trans (row q hq)).trans ?_)
  rw [← mul_sum]
  have tail : (∑ q ∈ Icc 1 B, 1/(q : ℝ)^2) ≤ 2 := by
    simpa only [Nat.cast_one,div_one] using inverse_square_tail_Icc 1 B (by decide)
  exact (mul_le_mul_of_nonneg_left tail C0).trans_eq (by unfold C L; ring)

end

end B13NondividingResidueReductionProof

end

/- Average product integrable -/
section

namespace B13NondividingResidueReductionProof

open MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ProgressionApprox DyadicMixedB4WindowKernel

noncomputable section

theorem norm_progression_average_decay {u : ℕ} (hu : 0 < u) (l r : ℕ)
    {t : ℝ} (ht : t ≠ 0) : ‖progressionAverage u l r t‖ ≤ 1/((u : ℝ)*|t|) := by
  have ur : (0 : ℝ) < u := by exact_mod_cast hu
  by_cases ordered : l ≤ r
  · rw [progressionAverage,ite_eq_left ordered]
    let c : ℂ := 2*(Real.pi : ℂ)*(t : ℂ)*Complex.I
    let a : ℝ := (u : ℝ)*((l : ℝ)+1/2)
    let b : ℝ := (u : ℝ)*((r : ℝ)+1/2)
    have cNe : c ≠ 0 := by
      unfold c
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero)) (by exact_mod_cast ht)) Complex.I_ne_zero
    have phase_exp (x : ℝ) : phase (x*t) = Complex.exp (c*(x : ℂ)) := by
      unfold c phase
      push_cast
      congr 1
      ring
    have normC : ‖c‖ = 2*Real.pi*|t| := by
      unfold c
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
      norm_num
    have numerator : ‖Complex.exp (c*(b : ℂ))-Complex.exp (c*(a : ℂ))‖ ≤ 2 := by
      rw [← phase_exp, ← phase_exp]
      exact (norm_sub_le _ _).trans_eq (by simp; norm_num)
    change ‖(u : ℂ)⁻¹ * ∫ x in a..b, phase (x*t)‖ ≤ _
    simp_rw [phase_exp]
    rw [integral_exp_mul_complex cNe,norm_mul,norm_inv,Complex.norm_natCast,norm_div,normC]
    have pp : (1 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_three]
    calc
      _ ≤ (u : ℝ)⁻¹*(2/(2*Real.pi*|t|)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right numerator (by positivity)) (by positivity)
      _ = 1/((u : ℝ)*Real.pi*|t|) := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left zero_le_one (mul_pos ur (abs_pos.mpr ht))
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left pp ur.le) (abs_nonneg _)
  · rw [progressionAverage,ite_eq_right ordered,norm_zero]
    positivity

def continuousAverageProduct (x : ℝ) (u v l r p s : ℕ) (t : ℝ) : ℂ :=
  phase (-x*t) * (progressionAverage u l r t * progressionAverage v p s t)

theorem continuous_average_product (x : ℝ) (u v l r p s : ℕ) :
    Continuous (continuousAverageProduct x u v l r p s) := by
  have fc : Continuous (fun t : ℝ => phase (-x*t)) := by unfold phase; fun_prop
  exact fc.mul ((progressionAverage_continuous ..).mul (progressionAverage_continuous ..))

theorem norm_continuous_average_product_decay {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (x : ℝ) (l r p s : ℕ) {t : ℝ} (ht : t ≠ 0) :
    ‖continuousAverageProduct x u v l r p s t‖ ≤ 1/((u : ℝ)*(v : ℝ)*t^2) := by
  unfold continuousAverageProduct
  rw [norm_mul,norm_phase',one_mul,norm_mul]
  refine (mul_le_mul (norm_progression_average_decay hu l r ht)
    (norm_progression_average_decay hv p s ht) (norm_nonneg _) (by positivity)).trans_eq ?_
  rw [div_mul_div_comm,one_mul,show (u : ℝ) * |t| * ((v : ℝ) * |t|) = ((u : ℝ)*v) * |t|^2 by ring,sq_abs]

theorem continuous_average_product_integrable {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (x : ℝ) (l r p s : ℕ) :
    Integrable (continuousAverageProduct x u v l r p s) := by
  let C : ℝ := 2*((r : ℝ)*s+1)
  have cI : Integrable (fun t : ℝ => C*(1+t^2)⁻¹) := integrable_inv_one_add_sq.const_mul C
  refine cI.mono' (continuous_average_product x u v l r p s).aestronglyMeasurable ?_
  filter_upwards with t
  by_cases ht : |t| ≤ 1
  · have small : t^2 ≤ 1 := by nlinarith only [(abs_le.mp ht).1,(abs_le.mp ht).2]
    have cap : ‖continuousAverageProduct x u v l r p s t‖ ≤ (r : ℝ)*s := by
      unfold continuousAverageProduct
      rw [norm_mul,norm_phase',one_mul,norm_mul]
      exact mul_le_mul ((norm_progression_average_le_wave hu l r t).trans (wave_cap ..))
        ((norm_progression_average_le_wave hv p s t).trans (wave_cap ..))
        (norm_nonneg _) (Nat.cast_nonneg _)
    refine cap.trans ?_
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ ((r : ℝ)*s)*2 := mul_le_mul_of_nonneg_left (by linarith only [small]) (by positivity)
      _ ≤ _ := by unfold C; linarith
  · have ht0 : t ≠ 0 := by intro eq; simp [eq] at ht
    have big : 1 ≤ t^2 := by
      have a : 1 ≤ |t| := (lt_of_not_ge ht).le
      have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) a 2
      simpa only [one_pow,sq_abs] using h
    have ur : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have vr : (1 : ℝ) ≤ v := by exact_mod_cast hv
    have step : (1 : ℝ) ≤ (u : ℝ)*v := one_le_mul_of_one_le_of_one_le ur vr
    refine (norm_continuous_average_product_decay hu hv x l r p s ht0).trans ?_
    calc
      _ ≤ 1/t^2 := div_le_div_of_nonneg_left zero_le_one (by positivity) (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right step (sq_nonneg t))
      _ ≤ _ := by
        rw [← div_eq_mul_inv]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have c : 2 ≤ C := by
          unfold C
          have h : 0 ≤ (r : ℝ)*s := by positivity
          linarith only [h]
        have := mul_le_mul_of_nonneg_right c (sq_nonneg t)
        linarith only [big,this]

end

end B13NondividingResidueReductionProof

end

/- Average product tail -/
section

namespace B13NondividingResidueReductionProof

open MeasureTheory

noncomputable section

private theorem norm_tail_Ioi_le {f : ℝ → ℂ} (fi : Integrable f) {h C : ℝ}
    (hp : 0 < h) (bound : ∀ t > h, ‖f t‖ ≤ C/(t^2)) :
    ‖∫ t in Set.Ioi h,f t‖ ≤ C/h := by
  have cInt : IntegrableOn (fun t : ℝ => C*t^(-2 : ℝ)) (Set.Ioi h) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hp).const_mul C
  have equal (t : ℝ) (ht : t ∈ Set.Ioi h) : C/t^2 = C*t^(-2 : ℝ) := by
    rw [show (-2:ℝ) = -(2:ℝ) by norm_num,Real.rpow_neg (hp.trans ht).le,Real.rpow_two,div_eq_mul_inv]
  calc
    _ ≤ ∫ t in Set.Ioi h, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi h, C*t^(-2 : ℝ) :=
      setIntegral_mono_on fi.norm.integrableOn cInt measurableSet_Ioi
        (fun t ht => (bound t ht).trans_eq (equal t ht))
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) hp,show (-2:ℝ)+1 = -1 by norm_num,
        Real.rpow_neg_one]
      ring

theorem norm_window_sub_full_integral_le {f : ℝ → ℂ} (fi : Integrable f)
    {h C : ℝ} (hp : 0 < h) (decay : ∀ t : ℝ, t ≠ 0 → ‖f t‖ ≤ C/t^2) :
    ‖(∫ t in -h..h,f t) - ∫ t : ℝ,f t‖ ≤ 2*C/h := by
  have posTail : ‖∫ t in Set.Ioi h,f t‖ ≤ C/h :=
    norm_tail_Ioi_le fi hp (fun t ht => decay t (hp.trans ht).ne')
  have negTail : ‖∫ t in Set.Iic (-h),f t‖ ≤ C/h := by
    rw [← integral_comp_neg_Ioi h f]
    apply norm_tail_Ioi_le fi.comp_neg hp
    intro t near
    have h0 := (hp.trans near).ne'
    simpa only [show (-t)^2=t^2 by ring] using decay (-t) (neg_ne_zero.mpr h0)
  let I := Set.Ioc (-h) h
  have order : -h ≤ h := by linarith only [hp]
  have complement : Iᶜ = Set.Iic (-h) ∪ Set.Ioi h := by
    ext t
    simp only [I,Set.mem_compl_iff,Set.mem_Ioc,Set.mem_union,Set.mem_Iic,Set.mem_Ioi]
    constructor
    · intro outside
      by_cases left : -h < t
      · exact Or.inr (lt_of_not_ge fun le => outside ⟨left,le⟩)
      · exact Or.inl (le_of_not_gt left)
    · rintro (left | right) ⟨first,last⟩
      · exact (not_lt_of_ge left) first
      · exact (not_lt_of_ge last) right
  have disjoint : Disjoint (Set.Iic (-h)) (Set.Ioi h) :=
    Set.disjoint_left.mpr fun t ht near => (not_lt_of_ge (le_trans ht order)) near
  have sum : (∫ t in -h..h,f t) + (∫ t in Set.Iic (-h),f t) + (∫ t in Set.Ioi h,f t) =
      ∫ t : ℝ,f t := by
    rw [intervalIntegral.integral_of_le order,add_assoc,← setIntegral_union disjoint measurableSet_Ioi
      fi.integrableOn fi.integrableOn,← complement]
    exact integral_add_compl measurableSet_Ioc fi
  change ‖(∫ t in -h..h,f t) - ∫ t : ℝ,f t‖ ≤ _
  rw [← sum]
  have eq : (∫ t in -h..h,f t) - ((∫ t in -h..h,f t) + (∫ t in Set.Iic (-h),f t) + (∫ t in Set.Ioi h,f t)) =
      -((∫ t in Set.Iic (-h),f t)+(∫ t in Set.Ioi h,f t)) := by abel
  rw [eq,norm_neg]
  exact (norm_add_le _ _).trans ((add_le_add negTail posTail).trans_eq (by ring))

end

end B13NondividingResidueReductionProof

end

/- Centered wide windows -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open scoped Classical

noncomputable section

def wideHalfWidth (n H q : ℕ) : ℝ := (H : ℝ)/((q : ℝ)*n)

theorem integral_wide_arc_eq_clipped (n H q a : ℕ) (aq : a ≤ q) (f : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..1,(wideArc n H q a).indicator f t) =
      ∫ t in max 0 ((a : ℝ)/q-wideHalfWidth n H q)..
        min 1 ((a : ℝ)/q+wideHalfWidth n H q),f t := by
  let c := (a : ℝ)/q
  let h := wideHalfWidth n H q
  have hc0 : 0 ≤ c := by unfold c; positivity
  have hc1 : c ≤ 1 := by
    unfold c
    by_cases zero : q = 0
    · simp [zero]
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero zero)).mpr (by exact_mod_cast aq)
  have h0 : 0 ≤ h := by unfold h wideHalfWidth; positivity
  have order : max 0 (c-h) ≤ min 1 (c+h) := by
    rw [max_le_iff,le_min_iff,le_min_iff]
    constructor <;> constructor <;> linarith only [hc0,hc1,h0]
  have set : wideArc n H q a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (max 0 (c-h)) (min 1 (c+h)) := by
    ext t
    change (|t-c| ≤ h ∧ 0 ≤ t ∧ t ≤ 1) ↔ max 0 (c-h) ≤ t ∧ t ≤ min 1 (c+h)
    rw [abs_le,max_le_iff,le_min_iff]
    constructor
    · rintro ⟨⟨l,r⟩,u,v⟩
      exact ⟨⟨u,by linarith only [l]⟩,v,by linarith only [r]⟩
    · rintro ⟨⟨u,l⟩,v,r⟩
      exact ⟨⟨by linarith only [l],by linarith only [r]⟩,u,v⟩
  rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator (wide_arc_measurable ..),Set.inter_comm,set,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le order]

def standardRamanujan (q : ℕ) (k : ℤ) : ℂ := if q=1 then 1 else ramanujan q k

private theorem num_set_one : numSet 1 = {0,1} := by decide

theorem integral_shifted_wide_arc_sum (n H q : ℕ) (hn : 0 < n) (hq : 0 < q) (Hn : H ≤ n)
    (half : wideHalfWidth n H q ≤ 1/2) (F : ℝ → ℂ) (fc : Continuous F)
    (k : ℤ) :
    (∑ a ∈ numSet q,∫ t in (0 : ℝ)..1,(wideArc n H q a).indicator
      (fun x => phase ((k : ℝ)*x)*F (x-(a : ℝ)/q)) t) =
      standardRamanujan q k * ∫ t in -(wideHalfWidth n H q)..wideHalfWidth n H q,phase ((k : ℝ)*t)*F t := by
  let h := wideHalfWidth n H q
  let G (t : ℝ) := phase ((k : ℝ)*t)*F t
  have h0 : 0 ≤ h := by unfold h wideHalfWidth; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have width : h ≤ (1 : ℝ)/q := by
    unfold h wideHalfWidth
    apply (div_le_div_iff₀ (mul_pos hqR hnR) hqR).mpr
    rw [one_mul,mul_comm (H : ℝ)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Hn) hqR.le
  have translation (a : ℕ) (l r : ℝ) :
      (∫ t in l+(a : ℝ)/q..r+(a : ℝ)/q, phase ((k : ℝ)*t)*F (t-(a : ℝ)/q)) =
        phase ((k : ℝ)*((a : ℝ)/q)) * ∫ t in l..r,G t := by
    rw [← intervalIntegral.integral_comp_add_right, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [add_sub_cancel_right,mul_add,phase_add]
    unfold G
    ring
  by_cases one : q=1
  · subst q
    rw [num_set_one,standardRamanujan,ite_eq_left rfl,one_mul,
      sum_insert (by simp : (0 : ℕ) ∉ ({1} : Finset ℕ)),sum_singleton]
    rw [integral_wide_arc_eq_clipped _ _ _ _ (by decide),
      integral_wide_arc_eq_clipped _ _ _ _ (by decide)]
    have width0 : (0 : ℝ) ≤ h := h0
    have half0 : h ≤ 1/2 := half
    have z : max 0 ((0 : ℝ)/1-h) = 0 := by simp [max_eq_left (neg_nonpos.mpr width0)]
    have h1 : h ≤ 1 := by linarith only [half0]
    have z' : min 1 ((0 : ℝ)/1+h) = h := by simp [min_eq_right h1]
    have o : max 0 ((1 : ℝ)/1-h) = 1-h := by simp [max_eq_right (by linarith only [half0] : 0 ≤ 1-h)]
    have o' : min 1 ((1 : ℝ)/1+h) = 1 := by simp [min_eq_left (le_add_of_nonneg_right width0)]
    change (∫ t in max 0 ((0 : ℝ)/1-h)..min 1 ((0 : ℝ)/1+h),
       phase ((k : ℝ)*t)*F (t-(0 : ℝ)/1)) +
      (∫ t in max 0 ((1 : ℝ)/1-h)..min 1 ((1 : ℝ)/1+h),
       phase ((k : ℝ)*t)*F (t-(1 : ℝ)/1)) = ∫ t in -h..h,G t
    rw [z,z',o,o']
    have moved := translation 1 (-h) 0
    have unitPhase : phase (k : ℝ) = 1 := by
      unfold phase
      have eq : ((↑(2*Real.pi*(k : ℝ)) : ℂ)*Complex.I) =
          (k : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by push_cast; ring
      rw [eq]
      exact Complex.exp_int_mul_two_pi_mul_I k
    norm_num [unitPhase] at moved
    simp only [zero_div,one_div,inv_one,sub_zero]
    rw [show 1-h = -h+1 by ring,moved]
    change (∫ t in (0 : ℝ)..h,G t)+(∫ t in -h..0,G t) = _
    rw [add_comm]
    have phaseC : Continuous (fun t : ℝ => phase ((k : ℝ)*t)) := by unfold phase; fun_prop
    have gc : Continuous G := phaseC.mul fc
    exact intervalIntegral.integral_add_adjacent_intervals
      (gc.intervalIntegrable (-h) 0) (gc.intervalIntegrable 0 h)
  · have two : 1 < q := by omega
    rw [standardRamanujan,ite_eq_right one,ramanujan,sum_mul]
    refine sum_congr rfl fun a ha => ?_
    obtain ⟨aRange,cop⟩ := mem_filter.mp ha
    have aLe : a ≤ q := Nat.le_of_lt_succ (mem_range.mp aRange)
    have aPos : 0 < a := by
      by_contra! low
      have zz : a=0 := by omega
      subst a
      exact one (q.coprime_zero_left.mp cop)
    have aLt : a < q := by
      apply lt_of_le_of_ne aLe
      intro equal
      subst a
      exact one (by simpa [Nat.coprime_self] using cop)
    have left : 1/(q : ℝ) ≤ (a : ℝ)/q := div_le_div_of_nonneg_right (by exact_mod_cast aPos) hqR.le
    have right : (a : ℝ)/q ≤ 1-1/(q : ℝ) := by
      apply (div_le_iff₀ hqR).mpr
      have space : (a : ℝ)+1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt aLt
      rw [show (1-1/(q : ℝ))*(q : ℝ) = (q : ℝ)-1 by field_simp]
      linarith only [space]
    rw [integral_wide_arc_eq_clipped _ _ _ _ aLe,
      max_eq_right (by linarith only [width,left] : 0 ≤ (a : ℝ)/q-h),
      min_eq_right (by linarith only [width,right] : (a : ℝ)/q+h ≤ 1)]
    have shifted := translation a (-h) h
    rw [show -h+(a : ℝ)/q = (a : ℝ)/q-h by ring, add_comm h ((a : ℝ)/q)] at shifted
    exact shifted

end

end B13NondividingResidueReductionProof

end

/- Standard ramanujan -/
section

namespace B13NondividingResidueReductionProof

open Finset ArithmeticFunction
open DyadicMixedB4Geometric DyadicMixedB4ArcCenters DyadicMixedB4Ramanujan
open DyadicMixedB4MoebiusGauss DyadicMixedB4ModulusTail DyadicMixedB4GcdHarmonic
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

private def divisorMass (n : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun d => if d∣n then (d : ℂ) else 0,by split_ifs <;> simp⟩

theorem standard_ramanujan_moebius {q : ℕ} (hq : 0 < q) (n : ℕ) :
    standardRamanujan q (-(n : ℤ)) =
      ∑ e ∈ q.divisors, moebiusComplex e * if (q/e)∣n then ((q/e : ℕ) : ℂ) else 0 := by
  by_cases q1 : q=1
  · subst q
    simp [standardRamanujan,moebiusComplex]
  have q2 : 1 < q := by omega
  let _ : NeZero q := ⟨hq.ne'⟩
  have conjEq :
      ramanujan q (-(n : ℤ)) = (starRingEnd ℂ) (ramanujan q (n : ℤ)) := by
    simp only [ramanujan,Int.cast_neg,neg_mul,phase_neg,map_sum]
  rw [standardRamanujan,ite_eq_right q1,conjEq,ramanujan_moebius q2,map_sum]
  refine sum_congr rfl fun e _ => ?_
  unfold moebiusComplex
  by_cases d : (q/e)∣n <;> simp [d]

private theorem standard_ramanujan_eq_mul {q : ℕ} (hq : 0 < q) (n : ℕ) :
    standardRamanujan q (-(n : ℤ)) = ((μ : ArithmeticFunction ℂ)*divisorMass n) q := by
  rw [standard_ramanujan_moebius hq,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b =>
    (μ : ArithmeticFunction ℂ) a*divisorMass n b)]
  rfl

theorem sum_standard_ramanujan_divisors (n g : ℕ) :
    (∑ q ∈ g.divisors, standardRamanujan q (-(n : ℤ))) = if g∣n then (g : ℂ) else 0 := by
  calc
    _ = ∑ q ∈ g.divisors, ((μ : ArithmeticFunction ℂ)*divisorMass n) q :=
      sum_congr rfl fun q hq => standard_ramanujan_eq_mul (Nat.pos_of_mem_divisors hq) n
    _ = ((((μ : ArithmeticFunction ℂ)*divisorMass n)*ζ : ArithmeticFunction ℂ) g) := by rw [coe_mul_zeta_apply]
    _ = divisorMass n g := by
      rw [mul_comm (μ : ArithmeticFunction ℂ) (divisorMass n),mul_assoc,coe_moebius_mul_coe_zeta,mul_one]
    _ = _ := rfl

theorem norm_standard_ramanujan_le {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    ‖standardRamanujan q (-(n : ℤ))‖ ≤ ∑ d ∈ n.divisors, if d∣q then (d : ℝ) else 0 := by
  rw [standard_ramanujan_moebius hq]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ e ∈ q.divisors, if (q/e)∣n then ((q/e : ℕ) : ℝ) else 0 := by
      refine sum_le_sum fun e _ => ?_
      by_cases d : (q/e)∣n
      · rw [ite_eq_left d,ite_eq_left d,norm_mul,Complex.norm_natCast]
        exact mul_le_of_le_one_left (Nat.cast_nonneg _) (norm_moebiusComplex_le_one e)
      · simp [d]
    _ = _ := by
      rw [Nat.sum_div_divisors q (fun e => if e∣n then (e : ℝ) else 0),← sum_filter,← sum_filter]
      congr 1
      ext d
      simp only [mem_filter,Nat.mem_divisors]
      exact ⟨fun ⟨⟨dq,_⟩,dn⟩ => ⟨⟨dn,hn.ne'⟩,dq⟩,fun ⟨⟨dn,_⟩,dq⟩ => ⟨⟨dq,hq.ne'⟩,dn⟩⟩

theorem sum_norm_standard_ramanujan_over_q_le (n B : ℕ) (hn : 0 < n) :
    (∑ q ∈ Icc 1 B, ‖standardRamanujan q (-(n : ℤ))‖/(q : ℝ)) ≤
      (n.divisors.card : ℝ)*(1+Real.log (B : ℝ)) := by
  let Q := Icc 1 B
  let w (d q : ℕ) : ℝ := if d∣q then (d : ℝ) else 0
  have row (d : ℕ) (hd : d ∈ n.divisors) :
      (∑ q ∈ Q, w d q/(q : ℝ)) ≤ 1+Real.log (B : ℝ) := by
    have dp := Nat.pos_of_mem_divisors hd
    have dr : (0 : ℝ) < d := by exact_mod_cast dp
    calc
      _ = (d : ℝ)*∑ q ∈ Q.filter (fun q => d∣q), (q : ℝ)⁻¹ := by
        rw [mul_sum,sum_filter]
        refine sum_congr rfl fun q _ => ?_
        by_cases dvd : d∣q <;> simp [w,dvd,div_eq_mul_inv]
      _ = ∑ q ∈ Icc 1 (B/d), (q : ℝ)⁻¹ := by
        unfold Q
        rw [sum_inverse_multiples d B dp,← mul_assoc,mul_inv_cancel₀ dr.ne',one_mul]
      _ ≤ _ := (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self B d))
        (fun _ _ _ => by positivity)).trans (sum_inverse_Icc_le B)
  calc
    _ ≤ ∑ q ∈ Q, (∑ d ∈ n.divisors,w d q)/(q : ℝ) :=
      sum_le_sum fun q hq => div_le_div_of_nonneg_right
        (norm_standard_ramanujan_le (mem_Icc.mp hq).1 hn) (Nat.cast_nonneg _)
    _ = ∑ d ∈ n.divisors,∑ q ∈ Q,w d q/(q : ℝ) := by
      simp only [div_eq_mul_inv,sum_mul]
      exact sum_comm
    _ ≤ ∑ _ ∈ n.divisors,(1+Real.log (B : ℝ)) := sum_le_sum row
    _ = _ := by rw [sum_const,nsmul_eq_mul]

end

end B13NondividingResidueReductionProof

end

/- Wide average tail sum -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcCenters
open DyadicMixedB4ProgressionApprox DyadicMixedB4WindowKernel
open scoped Classical

noncomputable section

def averagePairShell (q : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ)
    (gate : α → β → Prop) (t : ℝ) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if gate i j ∧ q∣u i ∧ q∣v j then
    (a i * progressionAverage (u i) (l i) (r i) t) *
    (b j * progressionAverage (v j) (p j) (s j) t) else 0

private theorem average_pair_shell_continuous (q : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) :
    Continuous (averagePairShell q I J u l r v p s a b gate) := by
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  by_cases ok : gate i j ∧ q∣u i ∧ q∣v j
  · simp only [ite_eq_left ok]
    change Continuous (((fun _ : ℝ => a i) * progressionAverage (u i) (l i) (r i)) *
      ((fun _ : ℝ => b j) * progressionAverage (v j) (p j) (s j)))
    exact (continuous_const.mul (progressionAverage_continuous ..)).mul
      (continuous_const.mul (progressionAverage_continuous ..))
  · simp only [ite_eq_right ok]
    exact continuous_const

theorem average_pair_shell_decomposition (q : ℕ) (x : ℝ)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ)
    (gate : α → β → Prop) (t : ℝ) :
    phase (-x*t)*averagePairShell q I J u l r v p s a b gate t =
      ∑ i ∈ I, ∑ j ∈ J, if gate i j ∧ q∣u i ∧ q∣v j then
        a i*b j*continuousAverageProduct x (u i) (v j) (l i) (r i) (p j) (s j) t else 0 := by
  unfold averagePairShell
  simp only [mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases d : gate i j ∧ q∣u i ∧ q∣v j
  · simp only [ite_eq_left d,continuousAverageProduct]
    ring
  · simp [d]

theorem common_average_wide_eq_centered (n B H : ℕ) (hn : 0 < n) (thin : 4*H*B ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) :
    commonAverageWideFamily n B H I J u l r v p s a b gate =
      ∑ q ∈ Icc 1 B, standardRamanujan q (-(n : ℤ)) *
        ∫ t in -(wideHalfWidth n H q)..wideHalfWidth n H q,
          phase (((-(n : ℤ)) : ℝ)*t)*averagePairShell q I J u l r v p s a b gate t := by
  unfold commonAverageWideFamily
  refine sum_congr rfl fun q hq => ?_
  have qPos : 0 < q := (mem_Icc.mp hq).1
  have br : 0 < B := qPos.trans_le (mem_Icc.mp hq).2
  have H4 : 4*H ≤ n := (Nat.le_mul_of_pos_right _ br).trans thin
  have Hn : H ≤ n := by omega
  have half : wideHalfWidth n H q ≤ 1/2 := by
    have qr : (1 : ℝ) ≤ q := by exact_mod_cast qPos
    have nr : (0 : ℝ) < n := by exact_mod_cast hn
    have wider : (2 : ℝ)*H ≤ n := by exact_mod_cast (show 2*H ≤ n by omega)
    unfold wideHalfWidth
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).mpr
    rw [one_mul,mul_comm (H : ℝ)]
    exact wider.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right qr nr.le)
  exact integral_shifted_wide_arc_sum n H q hn qPos Hn half _ (average_pair_shell_continuous ..) (-(n : ℤ))

def fullCommonAverageFamily (n B : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) : ℂ :=
  ∑ q ∈ Icc 1 B, standardRamanujan q (-(n : ℤ)) *
    ∫ t : ℝ, phase (((-(n : ℤ)) : ℝ)*t)*averagePairShell q I J u l r v p s a b gate t

theorem norm_common_average_wide_tail_le (n A B H : ℕ) (hn : 0 < n) (Hpos : 0 < H)
    (Apos : 0 < A) (thin : 4*H*B ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    {W : ℝ} (W0 : 0 ≤ W) (uSteps : ∀ i ∈ I, u i ∈ Icc 1 A) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 A)
    (uWeights : ∀ x ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i=x), ‖a i‖) ≤ W)
    (vWeights : ∀ x ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j=x), ‖b j‖) ≤ W) :
    ‖commonAverageWideFamily n B H I J u l r v p s a b gate -
        fullCommonAverageFamily n B I J u l r v p s a b gate‖ ≤
      2*(W*(1+Real.log (A : ℝ)))^2*((n : ℝ)/H)*(n.divisors.card : ℝ)*(1+Real.log (B : ℝ)) := by
  let K := W*(1+Real.log (A : ℝ))
  let F (q : ℕ) (t : ℝ) := phase (((-(n : ℤ)) : ℝ)*t)*averagePairShell q I J u l r v p s a b gate t
  have logA0 : 0 ≤ 1+Real.log (A : ℝ) := add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast Apos))
  have each (q : ℕ) (qMem : q ∈ Icc 1 B) :
      ‖(∫ t in -(wideHalfWidth n H q)..wideHalfWidth n H q,F q t)-∫ t : ℝ,F q t‖ ≤
      (2*K^2*((n : ℝ)/H))/(q : ℝ) := by
    have qPos : 0 < q := (mem_Icc.mp qMem).1
    have pr (t : ℝ) : F q t = ∑ i ∈ I, ∑ j ∈ J, if gate i j ∧ q∣u i ∧ q∣v j then
        a i*b j*continuousAverageProduct (n : ℝ) (u i) (v j) (l i) (r i) (p j) (s j) t else 0 := by
      have eq := average_pair_shell_decomposition q (n : ℝ) I J u l r v p s a b gate t
      simpa only [F,Int.cast_neg,Int.cast_natCast] using eq
    have integrable : Integrable (F q) := by
      rw [show F q = _ from funext pr]
      refine integrable_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => ?_))
      by_cases d : gate i j ∧ q∣u i ∧ q∣v j
      · simp only [ite_eq_left d]
        exact (continuous_average_product_integrable (mem_Icc.mp (uSteps i hi)).1
          (mem_Icc.mp (vSteps j hj)).1 (n : ℝ) (l i) (r i) (p j) (s j)).const_mul _
      · simp only [ite_eq_right d]
        exact integrable_zero ..
    have decay (t : ℝ) (ht : t ≠ 0) : ‖F q t‖ ≤ (K/(q : ℝ))^2/t^2 := by
      let P (i : α) := ‖a i‖*(1/(u i : ℝ))
      let Q (j : β) := ‖b j‖*(1/(v j : ℝ))
      let I' := I.filter (fun i => q∣u i)
      let J' := J.filter (fun j => q∣v j)
      rw [pr]
      refine (norm_sum_le _ _).trans ((sum_le_sum fun i _ => norm_sum_le _ _).trans ?_)
      calc
        _ ≤ ∑ i ∈ I, ∑ j ∈ J, if q∣u i ∧ q∣v j then P i*Q j/t^2 else 0 := by
          refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
          by_cases divides : q∣u i ∧ q∣v j
          · rw [ite_eq_left divides]
            by_cases g : gate i j
            · have active : gate i j ∧ q∣u i ∧ q∣v j := ⟨g,divides⟩
              rw [ite_eq_left active,norm_mul,norm_mul]
              refine (mul_le_mul_of_nonneg_left (norm_continuous_average_product_decay
                (mem_Icc.mp (uSteps i hi)).1 (mem_Icc.mp (vSteps j hj)).1 (n : ℝ) _ _ _ _ ht)
                (by positivity)).trans_eq ?_
              unfold P Q
              ring
            · have inactive : ¬(gate i j ∧ q∣u i ∧ q∣v j) := fun yes => g yes.1
              rw [ite_eq_right inactive,norm_zero]
              unfold P Q
              positivity
          · simp only [ite_eq_right (fun yes : gate i j ∧ q∣u i ∧ q∣v j => divides yes.2),
              ite_eq_right divides,norm_zero,le_rfl]
        _ = (∑ i ∈ I',P i)*(∑ j ∈ J',Q j)/t^2 := by
          rw [sum_mul_sum,div_eq_mul_inv,sum_mul]
          simp only [I',J',sum_filter]
          refine sum_congr rfl fun i _ => ?_
          rw [sum_mul]
          by_cases A : q∣u i
          · simp only [A,true_and,ite_true]
            refine sum_congr rfl fun j _ => ?_
            by_cases B : q∣v j <;> simp [B,div_eq_mul_inv]
          · simp [A]
        _ ≤ _ := by
          have l : (∑ i ∈ I',P i) ≤ K/(q : ℝ) := by
            have eq : W*((1 : ℝ)/q*(1+Real.log (A : ℝ))) = K/(q : ℝ) := by unfold K; ring
            exact (divisible_inverse_step_mass_le 1 A q qPos I u a W0 uSteps uWeights).trans_eq eq
          have r : (∑ j ∈ J',Q j) ≤ K/(q : ℝ) := by
            have eq : W*((1 : ℝ)/q*(1+Real.log (A : ℝ))) = K/(q : ℝ) := by unfold K; ring
            exact (divisible_inverse_step_mass_le 1 A q qPos J v b W0 vSteps vWeights).trans_eq eq
          rw [pow_two (K/(q : ℝ))]
          have kPos : 0 ≤ K/(q : ℝ) := by unfold K; positivity
          exact div_le_div_of_nonneg_right (mul_le_mul l r (by unfold Q; positivity) kPos) (sq_nonneg _)
    have hp : 0 < wideHalfWidth n H q := by unfold wideHalfWidth; positivity
    refine (norm_window_sub_full_integral_le integrable hp decay).trans_eq ?_
    unfold wideHalfWidth
    have qR : (q : ℝ) ≠ 0 := by exact_mod_cast qPos.ne'
    have nR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have HR : (H : ℝ) ≠ 0 := by exact_mod_cast Hpos.ne'
    field_simp
  rw [common_average_wide_eq_centered n B H hn thin,fullCommonAverageFamily,← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  change (∑ q ∈ Icc 1 B, ‖standardRamanujan q (-(n : ℤ))*(∫ t in -(wideHalfWidth n H q)..wideHalfWidth n H q,F q t) -
    standardRamanujan q (-(n : ℤ))*(∫ t : ℝ,F q t)‖) ≤ _
  calc
    _ ≤ ∑ q ∈ Icc 1 B, ‖standardRamanujan q (-(n : ℤ))‖*((2*K^2*((n : ℝ)/H))/(q : ℝ)) := by
      refine sum_le_sum fun q hq => ?_
      rw [← mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (each q hq) (norm_nonneg _)
    _ = (2*K^2*((n : ℝ)/H))*∑ q ∈ Icc 1 B, ‖standardRamanujan q (-(n : ℤ))‖/(q : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left (sum_norm_standard_ramanujan_over_q_le n B hn) (by positivity)).trans_eq
      (by unfold K; ring)

end

end B13NondividingResidueReductionProof

end

/- Average product overlap -/
section

namespace B13NondividingResidueReductionProof

open MeasureTheory ContinuousLinearMap
open DyadicMixedB4Geometric DyadicMixedB4ProgressionApprox
open scoped FourierTransform Convolution Classical

noncomputable section

def currentBinEdge (u x : ℕ) : ℝ := (u : ℝ)*((x : ℝ)+1/2)

private def progressionDensity (u l r : ℕ) : ℝ → ℂ :=
  (Set.Icc (currentBinEdge u l) (currentBinEdge u r)).indicator (fun _ => (u : ℂ)⁻¹)

private theorem progression_density_integrable (u l r : ℕ) : Integrable (progressionDensity u l r) := by
  unfold progressionDensity
  exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp [Real.volume_Icc]))

private theorem phase_mul_neg_eq_fourier (x t : ℝ) :
    phase (x*(-t)) = Complex.exp ((↑(-2*Real.pi*x*t) : ℂ)*Complex.I) := by
  unfold phase
  push_cast
  congr 1
  ring

private theorem fourier_progression_density (u l r : ℕ) (t : ℝ) :
    𝓕 (progressionDensity u l r) t = progressionAverage u l r (-t) := by
  let a := currentBinEdge u l
  let b := currentBinEdge u r
  let I := Set.Icc a b
  rw [Real.fourier_real_eq_integral_exp_smul]
  have eq (x : ℝ) : Complex.exp ((↑(-2*Real.pi*x*t) : ℂ)*Complex.I) • progressionDensity u l r x =
      I.indicator (fun y => (u : ℂ)⁻¹*phase (y*(-t))) x := by
    by_cases hi : x ∈ I
    · have inside : x ∈ Set.Icc (currentBinEdge u l) (currentBinEdge u r) := hi
      simp only [progressionDensity,Set.indicator_of_mem inside,Set.indicator_of_mem hi,smul_eq_mul,
        ← phase_mul_neg_eq_fourier]
      ring
    · have outside : x ∉ Set.Icc (currentBinEdge u l) (currentBinEdge u r) := hi
      simp only [progressionDensity,Set.indicator_of_notMem outside,Set.indicator_of_notMem hi,smul_zero]
  simp_rw [eq]
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc]
  by_cases h : l ≤ r
  · have order : a ≤ b := by
      have lr : (l : ℝ) ≤ r := by exact_mod_cast h
      unfold a b currentBinEdge
      gcongr
    rw [← intervalIntegral.integral_of_le order,intervalIntegral.integral_const_mul,progressionAverage,ite_eq_left h]
    rfl
  · rw [progressionAverage,ite_eq_right h]
    by_cases z : u=0
    · simp [z,a,b,currentBinEdge]
    · have pos : (0 : ℝ) < u := by exact_mod_cast Nat.pos_of_ne_zero z
      have inv : b < a := by
        unfold a b currentBinEdge
        have lt : (r : ℝ) < l := by exact_mod_cast (lt_of_not_ge h)
        exact mul_lt_mul_of_pos_left (by linarith only [lt] : (r : ℝ)+1/2 < (l : ℝ)+1/2) pos
      rw [Set.Ioc_eq_empty (not_lt_of_ge inv.le), setIntegral_empty]

def progressionOverlap (u v l r p s : ℕ) (x : ℝ) : ℝ :=
  max 0 (min (currentBinEdge u r) (x-currentBinEdge v p) -
    max (currentBinEdge u l) (x-currentBinEdge v s))

private theorem progression_density_convolution_eq (u v l r p s : ℕ) (x : ℝ) :
    (progressionDensity u l r ⋆[mul ℂ ℂ] progressionDensity v p s) x =
      ((progressionOverlap u v l r p s x : ℝ) : ℂ)*((u : ℂ)⁻¹*(v : ℂ)⁻¹) := by
  let a := max (currentBinEdge u l) (x-currentBinEdge v s)
  let b := min (currentBinEdge u r) (x-currentBinEdge v p)
  let I := Set.Icc a b
  let C := (u : ℂ)⁻¹*(v : ℂ)⁻¹
  rw [convolution_def]
  have mem (t : ℝ) : t ∈ I ↔ t ∈ Set.Icc (currentBinEdge u l) (currentBinEdge u r) ∧
      x-t ∈ Set.Icc (currentBinEdge v p) (currentBinEdge v s) := by
    unfold I a b
    simp only [Set.mem_Icc,max_le_iff,le_min_iff]
    constructor
    · rintro ⟨⟨A,B⟩,D,E⟩
      exact ⟨⟨A,D⟩,⟨by linarith only [E],by linarith only [B]⟩⟩
    · rintro ⟨⟨A,D⟩,B,E⟩
      exact ⟨⟨A,by linarith only [E]⟩,D,by linarith only [B]⟩
  have eq (t : ℝ) : mul ℂ ℂ (progressionDensity u l r t) (progressionDensity v p s (x-t)) =
      I.indicator (fun _ => C) t := by
    change progressionDensity u l r t * progressionDensity v p s (x-t) = _
    by_cases left : t ∈ Set.Icc (currentBinEdge u l) (currentBinEdge u r) <;>
      by_cases right : x-t ∈ Set.Icc (currentBinEdge v p) (currentBinEdge v s) <;>
      simp [progressionDensity,mem,left,right,C]
  simp_rw [eq]
  rw [integral_indicator measurableSet_Icc,setIntegral_const,Measure.real,Real.volume_Icc,
    ENNReal.toReal_ofReal',Complex.real_smul, max_comm]
  rfl

theorem integral_continuous_average_product_eq_overlap {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (x : ℝ) (l r p s : ℕ) :
    (∫ t : ℝ, continuousAverageProduct x u v l r p s t) =
      ((progressionOverlap u v l r p s x : ℝ) : ℂ)*((u : ℂ)⁻¹*(v : ℂ)⁻¹) := by
  let f := progressionDensity u l r
  let g := progressionDensity v p s
  let F := f ⋆[mul ℂ ℂ] g
  have fi : Integrable f := progression_density_integrable u l r
  have gi : Integrable g := progression_density_integrable v p s
  have integrable : Integrable F := fi.integrable_convolution (mul ℂ ℂ) gi
  have conv (y : ℝ) : F y = _ := progression_density_convolution_eq u v l r p s y
  have continuous : Continuous F := by
    rw [show F = _ from funext conv]
    have h1 : Continuous (fun t : ℝ => min (currentBinEdge u r) (t-currentBinEdge v p)) :=
      continuous_const.min (continuous_id.sub continuous_const)
    have h2 : Continuous (fun t : ℝ => max (currentBinEdge u l) (t-currentBinEdge v s)) :=
      continuous_const.max (continuous_id.sub continuous_const)
    have real : Continuous (progressionOverlap u v l r p s) := continuous_const.max (h1.sub h2)
    exact (Complex.continuous_ofReal.comp real).mul continuous_const
  have transform (t : ℝ) : 𝓕 F t =
      progressionAverage u l r (-t)*progressionAverage v p s (-t) := by
    rw [show 𝓕 F t = 𝓕 f t * 𝓕 g t from Real.fourier_mul_convolution_eq fi gi t]
    exact congrArg₂ (·*·) (fourier_progression_density u l r t) (fourier_progression_density v p s t)
  have inv : ∀ t : ℝ, (𝓕⁻ F) t = progressionAverage u l r t * progressionAverage v p s t := by
    intro t
    rw [Real.fourierInv_eq_fourier_neg,transform,neg_neg]
  have transformI : Integrable (𝓕 F) := by
    rw [show (𝓕 F) = _ from funext transform]
    have h := (continuous_average_product_integrable hu hv 0 l r p s).comp_neg
    simpa [continuousAverageProduct,phase] using h
  calc
    _ = 𝓕 (𝓕⁻ F) x := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
        change continuousAverageProduct x u v l r p s t =
          Complex.exp ((↑(-2*Real.pi*t*x) : ℂ)*Complex.I) • (𝓕⁻ F) t
        rw [inv,← phase_mul_neg_eq_fourier,smul_eq_mul]
        unfold continuousAverageProduct
        rw [mul_comm t (-x)])
    _ = F x := integrable.fourier_fourierInv_eq transformI continuous.continuousAt
    _ = _ := conv x

end

end B13NondividingResidueReductionProof

end

/- Full average overlap -/
section

namespace B13NondividingResidueReductionProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcCenters
open scoped Classical

noncomputable section

def overlapMass (n u v l r p s : ℕ) : ℂ :=
  (progressionOverlap u v l r p s (n : ℝ) : ℂ)*((u : ℂ)⁻¹*(v : ℂ)⁻¹)

theorem integral_average_pair_shell_eq_overlap (n q : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    (uPos : ∀ i ∈ I, 0 < u i) (vPos : ∀ j ∈ J, 0 < v j) :
    (∫ t : ℝ,phase (((-(n : ℤ)) : ℝ)*t)*averagePairShell q I J u l r v p s a b gate t) =
      ∑ i ∈ I, ∑ j ∈ J, if gate i j ∧ q∣u i ∧ q∣v j then
        a i*b j*overlapMass n (u i) (v j) (l i) (r i) (p j) (s j) else 0 := by
  let F (i : α) (j : β) (t : ℝ) := if gate i j ∧ q∣u i ∧ q∣v j then
    a i*b j*continuousAverageProduct (n : ℝ) (u i) (v j) (l i) (r i) (p j) (s j) t else 0
  have entry (i : α) (j : β) (hi : i ∈ I) (hj : j ∈ J) : Integrable (F i j) := by
    by_cases h : gate i j ∧ q∣u i ∧ q∣v j
    · simpa only [F,ite_eq_left h] using
        (continuous_average_product_integrable (uPos i hi) (vPos j hj) (n : ℝ) (l i) (r i) (p j) (s j)).const_mul (a i*b j)
    · simp only [F,ite_eq_right h]
      exact integrable_zero ..
  have rows (i : α) (hi : i ∈ I) : Integrable (fun t => ∑ j ∈ J,F i j t) :=
    integrable_finsetSum _ fun j hj => entry i j hi hj
  have equation (t : ℝ) : phase (((-(n : ℤ)) : ℝ)*t)*averagePairShell q I J u l r v p s a b gate t =
      ∑ i ∈ I, ∑ j ∈ J,F i j t := by
    simpa only [F, Int.cast_neg, Int.cast_natCast] using
      average_pair_shell_decomposition q (n : ℝ) I J u l r v p s a b gate t
  simp_rw [equation]
  rw [integral_finsetSum _ rows]
  refine sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ (fun j hj => entry i j hi hj)]
  refine sum_congr rfl fun j hj => ?_
  by_cases h : gate i j ∧ q∣u i ∧ q∣v j
  · simp only [F,ite_eq_left h,integral_const_mul]
    rw [integral_continuous_average_product_eq_overlap (uPos i hi) (vPos j hj),overlapMass]
  · simp [F,h]

def singularOverlapFamily (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ)
    (gate : α → β → Prop) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if gate i j ∧ (u i).gcd (v j) ∣ n then
    a i*b j*((u i).gcd (v j) : ℂ)*overlapMass n (u i) (v j) (l i) (r i) (p j) (s j) else 0

theorem full_common_average_eq_singular_overlap (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    (uSteps : ∀ i ∈ I, u i ∈ Icc 1 n) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 n) :
    fullCommonAverageFamily n n I J u l r v p s a b gate = singularOverlapFamily n I J u l r v p s a b gate := by
  let F (q : ℕ) (i : α) (j : β) : ℂ :=
    if gate i j ∧ q∣u i ∧ q∣v j then
      standardRamanujan q (-(n : ℤ))*a i*b j*overlapMass n (u i) (v j) (l i) (r i) (p j) (s j) else 0
  unfold fullCommonAverageFamily singularOverlapFamily
  calc
    _ = ∑ q ∈ Icc 1 n, ∑ i ∈ I, ∑ j ∈ J,F q i j := by
      refine sum_congr rfl fun q _ => ?_
      rw [integral_average_pair_shell_eq_overlap n q I J u l r v p s a b gate
        (fun i hi => (mem_Icc.mp (uSteps i hi)).1) (fun j hj => (mem_Icc.mp (vSteps j hj)).1),mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      by_cases ok : gate i j ∧ q∣u i ∧ q∣v j <;> simp [F,ok,mul_assoc]
    _ = ∑ i ∈ I, ∑ j ∈ J, ∑ q ∈ Icc 1 n,F q i j := by
      rw [sum_comm]
      exact sum_congr rfl fun _ _ => sum_comm
    _ = _ := by
      refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
      by_cases active : gate i j
      · let d := (u i).gcd (v j)
        have dp : 0 < d := Nat.gcd_pos_of_pos_left _ (mem_Icc.mp (uSteps i hi)).1
        have dn : d ≤ n := (Nat.gcd_le_left _ (mem_Icc.mp (uSteps i hi)).1).trans (mem_Icc.mp (uSteps i hi)).2
        have same : ((Icc 1 n).filter (fun q => q∣u i ∧ q∣v j)) = d.divisors := by
          ext q
          simp only [mem_filter,mem_Icc,Nat.mem_divisors]
          constructor
          · rintro ⟨_,qu,qv⟩
            exact ⟨Nat.dvd_gcd qu qv,dp.ne'⟩
          · rintro ⟨Q,_⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos Q dp,(Nat.le_of_dvd dp Q).trans dn⟩,
              Q.trans (Nat.gcd_dvd_left _ _),Q.trans (Nat.gcd_dvd_right _ _)⟩
        have eq :
            (∑ q ∈ Icc 1 n,F q i j) = (a i*b j*overlapMass n (u i) (v j) (l i) (r i) (p j) (s j)) *
              (∑ q ∈ d.divisors, standardRamanujan q (-(n : ℤ))) := by
          rw [← same,mul_sum, sum_filter]
          refine sum_congr rfl fun q _ => ?_
          by_cases div : q∣u i ∧ q∣v j <;> simp [F,active,div] <;> ring
        rw [eq,sum_standard_ramanujan_divisors]
        by_cases hn : d∣n <;> simp [active,hn,d] <;> ring
      · simp [F,active]

theorem norm_overlap_mass_le {n u v l r p s : ℕ} (hu : 0 < u) (hr : r ≤ n/u) :
    ‖overlapMass n u v l r p s‖ ≤ (n : ℝ)/((u : ℝ)*v) := by
  have lo : 0 ≤ progressionOverlap u v l r p s (n : ℝ) := le_max_left _ _
  have hi : progressionOverlap u v l r p s (n : ℝ) ≤ (n : ℝ) := by
    unfold progressionOverlap
    apply max_le (Nat.cast_nonneg _)
    have rmax := min_le_left (currentBinEdge u r) ((n : ℝ)-currentBinEdge v p)
    have lmin := le_max_left (currentBinEdge u l) ((n : ℝ)-currentBinEdge v s)
    have load : (u : ℝ)*(r : ℝ) ≤ n := by
      exact_mod_cast (show u*r ≤ n by rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hu).mp hr)
    unfold currentBinEdge at rmax lmin ⊢
    nlinarith only [rmax,lmin,load,show 0 ≤ (u : ℝ)*(l : ℝ) by positivity]
  unfold overlapMass
  rw [norm_mul,norm_mul,norm_inv,norm_inv,Complex.norm_real,Complex.norm_natCast,Complex.norm_natCast,
    Real.norm_eq_abs,abs_of_nonneg lo]
  exact (mul_le_mul_of_nonneg_right hi (by positivity)).trans_eq (by ring)

theorem norm_full_common_average_shell_le (n A q : ℕ) (qPos : 0 < q)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    {W : ℝ} (W0 : 0 ≤ W) (Apos : 0 < A)
    (uSteps : ∀ i ∈ I, u i ∈ Icc 1 A) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 A)
    (uEnds : ∀ i ∈ I, r i ≤ n/u i)
    (uWeights : ∀ x ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i=x), ‖a i‖) ≤ W)
    (vWeights : ∀ x ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j=x), ‖b j‖) ≤ W) :
    ‖∫ t : ℝ,phase (((-(n : ℤ)) : ℝ)*t)*averagePairShell q I J u l r v p s a b gate t‖ ≤
      (n : ℝ)*(W*(1+Real.log (A : ℝ)))^2/(q : ℝ)^2 := by
  let P (i : α) := ‖a i‖*(1/(u i : ℝ))
  let Q (j : β) := ‖b j‖*(1/(v j : ℝ))
  let I' := I.filter (fun i => q∣u i)
  let J' := J.filter (fun j => q∣v j)
  let K := W*((1 : ℝ)/q*(1+Real.log (A : ℝ)))
  have K0 : 0 ≤ K := by
    have log0 : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg (by exact_mod_cast Apos)
    unfold K
    positivity
  have capU : (∑ i ∈ I',P i) ≤ K :=
    divisible_inverse_step_mass_le 1 A q qPos I u a W0 uSteps uWeights
  have capV : (∑ j ∈ J',Q j) ≤ K :=
    divisible_inverse_step_mass_le 1 A q qPos J v b W0 vSteps vWeights
  rw [integral_average_pair_shell_eq_overlap n q I J u l r v p s a b gate
    (fun i hi => (mem_Icc.mp (uSteps i hi)).1) (fun j hj => (mem_Icc.mp (vSteps j hj)).1)]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun i _ => norm_sum_le _ _).trans ?_)
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, if q∣u i ∧ q∣v j then (n : ℝ)*P i*Q j else 0 := by
      refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
      by_cases d : q∣u i ∧ q∣v j
      · rw [ite_eq_left d]
        by_cases g : gate i j
        · have ok : gate i j ∧ q∣u i ∧ q∣v j := ⟨g,d⟩
          rw [ite_eq_left ok,norm_mul,norm_mul]
          refine (mul_le_mul_of_nonneg_left (norm_overlap_mass_le (mem_Icc.mp (uSteps i hi)).1
            (uEnds i hi)) (by positivity)).trans_eq ?_
          unfold P Q
          ring
        · have bad : ¬(gate i j ∧ q∣u i ∧ q∣v j) := fun yes => g yes.1
          rw [ite_eq_right bad,norm_zero]
          unfold P Q
          positivity
      · simp only [ite_eq_right (fun yes : gate i j ∧ q∣u i ∧ q∣v j => d yes.2),
          ite_eq_right d,norm_zero,le_rfl]
    _ = (n : ℝ)*((∑ i ∈ I',P i)*(∑ j ∈ J',Q j)) := by
      rw [sum_mul_sum,mul_sum]
      simp only [I',J',sum_filter]
      refine sum_congr rfl fun i _ => ?_
      by_cases h : q∣u i
      · simp only [h,true_and,ite_true,mul_sum]
        refine sum_congr rfl fun j _ => ?_
        by_cases h' : q∣v j <;> simp [h',mul_assoc]
      · simp [h]
    _ ≤ (n : ℝ)*(K*K) := mul_le_mul_of_nonneg_left
      (mul_le_mul capU capV (by unfold Q; positivity) K0) (Nat.cast_nonneg _)
    _ = _ := by unfold K; ring

theorem norm_full_common_average_truncation_le {n A B : ℕ} (hn : 0 < n) (Bpos : 1 ≤ B) (Bn : B ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    {W : ℝ} (W0 : 0 ≤ W) (Apos : 0 < A)
    (uSteps : ∀ i ∈ I, u i ∈ Icc 1 A) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 A)
    (uEnds : ∀ i ∈ I, r i ≤ n/u i)
    (uWeights : ∀ x ∈ Icc 1 A, (∑ i ∈ I.filter (fun i => u i=x), ‖a i‖) ≤ W)
    (vWeights : ∀ x ∈ Icc 1 A, (∑ j ∈ J.filter (fun j => v j=x), ‖b j‖) ≤ W) :
    ‖fullCommonAverageFamily n B I J u l r v p s a b gate -
      fullCommonAverageFamily n n I J u l r v p s a b gate‖ ≤
    (n : ℝ)*(W*(1+Real.log (A : ℝ)))^2*(n.divisors.card : ℝ)*(2/(B : ℝ)) := by
  let S := Icc 1 B
  let T := Icc (B+1) n
  let F (q : ℕ) := standardRamanujan q (-(n : ℤ)) *
    ∫ t : ℝ,phase (((-(n : ℤ)) : ℝ)*t)*averagePairShell q I J u l r v p s a b gate t
  let C := (n : ℝ)*(W*(1+Real.log (A : ℝ)))^2
  have parts : Icc 1 n = S ∪ T := by
    ext q
    simp only [S,T,mem_Icc,mem_union]
    omega
  have apart : Disjoint S T := by
    rw [disjoint_left]
    intro q h1 h2
    have q1 := (mem_Icc.mp h1).2
    have q2 := (mem_Icc.mp h2).1
    omega
  change ‖(∑ q ∈ S,F q)-(∑ q ∈ Icc 1 n,F q)‖ ≤ _
  rw [parts,sum_union apart,sub_add_cancel_left,norm_neg]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ q ∈ T,C*(‖ramanujan q (-(n : ℤ))‖/(q : ℝ)^2) := by
      refine sum_le_sum fun q hq => ?_
      have q1 : 1 < q := Bpos.trans_lt (mem_Icc.mp hq).1
      have qpos := zero_lt_one.trans q1
      unfold F
      rw [norm_mul,standardRamanujan,ite_eq_right q1.ne']
      exact (mul_le_mul_of_nonneg_left
        (norm_full_common_average_shell_le n A q qpos I J u l r v p s a b gate W0 Apos
          uSteps vSteps uEnds uWeights vWeights) (norm_nonneg _)).trans_eq (by unfold C; ring)
    _ ≤ _ := by
      rw [← mul_sum]
      exact (mul_le_mul_of_nonneg_left (ramanujan_inverse_square_tail n B n hn Bpos) (by unfold C; positivity)).trans_eq
        (by unfold C; ring)

end

end B13NondividingResidueReductionProof

end

/- Integer volume rounding -/
section

namespace B13NondividingResidueReductionProof

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

end B13NondividingResidueReductionProof

end

/- Volume rounding family -/
section

namespace B13NondividingResidueReductionProof

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

end B13NondividingResidueReductionProof

end

/- Medium exact partition -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Scale
open scoped Classical

noncomputable section

def prefixStepGate (n u v : ℕ) : Prop :=
  maximumStep n^2 < u*v ∧ u.gcd v ≤ maximumStep n

instance (n u v : ℕ) : Decidable (prefixStepGate n u v) :=
  inferInstanceAs (Decidable (maximumStep n^2 < u*v ∧ u.gcd v ≤ maximumStep n))

private def prefixPairFamily (n : ℕ) {ι : Type} (I : Finset (ℕ × ℕ)) (J : Finset ι)
    (v p s : ι → ℕ) (w : ι → ℂ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if prefixStepGate n (leftBilinearStep i) (v j) then
    leftBilinearWeight n i*w j*f n (leftBilinearStep i) (v j) 0 (n/leftBilinearStep i) (p j) (s j)
  else 0

private def nondividingLowItems (n : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n)

private theorem nondividing_eq_residue_sums (n : ℕ) :
    bilateralNondividingResidueRemainder n =
      prefixPairFamily n (bilateralLeftWaveItems n) (nondividingLowItems n)
        rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight residueWindowPair +
      prefixPairFamily n (bilateralLeftWaveItems n) (rightHighWaveItems n)
        rightHighWaveStep (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)
        residueWindowPair := by
  let G (J : Finset RightLowWaveIndex) := prefixPairFamily n (bilateralLeftWaveItems n) J
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight residueWindowPair
  let V := prefixPairFamily n (bilateralLeftWaveItems n) (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n) residueWindowPair
  let D := (rightLowWaveItems n).filter (fun j => j.1 ∣ n)
  have cut : cutWaveFamily n (bilateralLeftWaveItems n) D leftBilinearStep (fun _ => 0)
      (fun i => n/leftBilinearStep i) rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n)
      (leftBilinearWeight n) rightLowWaveWeight = G D := by
    unfold cutWaveFamily G prefixPairFamily prefixStepGate
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    have u0 := (mem_Icc.mp (bilateral_left_step_range hi)).1
    have v0 := (mem_Icc.mp (bilateral_right_low_step_range (mem_filter.mp hj).1)).1
    rw [deep_wave_pair_eq_residue_window u0 v0]
    rfl
  have split : G (rightLowWaveItems n) = G D + G (nondividingLowItems n) := by
    unfold G prefixPairFamily D nondividingLowItems
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    exact (sum_filter_add_sum_filter_not _ _ _).symm
  change G (rightLowWaveItems n) + V -
    cutWaveFamily n (bilateralLeftWaveItems n) D leftBilinearStep (fun _ => 0)
      (fun i => n/leftBilinearStep i) rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n)
      (leftBilinearWeight n) rightLowWaveWeight = G (nondividingLowItems n) + V
  rw [cut,split]
  abel

theorem bilateral_nondividing_eq_prefix_pair_sums (n : ℕ) :
    bilateralNondividingResidueRemainder n =
      (∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ (rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n),
        let u := leftBilinearStep i
        let v := rightLowWaveStep j
        if prefixStepGate n u v then
          leftBilinearWeight n i*rightLowWaveWeight j*
            residueWindowPair n u v 0 (n/u) 0 (rightLowWaveUpper n j)
        else 0) +
      (∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ rightHighWaveItems n,
        let u := leftBilinearStep i
        let v := rightHighWaveStep j
        if prefixStepGate n u v then
          leftBilinearWeight n i*rightHighWaveWeight n j*
            residueWindowPair n u v 0 (n/u) (rightHighWaveLower n j) (n/v)
        else 0) :=
  nondividing_eq_residue_sums n

end

end B13NondividingResidueReductionProof

end

/- Extended wide volume -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def prefixVolumeFamily (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if gate i j then a i*b j*(pairVolume n (u i) (v j) (l i) (r i) (p j) (s j) : ℂ) else 0

theorem prefix_volume_family_eq_singular_add_rounding (n : ℕ) {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop) :
    prefixVolumeFamily n I J u l r v p s a b gate =
      singularOverlapFamily n I J u l r v p s a b gate + volumeRoundingFamily n I J u l r v p s a b gate := by
  unfold prefixVolumeFamily singularOverlapFamily volumeRoundingFamily
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases hg : gate i j
  · by_cases hd : (u i).gcd (v j) ∣ n
    · simp only [hg,hd,and_self,ite_true]
      ring
    · simp [hg,hd,pairVolume]
  · simp [hg]

end

end B13NondividingResidueReductionProof

end

/- Extended residue layer -/
section

namespace B13NondividingResidueReductionProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def outsideStepCap (A u v : ℕ) : Prop := ¬(u ≤ A ∧ v ≤ A)

end

end B13NondividingResidueReductionProof

end

/- Expanded wide approx -/
section

namespace B13NondividingResidueReductionProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def expandedWideStepCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(511/768 : ℝ)⌋₊

theorem expanded_wide_step_pos {n : ℕ} (hn : 0 < n) : 0 < expandedWideStepCap n :=
  Nat.le_floor (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))

theorem expanded_wide_step_le {n : ℕ} (hn : 0 < n) : expandedWideStepCap n ≤ n :=
  Nat.floor_le_of_le (Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num))

theorem eventually_expanded_wide_displacement :
    ∀ᶠ n : ℕ in atTop, 2*cutoffH n*expandedWideStepCap n ≤ n := by
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-(1/768-1/2048) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/768-1/2048)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2, eventually_log_budget_le_power (1/4096) (by norm_num),
    limit.eventually_lt_const (show (0 : ℝ) < 1/8192 by norm_num)] with n hn logBound small
  have nPos : 0 < n := by omega
  have nr : (0 : ℝ) < n := by exact_mod_cast nPos
  have A : (expandedWideStepCap n : ℝ) ≤ (n : ℝ)^(511/768 : ℝ) := Nat.floor_le (by positivity)
  have P : (n : ℝ)^(1/3 : ℝ)*((n : ℝ)^(1/4096 : ℝ))^2*(n : ℝ)^(511/768 : ℝ) =
    (n : ℝ)^(-(1/768-1/2048) : ℝ)*(n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le, ← Real.rpow_add nr, ← Real.rpow_add nr]
    calc
      _ = (n : ℝ)^(-(1/768-1/2048)+1 : ℝ) := by congr 1; norm_num
      _ = (n : ℝ)^(-(1/768-1/2048) : ℝ)*(n : ℝ)^(1 : ℝ) := Real.rpow_add nr _ _
      _ = _ := by rw [Real.rpow_one]
  have L0 := zero_le_one.trans (one_le_logBudget n)
  have top : 2*(cutoffH n : ℝ)*(expandedWideStepCap n : ℝ) ≤ (n : ℝ) := by
    calc
      _ ≤ 2*(4096*(n : ℝ)^(1/3 : ℝ)*logBudget n^2)*(n : ℝ)^(511/768 : ℝ) := by
        have hb := cutoff_h_le_power_log hn
        gcongr
      _ ≤ 2*(4096*(n : ℝ)^(1/3 : ℝ)*((n : ℝ)^(1/4096 : ℝ))^2)*(n : ℝ)^(511/768 : ℝ) := by
        gcongr
      _ = (8192*(n : ℝ)^(-(1/768-1/2048) : ℝ))*(n : ℝ) := by linear_combination 8192*P
      _ ≤ _ := by
        have h : 8192*(n : ℝ)^(-(1/768-1/2048) : ℝ) ≤ 1 := by linarith only [small]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right h nr.le
  exact_mod_cast top

theorem norm_expanded_noncommon_wide_le (n : ℕ) (hn : 2 ≤ n)
    (small : 2*cutoffH n*expandedWideStepCap n ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (c : α → ℂ) (d : β → ℂ) (gate : α → β → Prop)
    {T : ℝ} (T1 : 1 ≤ T)
    (uSteps : ∀ i ∈ I, u i ∈ Icc 1 (expandedWideStepCap n)) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 (expandedWideStepCap n))
    (uEnds : ∀ i ∈ I, r i ≤ n/u i) (vEnds : ∀ j ∈ J, s j ≤ n/v j)
    (uWeights : ∀ x ∈ Icc 1 (expandedWideStepCap n), (∑ i ∈ I.filter (fun i => u i = x), ‖c i‖) ≤ T^3*logBudget n)
    (vWeights : ∀ x ∈ Icc 1 (expandedWideStepCap n), (∑ j ∈ J.filter (fun j => v j = x), ‖d j‖) ≤ T^3*logBudget n) :
    ‖noncommonWideFamily n (cutoffB n) (cutoffH n) I J u l r v p s c d gate‖ ≤
      393216*(n : ℝ)^(767/768 : ℝ)*T^6*logBudget n^7 := by
  have nPos : 0 < n := by omega
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast nPos
  have nr := zero_lt_one.trans_le n1
  let W := T^3*logBudget n
  let L := logBudget n
  let B : ℝ := cutoffB n
  let H : ℝ := cutoffH n
  let X : ℝ := (expandedWideStepCap n : ℝ)+B
  have L1 := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have W0 : 0 ≤ W := mul_nonneg (pow_nonneg (zero_le_one.trans T1) _) L0
  have Bn : cutoffB n ≤ n := (cutoffs_ordered n nPos).2.2.1.trans (cutoffs_ordered n nPos).2.2.2
  have Br : B ≤ (n : ℝ)^(1/3 : ℝ) := Nat.floor_le (by positivity)
  have Hr : H ≤ 4096*(n : ℝ)^(1/3 : ℝ)*L^2 := cutoff_h_le_power_log hn
  have Xr : X ≤ 2*(n : ℝ)^(511/768 : ℝ) := by
    have a : (expandedWideStepCap n : ℝ) ≤ (n : ℝ)^(511/768 : ℝ) := Nat.floor_le (by positivity)
    have b := Br.trans (Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : (1:ℝ)/3≤511/768))
    unfold X
    linarith only [a,b]
  have Blog : 1+Real.log B ≤ L := by
    have bp : (0 : ℝ) < B := by
      unfold B
      exact_mod_cast (show 0 < cutoffB n from (cutoffs_ordered n nPos).1.trans (cutoffs_ordered n nPos).2.1)
    have upper : B ≤ (n : ℝ)+2 := by
      have le : (cutoffB n : ℝ) ≤ n := by exact_mod_cast Bn
      unfold B
      linarith only [le]
    unfold L logBudget
    linarith only [Real.log_le_log bp upper]
  have one : H*B*X^2/n ≤ 16384*(n : ℝ)^(767/768 : ℝ)*L^3 := by
    calc
      _ ≤ (4096*(n : ℝ)^(1/3 : ℝ)*L^2)*(n : ℝ)^(1/3 : ℝ)*(2*(n : ℝ)^(511/768 : ℝ))^2/n := by gcongr
      _ = 16384*(n : ℝ)^(383/384 : ℝ)*L^2 := by
        have exp : (n : ℝ)^(1/3 : ℝ)*(n : ℝ)^(1/3 : ℝ)*((n : ℝ)^(511/768 : ℝ))^2 =
            (n : ℝ)^(383/384 : ℝ)*(n : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul nr.le, ← Real.rpow_add nr, ← Real.rpow_add nr]
          calc
            _ = (n : ℝ)^(383/384+1 : ℝ) := by congr 1; norm_num
            _ = (n : ℝ)^(383/384 : ℝ)*(n : ℝ)^(1 : ℝ) := Real.rpow_add nr _ _
            _ = _ := by rw [Real.rpow_one]
        apply (div_eq_iff nr.ne').mpr
        linear_combination 16384*L^2*exp
      _ ≤ _ := by
        have a := Real.rpow_le_rpow_of_exponent_le n1 (show (383/384:ℝ) ≤ 767/768 by norm_num)
        have b : L^2 ≤ L^3 := pow_le_pow_right₀ L1 (by decide)
        gcongr
  have two : H*X*(1+Real.log B) ≤ 8192*(n : ℝ)^(767/768 : ℝ)*L^3 := by
    calc
      _ ≤ (4096*(n : ℝ)^(1/3 : ℝ)*L^2)*(2*(n : ℝ)^(511/768 : ℝ))*L := by gcongr
      _ = _ := by
        have exp : (n : ℝ)^(1/3 : ℝ)*(n : ℝ)^(511/768 : ℝ) = (n : ℝ)^(767/768 : ℝ) := by
          rw [← Real.rpow_add nr]
          norm_num
        linear_combination 8192*L^3*exp
  refine (norm_noncommon_wide_family_le n (expandedWideStepCap n) (cutoffB n) (cutoffH n)
    nPos (expanded_wide_step_pos nPos) (expanded_wide_step_le nPos) Bn small
    I J u l r v p s c d gate W0 uSteps vSteps uEnds vEnds uWeights vWeights).trans ?_
  change 16*W^2*L^2*(H*B*X^2/n+H*X*(1+Real.log B)) ≤ _
  refine (mul_le_mul_of_nonneg_left (add_le_add one two) (by positivity)).trans_eq ?_
  unfold W L
  ring

theorem norm_expanded_wide_sub_average_le {n : ℕ} (hn : 2 ≤ n)
    (thin : 4*cutoffH n*cutoffB n ≤ n)
    (small : 2*cutoffH n*expandedWideStepCap n ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (c : α → ℂ) (d : β → ℂ) (gate : α → β → Prop)
    {T : ℝ} (T1 : 1 ≤ T)
    (uSteps : ∀ i ∈ I, u i ∈ Icc 1 (expandedWideStepCap n)) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 (expandedWideStepCap n))
    (uEnds : ∀ i ∈ I, r i ≤ n/u i) (vEnds : ∀ j ∈ J, s j ≤ n/v j)
    (uWeights : ∀ x ∈ Icc 1 (expandedWideStepCap n), (∑ i ∈ I.filter (fun i => u i = x), ‖c i‖) ≤ T^3*logBudget n)
    (vWeights : ∀ x ∈ Icc 1 (expandedWideStepCap n), (∑ j ∈ J.filter (fun j => v j = x), ‖d j‖) ≤ T^3*logBudget n) :
    ‖wideWaveFamily n (cutoffB n) (cutoffH n) I J u l r v p s c d gate -
      commonAverageWideFamily n (cutoffB n) (cutoffH n) I J u l r v p s c d gate‖ ≤
        917504*(n : ℝ)^(767/768 : ℝ)*T^6*logBudget n^7 := by
  let A := expandedWideStepCap n
  let L := logBudget n
  let B := cutoffB n
  let H := cutoffH n
  let W := T^3*L
  have L1 := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have W0 : 0 ≤ W := mul_nonneg (pow_nonneg (zero_le_one.trans T1) _) L0
  have n0 : 0 < n := by omega
  have np : (0 : ℝ) < n := by exact_mod_cast n0
  have A0 := expanded_wide_step_pos n0
  have Apos : (0 : ℝ) < A := by exact_mod_cast A0
  have An : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast expanded_wide_step_le n0
  have logA : 1+Real.log A ≤ L := by
    unfold L logBudget
    linarith only [Real.log_le_log Apos (show (A : ℝ) ≤ (n : ℝ)+2 by linarith)]
  have Apow : (A : ℝ) ≤ (n : ℝ)^(511/768 : ℝ) := Nat.floor_le (by positivity)
  have Hpow : (H : ℝ) ≤ 4096*(n : ℝ)^(1/3 : ℝ)*L^2 := cutoff_h_le_power_log hn
  have common := norm_common_wide_family_sub_average_le n A B H n0 A0 small
    I J u l r v p s c d gate W0 uSteps vSteps uEnds vEnds uWeights vWeights
  have normCommon :
      ‖commonWideFamily n B H I J u l r v p s c d gate -
        commonAverageWideFamily n B H I J u l r v p s c d gate‖ ≤
      524288*(n : ℝ)^(767/768 : ℝ)*T^6*L^7 := by
    refine common.trans ?_
    have powers : (n : ℝ)^(1/3 : ℝ)*(n : ℝ)^(511/768 : ℝ)=(n : ℝ)^(767/768 : ℝ) := by
      rw [← Real.rpow_add np]
      norm_num
    have log0 : 0 ≤ 1+Real.log (A : ℝ) := add_nonneg zero_le_one
      (Real.log_nonneg (by exact_mod_cast A0))
    calc
      _ ≤ 128*W^2*(4096*(n : ℝ)^(1/3 : ℝ)*L^2)*((n : ℝ)^(511/768 : ℝ))*L := by gcongr
      _ = 524288*(n : ℝ)^(767/768 : ℝ)*T^6*L^5 := by
        unfold W
        linear_combination 524288*T^6*L^5*powers
      _ ≤ _ := by
        have h : L^5 ≤ L^7 := pow_le_pow_right₀ L1 (by decide)
        gcongr
  have nc := norm_expanded_noncommon_wide_le n hn small I J u l r v p s c d gate T1
    uSteps vSteps uEnds vEnds uWeights vWeights
  rw [wide_wave_family_eq_partition n0 thin,add_sub_right_comm]
  exact (norm_add_le _ _).trans ((add_le_add normCommon nc).trans_eq (by ring))

end

end B13NondividingResidueReductionProof

end

/- Expanded wide volume -/
section

namespace B13NondividingResidueReductionProof

open Finset
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

theorem norm_expanded_average_sub_overlap_le {n : ℕ} (n0 : 0 < n)
    (thin : 4*cutoffH n*cutoffB n ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    {T : ℝ} (T1 : 1 ≤ T) (divN : (n.divisors.card : ℝ) ≤ T)
    (uSteps : ∀ i ∈ I, u i ∈ Icc 1 (expandedWideStepCap n)) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 (expandedWideStepCap n))
    (uEnds : ∀ i ∈ I, r i ≤ n/u i)
    (uWeights : ∀ x ∈ Icc 1 (expandedWideStepCap n), (∑ i ∈ I.filter (fun i => u i = x), ‖a i‖) ≤ T^3*logBudget n)
    (vWeights : ∀ x ∈ Icc 1 (expandedWideStepCap n), (∑ j ∈ J.filter (fun j => v j = x), ‖b j‖) ≤ T^3*logBudget n) :
    ‖commonAverageWideFamily n (cutoffB n) (cutoffH n) I J u l r v p s a b gate -
       singularOverlapFamily n I J u l r v p s a b gate‖ ≤
      8*(n : ℝ)^(2/3 : ℝ)*T^7*logBudget n^5 := by
  let A := expandedWideStepCap n
  let B := cutoffB n
  let H := cutoffH n
  let L := logBudget n
  let W := T^3*L
  have L1 := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have W0 : 0 ≤ W := mul_nonneg (pow_nonneg (zero_le_one.trans T1) _) L0
  obtain ⟨rPos,rB,bM,mN⟩ := cutoffs_ordered n n0
  have Bpos : 1 ≤ B := rPos.trans rB
  have Bn : B ≤ n := bM.trans mN
  have BposR : (0 : ℝ) < B := by
    exact_mod_cast Bpos
  have Apos : 0 < A := expanded_wide_step_pos n0
  have An : A ≤ n := expanded_wide_step_le n0
  have HB : B ≤ H := by
    unfold B H cutoffH
    have log1 : 1 ≤ Nat.log 2 (n+2) := Nat.log_pos (by decide) (by omega)
    simpa only [mul_one] using Nat.mul_le_mul (show cutoffB n ≤ 256*cutoffB n by omega) (one_le_pow₀ log1 (n := 2))
  have Hpos : 0 < H := Bpos.trans HB
  have nr : (0 : ℝ) < n := by exact_mod_cast n0
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast n0
  have hrb : (B : ℝ) ≤ (H : ℝ) := by exact_mod_cast HB
  have upper (x : ℕ) (xp : 0 < x) (xn : x ≤ n) : 1+Real.log (x : ℝ) ≤ L := by
    have le : (x : ℝ) ≤ n := by exact_mod_cast xn
    unfold L logBudget
    linarith only [Real.log_le_log (by exact_mod_cast xp : (0 : ℝ) < x) (show
      (x : ℝ) ≤ (n : ℝ)+2 by linarith only [le])]
  have logA := upper A Apos An
  have logB := upper B Bpos Bn
  have a0 : 0 ≤ 1+Real.log (A : ℝ) := add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast Apos))
  have b0 : 0 ≤ 1+Real.log (B : ℝ) := add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast Bpos))
  have nOverB : (n : ℝ)/B ≤ 2*(n : ℝ)^(2/3 : ℝ) := by
    have bLower : (n : ℝ)^(1/3 : ℝ)/2 ≤ (B : ℝ) := floor_half_le (Real.one_le_rpow n1 (by norm_num))
    apply (div_le_iff₀ BposR).mpr
    calc
      (n : ℝ) = (n : ℝ)^(2/3 : ℝ)*(n : ℝ)^(1/3 : ℝ) := by rw [← Real.rpow_add nr]; norm_num
      _ = (2*(n : ℝ)^(2/3 : ℝ))*((n : ℝ)^(1/3 : ℝ)/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left bLower (by positivity)
  have nOverH : (n : ℝ)/H ≤ 2*(n : ℝ)^(2/3 : ℝ) :=
    (div_le_div_of_nonneg_left nr.le BposR hrb).trans nOverB
  have averageTail := norm_common_average_wide_tail_le n A B H n0 Hpos Apos thin
    I J u l r v p s a b gate W0 uSteps vSteps uWeights vWeights
  have cutTail := norm_full_common_average_truncation_le n0 Bpos Bn
    I J u l r v p s a b gate W0 Apos uSteps vSteps uEnds uWeights vWeights
  have exactOverlap := full_common_average_eq_singular_overlap n I J u l r v p s a b gate
      (fun i hi => Icc_subset_Icc_right An (uSteps i hi)) (fun j hj => Icc_subset_Icc_right An (vSteps j hj))
  have average : ‖commonAverageWideFamily n B H I J u l r v p s a b gate -
      fullCommonAverageFamily n B I J u l r v p s a b gate‖ ≤ 4*(n : ℝ)^(2/3 : ℝ)*T^7*L^5 := by
    refine averageTail.trans ?_
    calc
      _ ≤ 2*(W*L)^2*(2*(n : ℝ)^(2/3 : ℝ))*T*L := by gcongr
      _ = _ := by unfold W; ring
  have finite : ‖fullCommonAverageFamily n B I J u l r v p s a b gate -
      fullCommonAverageFamily n n I J u l r v p s a b gate‖ ≤ 4*(n : ℝ)^(2/3 : ℝ)*T^7*L^5 := by
    refine cutTail.trans ?_
    calc
      _ = 2*(W*(1+Real.log (A : ℝ)))^2*((n : ℝ)/B)*(n.divisors.card : ℝ) := by ring
      _ ≤ 2*(W*L)^2*(2*(n : ℝ)^(2/3 : ℝ))*(T*L) := by
        have ext : (n.divisors.card : ℝ) ≤ T*L := divN.trans (le_mul_of_one_le_right (zero_le_one.trans T1) L1)
        gcongr
      _ = _ := by unfold W; ring
  rw [← exactOverlap,← sub_add_sub_cancel
    (commonAverageWideFamily n B H I J u l r v p s a b gate)
    (fullCommonAverageFamily n B I J u l r v p s a b gate)
    (fullCommonAverageFamily n n I J u l r v p s a b gate)]
  exact (norm_add_le _ _).trans ((add_le_add average finite).trans_eq (by ring))

theorem norm_expanded_volume_sub_wide_le {n : ℕ} (hn : 2 ≤ n)
    (thin : 4*cutoffH n*cutoffB n ≤ n) (small : 2*cutoffH n*expandedWideStepCap n ≤ n)
    {α β : Type*} (I : Finset α) (J : Finset β)
    (u l r : α → ℕ) (v p s : β → ℕ) (a : α → ℂ) (b : β → ℂ) (gate : α → β → Prop)
    {T : ℝ} (T1 : 1 ≤ T) (divN : (n.divisors.card : ℝ) ≤ T)
    (uSteps : ∀ i ∈ I, u i ∈ Icc 1 (expandedWideStepCap n)) (vSteps : ∀ j ∈ J, v j ∈ Icc 1 (expandedWideStepCap n))
    (uEnds : ∀ i ∈ I, r i ≤ n/u i) (vEnds : ∀ j ∈ J, s j ≤ n/v j)
    (uWeights : ∀ x ∈ Icc 1 (expandedWideStepCap n), (∑ i ∈ I.filter (fun i => u i = x), ‖a i‖) ≤ T^3*logBudget n)
    (vWeights : ∀ x ∈ Icc 1 (expandedWideStepCap n), (∑ j ∈ J.filter (fun j => v j = x), ‖b j‖) ≤ T^3*logBudget n) :
    ‖prefixVolumeFamily n I J u l r v p s a b gate -
       wideWaveFamily n (cutoffB n) (cutoffH n) I J u l r v p s a b gate‖ ≤
      917524*(n : ℝ)^(767/768 : ℝ)*T^7*logBudget n^7 := by
  let A := expandedWideStepCap n
  let L := logBudget n
  let W := T^3*L
  let V := prefixVolumeFamily n I J u l r v p s a b gate
  let R := volumeRoundingFamily n I J u l r v p s a b gate
  let S := singularOverlapFamily n I J u l r v p s a b gate
  let C := commonAverageWideFamily n (cutoffB n) (cutoffH n) I J u l r v p s a b gate
  let H := wideWaveFamily n (cutoffB n) (cutoffH n) I J u l r v p s a b gate
  have n0 : 0 < n := by omega
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast n0
  have A0 := expanded_wide_step_pos n0
  have L1 := one_le_logBudget n
  have W0 : 0 ≤ W := mul_nonneg (pow_nonneg (zero_le_one.trans T1) _) (zero_le_one.trans L1)
  have ar : (A : ℝ) ≤ (n : ℝ)^(511/768 : ℝ) := Nat.floor_le (by positivity)
  have logA : 1+Real.log A ≤ L := by
    have An : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast expanded_wide_step_le n0
    have Apos : (0 : ℝ) < A := by exact_mod_cast A0
    unfold L logBudget
    linarith only [Real.log_le_log Apos (show (A : ℝ) ≤ (n : ℝ)+2 by linarith)]
  have logA0 : 0 ≤ 1+Real.log A := add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast A0))
  have round : ‖R‖ ≤ 12*(n : ℝ)^(511/768 : ℝ)*T^7*L^3 := by
    refine (norm_volume_rounding_family_le n A n0 A0 I J u l r v p s a b gate
      W0 uSteps vSteps uWeights vWeights).trans ?_
    calc
      _ ≤ 12*W^2*(n : ℝ)^(511/768 : ℝ)*L*T := by gcongr
      _ = _ := by unfold W; ring
  have average := norm_expanded_average_sub_overlap_le n0 thin I J u l r v p s a b gate
    T1 divN uSteps vSteps uEnds uWeights vWeights
  have wide := norm_expanded_wide_sub_average_le hn thin small I J u l r v p s a b gate
    T1 uSteps vSteps uEnds vEnds uWeights vWeights
  have eq : V-H = R + ((S-C)+(C-H)) := by
    unfold V
    rw [prefix_volume_family_eq_singular_add_rounding]
    change S+R-H=_
    abel
  change ‖V-H‖ ≤ 917524*(n : ℝ)^(767/768 : ℝ)*T^7*L^7
  rw [eq]
  have av : ‖S-C‖ ≤ 8*(n : ℝ)^(2/3 : ℝ)*T^7*L^5 := by
    rw [norm_sub_rev]
    exact average
  have wi : ‖C-H‖ ≤ 917504*(n : ℝ)^(767/768 : ℝ)*T^6*L^7 := by
    rw [norm_sub_rev]
    exact wide
  refine (norm_add_le _ _).trans ((add_le_add round ((norm_add_le _ _).trans (add_le_add av wi))).trans ?_)
  have r1 := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : (511/768 : ℝ) ≤ 767/768)
  have r2 := Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : (2/3 : ℝ) ≤ 767/768)
  have l₃ : L^3 ≤ L^7 := pow_le_pow_right₀ L1 (by decide)
  have l₅ : L^5 ≤ L^7 := pow_le_pow_right₀ L1 (by decide)
  have t : T^6 ≤ T^7 := pow_le_pow_right₀ T1 (by decide)
  calc
    _ ≤ 12*(n : ℝ)^(767/768 : ℝ)*T^7*L^7 +
        (8*(n : ℝ)^(767/768 : ℝ)*T^7*L^7+917504*(n : ℝ)^(767/768 : ℝ)*T^7*L^7) := by gcongr
    _ = _ := by ring

end

end B13NondividingResidueReductionProof

end

/- Expanded residue layer -/
section

namespace B13NondividingResidueReductionProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical

noncomputable section

def expandedWaveItems (n : ℕ) {α : Type*} (I : Finset α) (u : α → ℕ) : Finset α :=
  I.filter fun i => u i ≤ expandedWideStepCap n

private def expandedLeftToRightPairSum (n : ℕ) {κ : Type} (I : Finset (ℕ × ℕ)) (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) (gate : ℕ → ℕ → Prop)
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ i ∈ I, ∑ j ∈ J, if gate (leftBilinearStep i) (v j) then
    leftBilinearWeight n i*w j*f (leftBilinearStep i) (v j) 0 (n/leftBilinearStep i) (p j) (s j)
  else 0

private def expandedOutsideStepPairSum (n A : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) : ℂ :=
  expandedLeftToRightPairSum n (bilateralLeftWaveItems n) J v p s w
    (fun u v => prefixStepGate n u v ∧ outsideStepCap A u v) (residueWindowPair n)

def arithmeticOutsideExpanded (n : ℕ) : ℂ :=
  expandedOutsideStepPairSum n (expandedWideStepCap n) ((rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n))
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight +
  expandedOutsideStepPairSum n (expandedWideStepCap n) (rightHighWaveItems n) rightHighWaveStep (rightHighWaveLower n)
    (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)

end

end B13NondividingResidueReductionProof

end

/- Raw expanded reduction -/
section

namespace B13NondividingResidueReductionProof

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

private def rawVolumeMinusWide (n u v l r p s : ℕ) : ℂ :=
  (pairVolume n u v l r p s : ℂ) - productStepWideIntegral n u v l r p s

def rawExpandedVolumeCorrectionFrom (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) : ℂ :=
  let I := expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep
  let R := expandedWaveItems n J v
  let gate (i : ℕ × ℕ) (j : κ) := prefixStepGate n (leftBilinearStep i) (v j)
  prefixVolumeFamily n I R leftBilinearStep (fun _ => 0) (fun i => n/leftBilinearStep i)
    v p s (leftBilinearWeight n) w gate -
  wideWaveFamily n (cutoffB n) (cutoffH n) I R leftBilinearStep (fun _ => 0)
    (fun i => n/leftBilinearStep i) v p s (leftBilinearWeight n) w gate

def rawExpandedVolumeCorrection (n : ℕ) : ℂ :=
  rawExpandedVolumeCorrectionFrom n ((rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n))
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight +
  rawExpandedVolumeCorrectionFrom n (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)

def rawExpandedResidue (n : ℕ) : ℂ :=
  rawExpandedWavePairSum n ((rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n))
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight
    (fun u v l r a b => (pairResidueError n u v l r a b : ℂ)) +
  rawExpandedWavePairSum n (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)
    (fun u v l r a b => (pairResidueError n u v l r a b : ℂ))

private theorem raw_expanded_correction_eq_wave_pair (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) :
    rawExpandedVolumeCorrectionFrom n J v p s w =
      rawExpandedWavePairSum n J v p s w (rawVolumeMinusWide n) := by
  unfold rawExpandedVolumeCorrectionFrom rawExpandedWavePairSum rawWavePairSum prefixVolumeFamily
  dsimp only
  rw [wide_wave_family_eq_pair_sum]
  simp only [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases h : prefixStepGate n (leftBilinearStep i) (v j) <;> simp [h,rawVolumeMinusWide,mul_sub]

private theorem norm_raw_expanded_volume_correction_from_le {n : ℕ} (hn : 2 ≤ n)
    (thin : 4*cutoffH n*cutoffB n ≤ n) (small : 2*cutoffH n*expandedWideStepCap n ≤ n)
    {κ : Type} (J : Finset κ) (v p s : κ → ℕ) (w : κ → ℂ)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (steps : ∀ j ∈ J, v j ∈ Icc 1 n) (ends : ∀ j ∈ J, s j ≤ n/v j)
    (weights : ∀ m ∈ Icc 1 n, (∑ j ∈ J.filter (fun j => v j=m), ‖w j‖) ≤ T^3*logBudget n) :
    ‖rawExpandedVolumeCorrectionFrom n J v p s w‖ ≤ 917524*(n : ℝ)^(767/768 : ℝ)*T^7*logBudget n^7 := by
  let A := expandedWideStepCap n
  have n0 : 0 < n := by omega
  have An := expanded_wide_step_le n0
  have range {α : Type} {S : Finset α} {u : α → ℕ} (h : ∀ x ∈ S, u x ∈ Icc 1 n) (x : α)
      (hx : x ∈ expandedWaveItems n S u) : u x ∈ Icc 1 A := by
    obtain ⟨base,limit⟩ := mem_filter.mp hx
    exact mem_Icc.mpr ⟨(mem_Icc.mp (h x base)).1,limit⟩
  have bound {α : Type} {S : Finset α} {u : α → ℕ} {c : α → ℂ}
      (h : ∀ m ∈ Icc 1 n, (∑ i ∈ S.filter (fun i => u i=m), ‖c i‖) ≤ T^3*logBudget n)
      (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ i ∈ (expandedWaveItems n S u).filter (fun i => u i=m), ‖c i‖) ≤ T^3*logBudget n :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (h m (Icc_subset_Icc_right An hm))
  exact norm_expanded_volume_sub_wide_le hn thin small _ _ _ _ _ v p s _ w _ T1 (divisors n le_rfl)
    (range (fun _ h => bilateral_left_step_range h)) (range steps) (fun _ _ => le_rfl)
    (fun j hj => ends j (mem_filter.mp hj).1)
    (bound (norm_bilateral_left_step_mass n0 (zero_le_one.trans T1) divisors)) (bound weights)

theorem norm_raw_expanded_volume_correction_le {n : ℕ} (hn : 2 ≤ n)
    (thin : 4*cutoffH n*cutoffB n ≤ n) (small : 2*cutoffH n*expandedWideStepCap n ≤ n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖rawExpandedVolumeCorrection n‖ ≤ 1835048*(n : ℝ)^(767/768 : ℝ)*T^7*logBudget n^7 := by
  have low := norm_raw_expanded_volume_correction_from_le hn thin small
    ((rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n))
    rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight T1 divisors
    (fun _ h => bilateral_right_low_step_range (mem_filter.mp h).1) (fun _ _ => min_le_right _ _)
    (fun x hx => (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_right_low_step_mass T1 divisors x hx))
  have high := norm_raw_expanded_volume_correction_from_le hn thin small (rightHighWaveItems n)
    rightHighWaveStep (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)
    T1 divisors (fun _ h => bilateral_right_high_step_range h) (fun _ _ => le_rfl)
    (norm_bilateral_right_high_step_mass (zero_le_one.trans T1) divisors)
  exact (norm_add_le _ _).trans ((add_le_add low high).trans_eq (by ring))

theorem raw_expanded_volume_correction_saving : saving rawExpandedVolumeCorrection := by
  intro e he
  obtain ⟨D,D1,divBound⟩ := divisor_envelope_at_power 32768 (by decide)
  let C := 1835048*D^7
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-(1/768-14/32768) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/768-14/32768)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(1/768-14/32768) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have estimates : ∀ᶠ n : ℕ in atTop, ‖rawExpandedVolumeCorrection n‖ ≤ e*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2,eventually_small_width,eventually_expanded_wide_displacement,
      eventually_log_budget_le_power (1/32768) (by norm_num),scaled.eventually_lt_const he] with n hn width small logb final
    have n0 : 0 < n := by omega
    have nr : (0 : ℝ) < n := by exact_mod_cast n0
    have log0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/32768 : ℝ)
    let T := D*X
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1
      (Real.one_le_rpow (by exact_mod_cast n0) (by norm_num))
    have thin : 4*cutoffH n*cutoffB n ≤ n :=
      (Nat.mul_le_mul_left _ (cutoffs_ordered n n0).2.2.1).trans width
    have exp : (n : ℝ)^(767/768 : ℝ)*X^14 = (n : ℝ)^(-(1/768-14/32768) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast nr.le,← Real.rpow_add nr,← Real.rpow_add_one nr.ne']
      congr 1
      norm_num
    calc
      _ ≤ 1835048*(n : ℝ)^(767/768 : ℝ)*T^7*logBudget n^7 :=
        norm_raw_expanded_volume_correction_le hn thin small T1 (divBound n)
      _ ≤ 1835048*(n : ℝ)^(767/768 : ℝ)*T^7*X^7 := by
        gcongr
      _ = C*((n : ℝ)^(767/768 : ℝ)*X^14) := by unfold C T; ring
      _ = (C*(n : ℝ)^(-(1/768-14/32768) : ℝ))*(n : ℝ) := by rw [exp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right final.le nr.le
  obtain ⟨N,h⟩ := eventually_atTop.mp estimates
  exact ⟨N,fun n hn _ => h n hn⟩

private theorem raw_expanded_eq_full_pair_sum (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℂ) :
    rawExpandedWavePairSum n J v p s w f =
      rawWavePairSum n (bilateralLeftWaveItems n) J v p s w
        (fun u v => (u ≤ expandedWideStepCap n ∧ v ≤ expandedWideStepCap n) ∧ prefixStepGate n u v) f := by
  unfold rawExpandedWavePairSum rawWavePairSum expandedWaveItems
  rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : leftBilinearStep i ≤ expandedWideStepCap n
  · rw [ite_eq_left hi,sum_filter]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : v j ≤ expandedWideStepCap n <;> simp [hi,hj]
  · simp [hi]

private def rawOutsideExpandedFrom (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) : ℂ :=
  rawWavePairSum n (bilateralLeftWaveItems n) J v p s w
    (fun u v => prefixStepGate n u v ∧ outsideStepCap (expandedWideStepCap n) u v) (residueWindowPair n)

private theorem raw_expanded_wave_pair_split (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) :
    rawWavePairSum n (bilateralLeftWaveItems n) J v p s w (prefixStepGate n) (residueWindowPair n) =
      rawExpandedWavePairSum n J v p s w (fun u v l r a b => (pairResidueError n u v l r a b : ℂ)) +
      rawOutsideExpandedFrom n J v p s w + rawExpandedVolumeCorrectionFrom n J v p s w := by
  rw [raw_expanded_correction_eq_wave_pair,raw_expanded_eq_full_pair_sum,raw_expanded_eq_full_pair_sum]
  unfold rawOutsideExpandedFrom rawWavePairSum
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases g : prefixStepGate n (leftBilinearStep i) (v j)
  · by_cases mem : leftBilinearStep i ≤ expandedWideStepCap n ∧ v j ≤ expandedWideStepCap n
    · simp [g,mem,outsideStepCap,residueWindowPair,rawVolumeMinusWide,mul_add]
    · simp [g,mem,outsideStepCap]
  · simp [g]

private theorem raw_expanded_prefix_eq (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) :
    (∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ J,
      let u := leftBilinearStep i
      let m := v j
      if prefixStepGate n u m then
        leftBilinearWeight n i*w j*residueWindowPair n u m 0 (n/u) (p j) (s j)
      else 0) =
    rawWavePairSum n (bilateralLeftWaveItems n) J v p s w (prefixStepGate n) (residueWindowPair n) := by
  unfold rawWavePairSum
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases h : prefixStepGate n (leftBilinearStep i) (v j) <;> simp [h]

theorem raw_expanded_remainder_eq (n : ℕ) :
    bilateralNondividingResidueRemainder n =
      rawExpandedResidue n + arithmeticOutsideExpanded n + rawExpandedVolumeCorrection n := by
  rw [bilateral_nondividing_eq_prefix_pair_sums]
  let J := (rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n)
  rw [raw_expanded_prefix_eq,raw_expanded_prefix_eq]
  have outside : arithmeticOutsideExpanded n =
      rawOutsideExpandedFrom n J rightLowWaveStep (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight +
      rawOutsideExpandedFrom n (rightHighWaveItems n) rightHighWaveStep (rightHighWaveLower n)
        (fun i => n/rightHighWaveStep i) (rightHighWaveWeight n) := rfl
  rw [raw_expanded_wave_pair_split,raw_expanded_wave_pair_split,outside]
  unfold rawExpandedResidue rawExpandedVolumeCorrection J
  abel

theorem frozen_iff_raw_expanded_residue :
    frozenGoal ↔ saving (fun n => rawExpandedResidue n + arithmeticOutsideExpanded n) := by
  rw [frozen_iff_nondividing_residue]
  constructor <;> intro H e he <;>
    obtain ⟨N,h⟩ := H (e/2) (by positivity) <;>
    obtain ⟨M,hm⟩ := raw_expanded_volume_correction_saving (e/2) (by positivity) <;>
    refine ⟨max N M,fun n hn even => ?_⟩
  · have back : rawExpandedResidue n + arithmeticOutsideExpanded n =
        bilateralNondividingResidueRemainder n - rawExpandedVolumeCorrection n := by
      rw [raw_expanded_remainder_eq]
      abel
    dsimp only
    rw [back]
    exact (norm_sub_le _ _).trans (by linarith only [h n (by omega) even,hm n (by omega) even])
  · rw [raw_expanded_remainder_eq]
    exact (norm_add_le _ _).trans (by linarith only [h n (by omega) even,hm n (by omega) even])

end

end B13NondividingResidueReductionProof

end

/- Route residue -/
section

theorem Conjectures.Goldbach.B13NondividingResidueReduction :
let vaughanGoal : Prop :=
      let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
          let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
          let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
          let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
          let H := fun n : ℕ => 256 * Q₁ n * Q n
          let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
          let Λ := ArithmeticFunction.vonMangoldt
          let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
          let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊
          let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊
          let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
          let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊
          let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a)
          let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a)
          let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume
          let M := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
          let Z := (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
          let P := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 256 : ℝ)⌋₊
          let K := fun n : ℕ => ⌊(n : ℝ) ^ (33 / 64 : ℝ)⌋₊
          let truncate : ArithmeticFunction ℝ → ℕ → ArithmeticFunction ℝ := fun f H => ⟨fun m => if m ≤ H then f m else 0, by simp⟩
          let W := fun (n b : ℕ) => if K n < b then (((M - truncate M (P n)) * (Λ - truncate Λ (P n)) * Z : ArithmeticFunction ℝ) b) else Λ b
          let τremain₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * W n (m / a)
          let PL := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 96 : ℝ)⌋₊
          let WL := fun (n b : ℕ) => (((M - truncate M (PL n)) * (Λ - truncate Λ (PL n)) * Z : ArithmeticFunction ℝ) b)
          let τremain₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * WL n (m / a)
          let rightShift := fun (n : ℕ) (t : ℝ) => ∑ m ∈ Finset.range (n + 1), (τremain₃ n m : ℂ) * E ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)
          let residual := fun n : ℕ => intervalIntegral (fun x => (wideArcs n)ᶜ.indicator (fun t => rightShift n t * S n (τremain₁ n) t) x) (0 : ℝ) 1 MeasureTheory.volume
          (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖residual n‖ ≤ e * (n : ℝ))
    let residueGoal : Prop :=
      let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
          let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
          let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
          let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
          let H := fun n : ℕ => 256 * Q₁ n * Q n
          let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
          let Λ := ArithmeticFunction.vonMangoldt
          let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
          let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊
          let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊
          let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
          let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊
          let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a)
          let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a)
          let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume
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
          let geo := fun (g a b : ℕ) (t : ℝ) => ∑ s ∈ Finset.Ioc a b, E (((g * s : ℕ) : ℝ) * t)
          let integral := fun (n g h a b c d : ℕ) => (let e := g.gcd h; let A := max (a : ℤ) (((n : ℤ) - (h : ℤ)*d - 1)/(g : ℤ)); let B := min (b : ℤ) (((n : ℤ) - (h : ℤ)*((c : ℤ)+1))/(g : ℤ)); let m : ℤ := (h/e : ℕ); let z := ((n/e : ℕ) : ℤ) * Nat.gcdA (g/e) (h/e) % m; let volume : ℝ := if e ∣ n then ((max 0 (B-A) : ℤ) : ℝ)/((h/e : ℕ) : ℝ) else 0; let discrepancy : ℝ := if e ∣ n then (if A ≤ B then ((((A-z)%m : ℤ) : ℝ) - (((B-z)%m : ℤ) : ℝ))/(m : ℝ) else 0) else 0; (discrepancy : ℂ) + ((volume : ℂ) - (intervalIntegral (fun x => (wideArcs n).indicator (fun t => E (((-(n : ℤ)) : ℝ) * t) * (geo g a b t * geo h c d t)) x) (0 : ℝ) 1 MeasureTheory.volume)))
          let w := fun (n : ℕ) (i : ℕ × ℕ) => ((∑ d ∈ (Nat.divisors i.1).filter (fun d => U n < d), μ d : ℝ) : ℂ) * (F (PL n) i.2 : ℂ)
          let errorPart := fun (n g h a b c d : ℕ) => (let e := g.gcd h; let A := max (a : ℤ) (((n : ℤ) - (h : ℤ)*d - 1)/(g : ℤ)); let B := min (b : ℤ) (((n : ℤ) - (h : ℤ)*((c : ℤ)+1))/(g : ℤ)); let m : ℤ := (h/e : ℕ); let z := ((n/e : ℕ) : ℤ) * Nat.gcdA (g/e) (h/e) % m; if e ∣ n then (if A ≤ B then ((((A-z)%m : ℤ) : ℝ) - (((B-z)%m : ℤ) : ℝ))/(m : ℝ) else 0) else 0)
          let expandedCap := fun n : ℕ => ⌊(n : ℝ)^(511/768 : ℝ)⌋₊
          let inside := fun (n u v : ℕ) =>
            stepCap n^2 < u*v ∧ u.gcd v ≤ stepCap n
          let outside := fun (n u v : ℕ) =>
            (stepCap n^2 < u*v ∧ u.gcd v ≤ stepCap n) ∧ ¬(u ≤ expandedCap n ∧ v ≤ expandedCap n)
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
          let outsideLow := fun n : ℕ =>
            ∑ i ∈ X n, ∑ j ∈ (Y n).filter (fun j => ¬j.1 ∣ n),
              @ite ℂ (outside n (u i) (vl j)) (Classical.propDecidable _) (w n i*((-(μ j.2 : ℂ))*(Λ j.1 : ℂ))*
                integral n (u i) (vl j) 0 (n/u i) 0 (min (B₃ n/j.2) (n/vl j))) 0
          let outsideHigh := fun n : ℕ =>
            ∑ i ∈ X n, ∑ j ∈ Z n,
              @ite ℂ (outside n (u i) (vh j)) (Classical.propDecidable _) (w n i*((-(μ j.1 : ℂ))*(F (PR n) j.2.2 : ℂ))*
                integral n (u i) (vh j) 0 (n/u i) (K n/j.2.2) (n/vh j)) 0
          let residual := fun n : ℕ => (insideLow n + insideHigh n) + (outsideLow n + outsideHigh n)
          (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖residual n‖ ≤ e * (n : ℝ))
    vaughanGoal ↔ residueGoal := by
  exact B13NondividingResidueReductionProof.frozen_iff_bilateral_vaughan.symm.trans
    B13NondividingResidueReductionProof.frozen_iff_raw_expanded_residue

end
