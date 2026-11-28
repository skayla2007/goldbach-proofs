import Mathlib

-- child 1 zh: 对每个充分大的偶数起点，根号长偶数窗中过半的归一化深弧系数范数至多为给定容差。
-- child 1 en: On every sufficiently late even-step square-root window, a strict majority of the normalized B13 coefficients have norm at most the given tolerance.
-- child 2 zh: 对每个充分大的偶数起点，根号长偶数窗中过半的归一化深弧系数与窗首的复数差范数至多为给定容差。
-- child 2 en: On every sufficiently late even-step square-root window, a strict majority of normalized coefficients differ from the left-end coefficient by at most the given tolerance in complex norm.

open Finset
open scoped BigOperators

theorem Conjectures.Cuts.Cutd1b8c2c48e6d9b5c82b9b28f :
(
let B := fun (n : ℕ) (p : ℝ) => ⌊(n : ℝ)^p⌋₊
    let U := fun n => B n (1/16)
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I)
    let w := fun (n l h m : ℕ) =>
      ∑ a ∈ (Nat.divisors m).filter (fun a => l < a ∧ a ≤ h ∧ U n < m/a),
        (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) *
          ArithmeticFunction.vonMangoldt (m/a)
    let S := fun (n l h : ℕ) (t : ℝ) =>
      ∑ k ∈ Finset.range (n+1), (w n l h k : ℂ)*E ((k : ℝ)*t)
    let wide := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B n (1/3) ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤
        ((256*B n (1/3)*(Nat.log 2 (n+2))^2 : ℕ) : ℝ)/((q : ℝ)*(n : ℝ))}
    let J := fun n : ℕ => intervalIntegral (fun t => (wide n)ᶜ.indicator
      (fun x => S n (U n) (B n (1/4)) x*S n (B n (1/3)) (B n (2/3)) x*E (-(n : ℝ)*x)) t)
      (0 : ℝ) 1 MeasureTheory.volume
    let a := fun n : ℕ => J n / (n : ℂ)
    let K := fun n : ℕ => Finset.range (n.sqrt+1)
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      n.sqrt+1 < 2*((K n).filter (fun j => ‖a (n+2*j)‖ ≤ e)).card
) →
(
let B := fun (n : ℕ) (p : ℝ) => ⌊(n : ℝ)^p⌋₊
    let U := fun n => B n (1/16)
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I)
    let w := fun (n l h m : ℕ) =>
      ∑ a ∈ (Nat.divisors m).filter (fun a => l < a ∧ a ≤ h ∧ U n < m/a),
        (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) *
          ArithmeticFunction.vonMangoldt (m/a)
    let S := fun (n l h : ℕ) (t : ℝ) =>
      ∑ k ∈ Finset.range (n+1), (w n l h k : ℂ)*E ((k : ℝ)*t)
    let wide := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ B n (1/3) ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤
        ((256*B n (1/3)*(Nat.log 2 (n+2))^2 : ℕ) : ℝ)/((q : ℝ)*(n : ℝ))}
    let J := fun n : ℕ => intervalIntegral (fun t => (wide n)ᶜ.indicator
      (fun x => S n (U n) (B n (1/4)) x*S n (B n (1/3)) (B n (2/3)) x*E (-(n : ℝ)*x)) t)
      (0 : ℝ) 1 MeasureTheory.volume
    let a := fun n : ℕ => J n / (n : ℂ)
    let K := fun n : ℕ => Finset.range (n.sqrt+1)
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      n.sqrt+1 < 2*((K n).filter (fun j => ‖a (n+2*j)-a n‖ ≤ e)).card
) →
(
let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let B₂ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let B₃ := fun n : ℕ => ⌊(n:ℝ)^(2/3:ℝ)⌋₊; let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let τ₃ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => B₂ n < a ∧ a ≤ B₃ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₃ n)‖ ≤ e * (n : ℝ)
) := by
  intro small stable
  dsimp only at small stable ⊢
  intro e he
  obtain ⟨N, hN⟩ := small (e/2) (by positivity)
  obtain ⟨M, hM⟩ := stable (e/2) (by positivity)
  refine ⟨max 1 (max N M), ?_⟩
  intro n hn even
  let F := Finset.range (n.sqrt+1)
  have hu := hN n (by omega) even
  have hv := hM n (by omega) even
  have overlap {U V : Finset ℕ} (u : U ⊆ F) (v : V ⊆ F)
      (hu : F.card < 2*U.card) (hv : F.card < 2*V.card) :
      ∃ j, j ∈ U ∧ j ∈ V := by
    by_contra! missing
    have disjoint : Disjoint U V := Finset.disjoint_left.mpr
      (fun j hU hV => missing j hU hV)
    have bound : (U ∪ V).card ≤ F.card := card_le_card (union_subset u v)
    rw [card_union_of_disjoint disjoint] at bound
    omega
  have fcard : F.card = n.sqrt+1 := card_range _
  nth_rewrite 1 [← fcard] at hu
  nth_rewrite 1 [← fcard] at hv
  obtain ⟨j, hj, hj'⟩ := overlap
    (show F.filter _ ⊆ F from filter_subset _ _)
    (show F.filter _ ⊆ F from filter_subset _ _) hu hv
  have smallValue := (mem_filter.mp hj).2
  have smallIncrement := (mem_filter.mp hj').2
  have unitBound : ∀ x y : ℂ, ‖x‖ ≤ e/2 → ‖x-y‖ ≤ e/2 → ‖y‖ ≤ e := by
    intro x y hx hxy
    calc
      ‖y‖ = ‖x-(x-y)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖+‖x-y‖ := norm_sub_le _ _
      _ ≤ e := by linarith
  have normalized := unitBound _ _ smallValue smallIncrement
  rw [norm_div, Complex.norm_natCast] at normalized
  exact (div_le_iff₀ (show (0 : ℝ) < n from by exact_mod_cast (show 0<n by omega))).mp normalized
