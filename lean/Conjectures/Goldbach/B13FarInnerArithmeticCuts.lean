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

namespace B13FarInnerArithmeticCutsProof

section

namespace DyadicMixedB4Geometric
open Finset MeasureTheory
noncomputable section

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
end B13FarInnerArithmeticCutsProof

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

namespace B13FarInnerArithmeticCutsProof

open Finset MeasureTheory ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4LowBand
open DyadicMixedB4EnergyTail DyadicMixedB4TailScale
open DyadicMixedB4YoungIntegral DyadicMixedB4NumericBudgets DyadicMixedB4FinalGrowth

noncomputable section

end

end B13FarInnerArithmeticCutsProof

namespace B13FarInnerArithmeticCutsProof

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Arithmetic DyadicMixedB4Scale DyadicMixedB4ArcDecomposition DyadicMixedB4Geometric

noncomputable section

end

end B13FarInnerArithmeticCutsProof

namespace B13FarInnerArithmeticCutsProof

open Finset MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4PairIntegral DyadicMixedB4Finish

noncomputable section

end

end B13FarInnerArithmeticCutsProof

namespace B13FarInnerArithmeticCutsProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Fourier
open DyadicMixedB4Scale DyadicMixedB4HighAtoms DyadicMixedB4PairIntegral

noncomputable section

end

end B13FarInnerArithmeticCutsProof

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Right cofactor -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Left type one -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Left zeta -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Vaughan zeta -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset MeasureTheory Filter Topology
open DyadicMixedB4Geometric DyadicMixedB4ArcGeometry DyadicMixedB4ArcDecomposition
open DyadicMixedB4Scale DyadicMixedB4PairIntegral DyadicMixedB4EnergyTail
open DyadicMixedB4MoebiusGauss DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def vaughanShortCut (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 96 : ℝ)⌋₊

end

end B13FarInnerArithmeticCutsProof

end

/- Right type one saving -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Bilateral short -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Left medium waves -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset MeasureTheory
open DyadicMixedB4Geometric DyadicMixedB4Scale DyadicMixedB4EnergyTail
open DyadicMixedB4ArcGeometry DyadicMixedB4OffWaveMoment DyadicMixedB4YoungIntegral
open DyadicMixedB4ArcDecomposition DyadicMixedB4PairIntegral
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction

noncomputable section

def leftMediumCap (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (3 / 10 : ℝ)⌋₊

end

end B13FarInnerArithmeticCutsProof

end

/- Left bilinear short -/
section

namespace B13FarInnerArithmeticCutsProof

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

end

end B13FarInnerArithmeticCutsProof

end

/- Right bilinear waves -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Joint actual waves -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Joint product limit -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Long lattice -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Residue count -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Residue error -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Wide medium budget -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def wideMediumStepCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(7/12 : ℝ)⌋₊

end

end B13FarInnerArithmeticCutsProof

end

/- Subcritical medium residue -/
section

namespace B13FarInnerArithmeticCutsProof

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

end

end B13FarInnerArithmeticCutsProof

end

/- Medium exact partition -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset
open DyadicMixedB4Scale
open scoped Classical

noncomputable section

def prefixStepGate (n u v : ℕ) : Prop :=
  maximumStep n^2 < u*v ∧ u.gcd v ≤ maximumStep n

instance (n u v : ℕ) : Decidable (prefixStepGate n u v) :=
  inferInstanceAs (Decidable (maximumStep n^2 < u*v ∧ u.gcd v ≤ maximumStep n))

end

end B13FarInnerArithmeticCutsProof

end

/- Medium large gcd residue -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Medium proper prime power -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Gcd scaled residue -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Extended wide approx -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def extendedWideStepCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(21/32 : ℝ)⌋₊

end

end B13FarInnerArithmeticCutsProof

end

/- Residue absolute triple mass -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Scaled large gcd mass -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Extended residue layer -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Extended proper prime power -/
section

namespace B13FarInnerArithmeticCutsProof

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

end

end B13FarInnerArithmeticCutsProof

end

/- Extended hyperbola rows -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Right divisor solution count -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Right divisor volume mass -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Large right divisor residue -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Extended target divisor cut -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4TailScale
open scoped Classical Finset

noncomputable section

def targetDivisorCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/128 : ℝ)⌋₊

end

end B13FarInnerArithmeticCutsProof

end

/- Residue direction swap -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset
open scoped Classical

noncomputable section

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

end

end B13FarInnerArithmeticCutsProof

end

/- Large left divisor residue -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Thin high arithmetic cuts -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open scoped Classical Finset

noncomputable section

def thinHighProductCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(8191/8192 : ℝ)⌋₊
def thinHighGcdCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/4096 : ℝ)⌋₊
def thinHighLeftDivisorCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(1/2048 : ℝ)⌋₊

end

end B13FarInnerArithmeticCutsProof

end

/- Expanded wide approx -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Expanded residue layer -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Outer right wave conversion -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset
open scoped Classical Finset

noncomputable section

def outerRightHighItems (n : ℕ) : Finset RightHighWaveIndex :=
  expandedWaveItems n (rightHighWaveItems n) rightHighWaveStep

end

end B13FarInnerArithmeticCutsProof

end

/- Right bounded cuts -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4TailScale DyadicMixedB4FinalGrowth
open scoped Classical Finset

noncomputable section

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

end

end B13FarInnerArithmeticCutsProof

end

/- Bounded outer left arithmetic -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Raw expanded reduction -/
section

namespace B13FarInnerArithmeticCutsProof

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

end

end B13FarInnerArithmeticCutsProof

end

/- High far strip windows geometry -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def highFarStripProductCap (n : ℕ) : ℕ := 2*⌊(n : ℝ)^(4097/4096 : ℝ)⌋₊

end

end B13FarInnerArithmeticCutsProof

end

/- Far inner arithmetic -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset DyadicMixedB4EnergyTail DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def farInnerGate (n u v : ℕ) : Prop :=
  prefixStepGate n u v ∧ highFarStripProductCap n < u*v

def farInnerThinGate (n u v : ℕ) : Prop :=
  boundedOuterLeftKeptGate farInnerGate n u v ∧ u.gcd n ≤ thinHighLeftDivisorCap n

def farInnerThinFrom (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) : ℂ :=
  rawWavePairSum n (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep)
    (expandedWaveItems n J v) v p s w (farInnerThinGate n)
    (fun u v l r a b => (pairResidueError n u v l r a b : ℂ))

def farInnerLeftDivisorCutFrom (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) : ℂ :=
  largeLeftDivisorResidueFamily n (thinHighLeftDivisorCap n) (thinHighGcdCap n)
    (expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep) (expandedWaveItems n J v)
    leftBilinearStep v p s (leftBilinearWeight n) w
      (fun i j => boundedOuterLeftKeptGate farInnerGate n (leftBilinearStep i) (v j))

theorem far_inner_kept_partition (n : ℕ) {κ : Type} (J : Finset κ)
    (v p s : κ → ℕ) (w : κ → ℂ) :
    boundedOuterLeftKeptFrom farInnerGate n J v p s w =
      farInnerThinFrom n J v p s w + farInnerLeftDivisorCutFrom n J v p s w := by
  unfold boundedOuterLeftKeptFrom farInnerThinFrom rawWavePairSum farInnerLeftDivisorCutFrom
    largeLeftDivisorResidueFamily
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  let u := leftBilinearStep i
  let m := v j
  by_cases h : boundedOuterLeftKeptGate farInnerGate n u m
  · have g : u.gcd m ≤ thinHighGcdCap n := h.2.2.1
    by_cases t : u.gcd n ≤ thinHighLeftDivisorCap n
    · simp [u,m,h,g,t,not_lt.mpr t,farInnerThinGate]
    · simp [u,m,h,g,t,lt_of_not_ge t,farInnerThinGate]
  · simp [u,m,h,farInnerThinGate]

private theorem norm_far_inner_left_divisor_cut_from_le {n : ℕ} (n0 : 0 < n) {κ : Type}
    (J : Finset κ) (v p s : κ → ℕ) (w : κ → ℂ)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T)
    (steps : ∀ j ∈ J, v j ∈ Icc 1 n)
    (weights : ∀ m ∈ Icc 1 n, (∑ j ∈ J.filter (fun j => v j=m), ‖w j‖) ≤ T^3*logBudget n) :
    ‖farInnerLeftDivisorCutFrom n J v p s w‖ ≤
      2*(n : ℝ)^(8191/8192 : ℝ)*T^9*logBudget n^4 := by
  let A := expandedWideStepCap n
  let L := logBudget n
  let W := T^3*L
  let E := thinHighLeftDivisorCap n
  let G := thinHighGcdCap n
  let N := (n : ℝ)
  have nr : 1 ≤ N := by change (1 : ℝ) ≤ n; exact_mod_cast n0
  have np := zero_lt_one.trans_le nr
  have An : A ≤ n := expanded_wide_step_le n0
  have T0 := zero_le_one.trans T1
  have L1 := one_le_logBudget n
  have L0 := zero_le_one.trans L1
  have W0 : 0 ≤ W := by unfold W; positivity
  have range {α : Type} {S : Finset α} {step : α → ℕ} (h : ∀ x ∈ S, step x ∈ Icc 1 n)
      (x : α) (hx : x ∈ expandedWaveItems n S step) : step x ∈ Icc 1 A := by
    obtain ⟨base,cap⟩ := mem_filter.mp hx
    exact mem_Icc.mpr ⟨(mem_Icc.mp (h x base)).1,cap⟩
  have mass {α : Type} {S : Finset α} {step : α → ℕ} {a : α → ℂ}
      (h : ∀ m ∈ Icc 1 n, (∑ i ∈ S.filter (fun i => step i=m), ‖a i‖) ≤ W)
      (m : ℕ) (hm : m ∈ Icc 1 A) :
      (∑ i ∈ (expandedWaveItems n S step).filter (fun i => step i=m), ‖a i‖) ≤ W :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (h m (Icc_subset_Icc_right An hm))
  have divN : N/((E : ℝ)+1) ≤ N^(2047/2048 : ℝ) := by
    calc
      _ ≤ N/N^(1/2048 : ℝ) := div_le_div_of_nonneg_left np.le (by positivity) (Nat.lt_floor_add_one _).le
      _ = _ := by nth_rw 1 [← Real.rpow_one N]; rw [← Real.rpow_sub np]; norm_num
  have gSize : (G : ℝ) ≤ N^(1/4096 : ℝ) := Nat.floor_le (by positivity)
  have G1 : 1 ≤ N^(1/4096 : ℝ) := Real.one_le_rpow nr (by norm_num)
  have ht : T^2+(G : ℝ)*L^2 ≤ 2*N^(1/4096 : ℝ)*T^2*L^2 := by
    have a := (le_mul_of_one_le_left (sq_nonneg T) G1).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ L1 (n := 2)))
    have b := mul_le_mul_of_nonneg_right
      (gSize.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ T1 (n := 2)))) (sq_nonneg L)
    linarith only [a,b]
  unfold farInnerLeftDivisorCutFrom
  refine (norm_large_left_divisor_residue_family_le n0 An _ _ _ _ _ _ _ _ _ W0 T0 divisors
    (range (fun _ h => bilateral_left_step_range h)) (range steps)
    (mass (norm_bilateral_left_step_mass n0 T0 divisors)) (mass weights)).trans ?_
  calc
    _ ≤ T*(W^2*N^(2047/2048 : ℝ)*(2*N^(1/4096 : ℝ)*T^2*L^2)) := by gcongr
    _ = 2*(N^(2047/2048 : ℝ)*N^(1/4096 : ℝ))*T^9*L^4 := by unfold W; ring
    _ ≤ _ := by
      have h : N^(2047/2048 : ℝ)*N^(1/4096 : ℝ) ≤ N^(8191/8192 : ℝ) := by
        rw [← Real.rpow_add np]
        exact Real.rpow_le_rpow_of_exponent_le nr (by norm_num)
      gcongr

theorem far_inner_left_divisor_cut_saving {κ : Type} (J : ℕ → Finset κ)
    (v : κ → ℕ) (p s : ℕ → κ → ℕ) (w : ℕ → κ → ℂ)
    (steps : ∀ n, ∀ j ∈ J n, v j ∈ Icc 1 n)
    (weights : ∀ n, ∀ {T : ℝ}, 1 ≤ T → (∀ u ≤ n, (u.divisors.card : ℝ) ≤ T) →
      ∀ m ∈ Icc 1 n, (∑ j ∈ (J n).filter (fun j => v j=m), ‖w n j‖) ≤ T^3*logBudget n) :
    saving (fun n => farInnerLeftDivisorCutFrom n (J n) v (p n) (s n) (w n)) := by
  apply saving_of_bounded_right_growth _ (K := 2) (by norm_num)
  intro n n0 T T1 divs
  exact norm_far_inner_left_divisor_cut_from_le n0 (J n) v (p n) (s n) (w n) T1 divs
    (steps n) (weights n T1 divs)

end

end B13FarInnerArithmeticCutsProof

end

/- Far expanded proper power -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset Filter Topology ArithmeticFunction
open DyadicMixedB4Scale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth DyadicMixedB4PairIntegral DyadicMixedB4TailScale DyadicMixedB4MoebiusGauss
open scoped Classical ArithmeticFunction.Moebius

noncomputable section

private theorem expanded_proper_power_right_data {n : ℕ} {j : RightLowWaveIndex}
    (h : j ∈ extendedProperPowerRightItems n) :
    j ∈ rightLowWaveItems n ∧ 0 < j.2 ∧ j.2 ≤ cutoffU n ∧ j.1 ≤ rightLargeCofactorCut n := by
  have base := (mem_filter.mp (mem_filter.mp (mem_filter.mp h).1).1).1
  have d := mem_Icc.mp (mem_sigma.mp base).2
  have bK := (mem_Ioc.mp (mem_sigma.mp base).1).2.trans (min_le_right _ _)
  exact ⟨base,d.1,d.2.trans (min_le_left _ _),bK⟩

def expandedProperPowerResidueSliceWith (gate : ℕ → ℕ → ℕ → Prop) (n : ℕ) : ℂ :=
  ∑ i ∈ expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep,
    ∑ j ∈ extendedProperPowerRightItems n,
      let u := leftBilinearStep i
      let v := rightLowWaveStep j
      @ite ℂ (gate n u v) (Classical.propDecidable _)
        (leftBilinearWeight n i*rightLowWaveWeight j*
          (pairResidueError n u v 0 (n/u) 0 (rightLowWaveUpper n j) : ℂ)) 0

private theorem norm_expanded_proper_power_residue_slice_with_le (gate : ℕ → ℕ → ℕ → Prop) {n : ℕ} (n2 : 2 ≤ n)
    {T : ℝ} (T1 : 1 ≤ T) (divisors : ∀ m ≤ n, (m.divisors.card : ℝ) ≤ T) :
    ‖expandedProperPowerResidueSliceWith gate n‖ ≤ 5*(n : ℝ)^(757/768 : ℝ)*T^3*logBudget n^3 := by
  let A := expandedWideStepCap n
  let K := rightLargeCofactorCut n
  let I := expandedWaveItems n (bilateralLeftWaveItems n) leftBilinearStep
  let J := extendedProperPowerRightItems n
  let L := logBudget n
  let W := T^3*L
  have n0 : 0 < n := by omega
  have nR : (0 : ℝ) < n := by exact_mod_cast n0
  have An : A ≤ n := expanded_wide_step_le n0
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
    obtain ⟨hbase,_,_,_⟩ := expanded_proper_power_right_data hj
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
  have aCap : (A : ℝ) ≤ (n : ℝ)^(511/768 : ℝ) := Nat.floor_le (by positivity)
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
    have v0 := (mem_Icc.mp (bilateral_right_low_step_range (expanded_proper_power_right_data hj).1)).1
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
    _ ≤ (W*(n : ℝ)^(511/768 : ℝ))*(((n : ℝ)^(33/128 : ℝ)*(5*L)*(n : ℝ)^(1/16 : ℝ))*L) := by gcongr
    _ = 5*((n : ℝ)^(511/768 : ℝ)*(n : ℝ)^(33/128 : ℝ)*(n : ℝ)^(1/16 : ℝ))*T^3*L^3 := by unfold W; ring
    _ = _ := by rw [← Real.rpow_add nR, ← Real.rpow_add nR]; norm_num [L]

theorem expanded_proper_power_residue_with_saving (gate : ℕ → ℕ → ℕ → Prop) : saving (expandedProperPowerResidueSliceWith gate) := by
  intro ε he
  obtain ⟨D,D1,dBound⟩ := divisor_envelope_at_power 1024 (by decide)
  let C := 5*D^3
  have limit : Tendsto (fun n : ℕ => (n : ℝ)^(-(1/128) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/128)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have scaled : Tendsto (fun n : ℕ => C*(n : ℝ)^(-(1/128) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul limit
  have estimate : ∀ᶠ n : ℕ in atTop, ‖expandedProperPowerResidueSliceWith gate n‖ ≤ ε*(n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, eventually_log_budget_le_power (1/1024) (by norm_num),
      scaled.eventually_lt_const he] with n hn logb small
    have n1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have nr : (0 : ℝ) < n := zero_lt_one.trans_le n1
    have log0 := zero_le_one.trans (one_le_logBudget n)
    let X := (n : ℝ)^(1/1024 : ℝ)
    let T := D*X
    have T1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le D1
      (Real.one_le_rpow n1 (by norm_num))
    have exponent : (n : ℝ)^(757/768 : ℝ)*X^6 ≤ (n : ℝ)^(-(1/128) : ℝ)*(n : ℝ) := by
      unfold X
      rw [← Real.rpow_mul_natCast nr.le, ← Real.rpow_add nr, ← Real.rpow_add_one nr.ne']
      exact Real.rpow_le_rpow_of_exponent_le n1 (by norm_num)
    calc
      _ ≤ 5*(n : ℝ)^(757/768 : ℝ)*T^3*logBudget n^3 :=
        norm_expanded_proper_power_residue_slice_with_le gate hn T1 (dBound n)
      _ ≤ 5*(n : ℝ)^(757/768 : ℝ)*T^3*X^3 := by gcongr
      _ = C*((n : ℝ)^(757/768 : ℝ)*X^6) := by unfold C T; ring
      _ ≤ C*((n : ℝ)^(-(1/128) : ℝ)*(n : ℝ)) :=
        mul_le_mul_of_nonneg_left exponent (by unfold C; positivity)
      _ = (C*(n : ℝ)^(-(1/128) : ℝ))*(n : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right small.le nr.le
  obtain ⟨N,h⟩ := eventually_atTop.mp estimate
  exact ⟨N,fun n hn _ => h n hn⟩

end

end B13FarInnerArithmeticCutsProof

end

/- Outer left remainder -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset DyadicMixedB4EnergyTail
open scoped Classical Finset

noncomputable section

def outerLeftLowItems (n : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n)

end

end B13FarInnerArithmeticCutsProof

end

/- Large high product remainder -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Low product families -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset DyadicMixedB4Scale
open scoped Classical Finset

noncomputable section

def lowPrimeItems (n : ℕ) : Finset RightLowWaveIndex :=
  (rightLowWaveItems n).filter (fun j => j.1.Prime ∧ ¬j.1 ∣ n)

end

end B13FarInnerArithmeticCutsProof

end

/- Low product remainder -/
section

namespace B13FarInnerArithmeticCutsProof

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

end B13FarInnerArithmeticCutsProof

end

/- Far inner remainder -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset ArithmeticFunction DyadicMixedB4EnergyTail
open scoped Classical Finset

noncomputable section

private theorem raw_low_above_product_eq_prime_add_proper (n : ℕ) :
    rawExpandedLowAboveProduct n =
      boundedOuterLeftBaseFrom farInnerGate n (lowPrimeItems n) rightLowWaveStep (fun _ => 0)
        (rightLowWaveUpper n) rightLowWaveWeight +
      expandedProperPowerResidueSliceWith farInnerGate n := by
  have leftLow : expandedWaveItems n (outerLeftLowItems n) rightLowWaveStep = outerLeftLowItems n := by
    apply filter_eq_self.mpr
    intro j hj
    exact ((right_low_step_le_proved_medium_cap (mem_filter.mp hj).1).trans
      (old_step_cap_le_extended n)).trans (extended_step_cap_le_expanded n)
  have leftPrime : expandedWaveItems n (lowPrimeItems n) rightLowWaveStep = lowPrimeItems n := by
    apply filter_eq_self.mpr
    intro j hj
    exact ((right_low_step_le_proved_medium_cap (mem_filter.mp hj).1).trans
      (old_step_cap_le_extended n)).trans (extended_step_cap_le_expanded n)
  have rightProper : extendedProperPowerRightItems n =
      (rightLowWaveItems n).filter (fun j => ¬j.1 ∣ n ∧ ¬j.1.Prime ∧ IsPrimePow j.1) := by
    ext j
    unfold extendedProperPowerRightItems extendedWaveItems
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨⟨base,nd⟩,_⟩,p,it⟩
      exact ⟨base,nd,p,it⟩
    · rintro ⟨base,nd,p,it⟩
      exact ⟨⟨⟨base,nd⟩,(right_low_step_le_proved_medium_cap base).trans (old_step_cap_le_extended n)⟩,p,it⟩
  unfold rawExpandedLowAboveProduct rawWavePairSum boundedOuterLeftBaseFrom expandedProperPowerResidueSliceWith
  rw [leftLow,leftPrime,rightProper]
  unfold outerLeftLowItems lowPrimeItems
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [sum_filter,← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases g : prefixStepGate n (leftBilinearStep i) (rightLowWaveStep j) ∧
      highFarStripProductCap n < leftBilinearStep i * rightLowWaveStep j
  · have h : farInnerGate n (leftBilinearStep i) (rightLowWaveStep j) := g
    by_cases d : j.1 ∣ n
    · simp [d]
    · by_cases p : j.1.Prime
      · simp [d,p,g,h]
      · by_cases q : IsPrimePow j.1
        · simp [d,p,q,g,h]
        · have z : vonMangoldt j.1 = 0 := vonMangoldt_eq_zero_iff.mpr q
          simp [d,p,q,rightLowWaveWeight,z]
  · have h : ¬ farInnerGate n (leftBilinearStep i) (rightLowWaveStep j) := g
    by_cases d : j.1 ∣ n <;> by_cases p : j.1.Prime <;> by_cases q : IsPrimePow j.1 <;>
      simp [d,p,q,g,h]

def farInnerAfterTrimming (n : ℕ) : ℂ :=
  farInnerThinFrom n (lowPrimeItems n) rightLowWaveStep
    (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight +
  farInnerThinFrom n (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)

def farInnerTrimming (n : ℕ) : ℂ :=
  expandedProperPowerResidueSliceWith farInnerGate n +
  (boundedOuterLeftCut farInnerGate n (lowPrimeItems n) rightLowWaveStep
    (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight +
  boundedOuterLeftCut farInnerGate n (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n)) +
  (farInnerLeftDivisorCutFrom n (lowPrimeItems n) rightLowWaveStep
    (fun _ => 0) (rightLowWaveUpper n) rightLowWaveWeight +
  farInnerLeftDivisorCutFrom n (rightHighWaveItems n) rightHighWaveStep
    (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n))

theorem raw_expanded_eq_far_inner_trimming (n : ℕ) :
    rawExpandedAfterBoundedProducts n = farInnerAfterTrimming n + farInnerTrimming n := by
  have high :
      rawExpandedHighAboveProduct n =
        boundedOuterLeftBaseFrom farInnerGate n (rightHighWaveItems n) rightHighWaveStep
          (rightHighWaveLower n) (fun j => n/rightHighWaveStep j) (rightHighWaveWeight n) := rfl
  unfold rawExpandedAfterBoundedProducts farInnerAfterTrimming farInnerTrimming
  rw [raw_low_above_product_eq_prime_add_proper,high,
    bounded_outer_left_base_eq_partition,bounded_outer_left_base_eq_partition,
    far_inner_kept_partition,far_inner_kept_partition]
  abel

private theorem far_inner_saving_add {a b : ℕ → ℂ} (ha : saving a) (hb : saving b) :
    saving (fun n => a n + b n) := by
  intro ε he
  obtain ⟨N,hN⟩ := ha (ε/2) (by positivity)
  obtain ⟨M,hM⟩ := hb (ε/2) (by positivity)
  refine ⟨max N M,fun n hn even => ?_⟩
  exact (norm_add_le _ _).trans
    (by linarith only [hN n (by omega) even,hM n (by omega) even])

theorem far_inner_trimming_saving : saving farInnerTrimming := by
  have loStep (n : ℕ) (j : RightLowWaveIndex) (h : j ∈ lowPrimeItems n) :
      rightLowWaveStep j ∈ Icc 1 n := bilateral_right_low_step_range (mem_filter.mp h).1
  have lowMass (n : ℕ) {T : ℝ} (T1 : 1 ≤ T) (d : ∀ u ≤ n, (u.divisors.card : ℝ) ≤ T)
      (m : ℕ) (hm : m ∈ Icc 1 n) :
      (∑ j ∈ (lowPrimeItems n).filter (fun j => rightLowWaveStep j=m), ‖rightLowWaveWeight j‖) ≤
        T^3*logBudget n :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
      (fun _ _ _ => norm_nonneg _)).trans (norm_bilateral_right_low_step_mass T1 d m hm)
  have hiStep (n : ℕ) (j : RightHighWaveIndex) (h : j ∈ rightHighWaveItems n) :
      rightHighWaveStep j ∈ Icc 1 n := bilateral_right_high_step_range h
  have highMass (n : ℕ) {T : ℝ} (T1 : 1 ≤ T) (d : ∀ u ≤ n, (u.divisors.card : ℝ) ≤ T)
      (m : ℕ) (hm : m ∈ Icc 1 n) :
      (∑ j ∈ (rightHighWaveItems n).filter (fun j => rightHighWaveStep j=m), ‖rightHighWaveWeight n j‖) ≤
        T^3*logBudget n :=
    norm_bilateral_right_high_step_mass (zero_le_one.trans T1) d m hm
  have lowOuter := bounded_outer_left_cut_saving farInnerGate lowPrimeItems rightLowWaveStep
    (fun _ _ => 0) rightLowWaveUpper (fun _ => rightLowWaveWeight) loStep
    (fun n _ t d m hm => lowMass n t d m hm)
  have highOuter := bounded_outer_left_cut_saving farInnerGate rightHighWaveItems rightHighWaveStep
    rightHighWaveLower (fun n j => n/rightHighWaveStep j) rightHighWaveWeight hiStep
    (fun n _ t d m hm => highMass n t d m hm)
  have lowLeft := far_inner_left_divisor_cut_saving lowPrimeItems rightLowWaveStep
    (fun _ _ => 0) rightLowWaveUpper (fun _ => rightLowWaveWeight) loStep
    (fun n _ t d m hm => lowMass n t d m hm)
  have highLeft := far_inner_left_divisor_cut_saving rightHighWaveItems rightHighWaveStep
    rightHighWaveLower (fun n j => n/rightHighWaveStep j) rightHighWaveWeight hiStep
    (fun n _ t d m hm => highMass n t d m hm)
  exact far_inner_saving_add (far_inner_saving_add (expanded_proper_power_residue_with_saving farInnerGate)
    (far_inner_saving_add lowOuter highOuter)) (far_inner_saving_add lowLeft highLeft)

end

end B13FarInnerArithmeticCutsProof

end

/- Route far cuts -/
section

namespace B13FarInnerArithmeticCutsProof

open Finset

theorem saving_far_inner_discarded :
    saving (fun n => rawExpandedAfterBoundedProducts n - farInnerAfterTrimming n) := by
  have heq (n : ℕ) :
      rawExpandedAfterBoundedProducts n - farInnerAfterTrimming n = farInnerTrimming n := by
    rw [raw_expanded_eq_far_inner_trimming]
    abel
  simp_rw [heq]
  exact far_inner_trimming_saving

end B13FarInnerArithmeticCutsProof

theorem Conjectures.Goldbach.B13FarInnerArithmeticCuts :
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
      (stepCap n^2 < u*v ∧ u.gcd v ≤ stepCap n) ∧ productCap n < u*v
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
    let retained := fun (n u v : ℕ) =>
      (((stepCap n^2 < u*v ∧ u.gcd v ≤ stepCap n) ∧ productCap n < u*v) ∧
        ⌊(n : ℝ)^(8191/8192 : ℝ)⌋₊ < u*v ∧ u.gcd v ≤ ⌊(n : ℝ)^(1/4096 : ℝ)⌋₊ ∧
        v.gcd n ≤ ⌊(n : ℝ)^(1/128 : ℝ)⌋₊) ∧ u.gcd n ≤ ⌊(n : ℝ)^(1/2048 : ℝ)⌋₊
    let retainedLow := fun n : ℕ =>
      ∑ i ∈ (X n).filter (fun i => u i ≤ expandedCap n),
      ∑ j ∈ ((Y n).filter (fun j => j.1.Prime ∧ ¬j.1 ∣ n)).filter (fun j => vl j ≤ expandedCap n),
        @ite ℂ (retained n (u i) (vl j)) (Classical.propDecidable _) (w n i*((-(μ j.2 : ℂ))*(Λ j.1 : ℂ))*
          (errorPart n (u i) (vl j) 0 (n/u i) 0 (min (B₃ n/j.2) (n/vl j)) : ℂ)) 0
    let retainedHigh := fun n : ℕ =>
      ∑ i ∈ (X n).filter (fun i => u i ≤ expandedCap n),
      ∑ j ∈ (Z n).filter (fun j => vh j ≤ expandedCap n),
        @ite ℂ (retained n (u i) (vh j)) (Classical.propDecidable _) (w n i*((-(μ j.1 : ℂ))*(F (PR n) j.2.2 : ℂ))*
          (errorPart n (u i) (vh j) 0 (n/u i) (K n/j.2.2) (n/vh j) : ℂ)) 0
    let residual := fun n => (insideLow n + insideHigh n) - (retainedLow n + retainedHigh n)
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖residual n‖ ≤ e * (n : ℝ) := by
  exact B13FarInnerArithmeticCutsProof.saving_far_inner_discarded

end
