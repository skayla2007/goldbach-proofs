import Mathlib

open scoped BigOperators

namespace B13InnerLowFarDiagonalAndEdgesSavingProof

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

theorem progression_pair_count_le {n u v l r p s : ℕ} (hv : 0 < v) :
    (progressionPairSolutions n u v l r p s).card ≤ r / (v / u.gcd v) + 1 := by
  let V := v / u.gcd v
  let points := progressionPairSolutions n u v l r p s
  have compare (i j : ℕ × ℕ) (hi : i ∈ points) (hj : j ∈ points) :
      i.1 ≡ j.1 [MOD V] := by
    have left := (mem_filter.mp hi).2
    have right := (mem_filter.mp hj).2
    have first : u*i.1 ≡ n [MOD v] := by
      rw [← left]
      have term : 0 ≡ v*i.2 [MOD v] := (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right v i.2)).symm
      simpa only [add_zero] using (Nat.ModEq.refl (u*i.1)).add term
    have second : u*j.1 ≡ n [MOD v] := by
      rw [← right]
      have term : 0 ≡ v*j.2 [MOD v] := (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right v j.2)).symm
      simpa only [add_zero] using (Nat.ModEq.refl (u*j.1)).add term
    simpa only [V, Nat.gcd_comm v u] using Nat.ModEq.cancel_left_div_gcd hv (first.trans second.symm)
  have count : points.card ≤ (range (r / V + 1)).card := by
    apply card_le_card_of_injOn (fun i : ℕ × ℕ => i.1 / V)
    · intro i hi
      have hi' : i ∈ points := hi
      have up := (mem_Ioc.mp (mem_product.mp (mem_filter.mp hi').1).1).2
      exact mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.div_le_div_right up))
    · intro i hi j hj quotient
      have hi' : i ∈ points := hi
      have hj' : j ∈ points := hj
      have modEq := compare i j hi' hj'
      have first : i.1 = j.1 := by
        have ie := Nat.div_add_mod i.1 V
        have je := Nat.div_add_mod j.1 V
        change i.1 % V = j.1 % V at modEq
        change i.1 / V = j.1 / V at quotient
        rw [quotient, modEq, je] at ie
        exact ie.symm
      have Li := (mem_filter.mp hi').2
      have Lj := (mem_filter.mp hj').2
      apply Prod.ext first
      apply Nat.eq_of_mul_eq_mul_left hv
      rw [first] at Li
      exact Nat.add_left_cancel (Li.trans Lj.symm)
  simpa [points, V] using count

theorem progression_pair_at_most_one {n u v l r p s : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hr : r ≤ n/u) (large : n * u.gcd v < u*v) :
    (progressionPairSolutions n u v l r p s).card ≤ 1 := by
  let d := u.gcd v
  let V := v / d
  have dvd : d ∣ v := Nat.gcd_dvd_right _ _
  have cancel : V*d=v := Nat.div_mul_cancel dvd
  have rLt : r < V := by
    by_contra! le
    have bound : r*u ≤ n := (Nat.le_div_iff_mul_le hu).mp hr
    have prod : (u*V)*d ≤ n*d := by
      have uv := (Nat.mul_le_mul_right u le).trans bound
      simpa only [Nat.mul_comm u V] using Nat.mul_le_mul_right d uv
    rw [Nat.mul_assoc, cancel] at prod
    exact (not_lt_of_ge prod) large
  have zero : r / (v / u.gcd v) = 0 := Nat.div_eq_of_lt rLt
  simpa only [zero, zero_add] using progression_pair_count_le (n := n)
    (u := u) (v := v) (l := l) (r := r) (p := p) (s := s) hv

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

/- Source PEqualNP.Outside.L_b13_extended_wide_approx -/
section

namespace GoldbachTypeII13

open Finset Filter Topology
open DyadicMixedB4Scale DyadicMixedB4TailScale DyadicMixedB4EnergyTail DyadicMixedB4FinalGrowth
open scoped Classical

noncomputable section

def extendedWideStepCap (n : ℕ) : ℕ := ⌊(n : ℝ)^(21/32 : ℝ)⌋₊

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_residue_absolute_triple_mass -/
section

namespace GoldbachTypeII13

open Finset
open scoped Classical Finset

noncomputable section

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

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_remainder -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def innerLowNearProduct (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  leftBilinearStep i*rightLowWaveStep j ≤ weilNearProductCap n

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

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_far_diagonal -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def innerLowFarAtom (n u v : ℕ) : ℂ :=
  ((progressionPairSolutions n u v 0 (n/u) 0 (n/v)).card : ℂ)-
    ((u.gcd v : ℝ)*((n : ℝ)/((u : ℝ)*(v : ℝ))) : ℂ)

theorem inner_low_far_product_above_normalized {n u v : ℕ} (n1 : 1 ≤ n)
    (gcd : u.gcd v ≤ thinHighGcdCap n) (prod : weilNearProductCap n < u*v) :
    n*(u.gcd v) < u*v := by
  let N := (n : ℝ)
  let p := N^(1+3/8192 : ℝ)
  have N1 : 1 ≤ N := by unfold N; exact_mod_cast n1
  have N0 := zero_lt_one.trans_le N1
  have p1 : 1 ≤ p := Real.one_le_rpow N1 (by norm_num)
  have floor : p ≤ 2*(⌊p⌋₊ : ℝ) := by
    by_cases small : p ≤ 2
    · have smallFloor : (1 : ℝ) ≤ ⌊p⌋₊ := by exact_mod_cast Nat.le_floor p1
      linarith only [small,smallFloor]
    · have large : 2 ≤ p := le_of_not_ge small
      linarith only [large,Nat.lt_floor_add_one p]
  have gcdR : (u.gcd v : ℝ) ≤ N^(1/4096 : ℝ) :=
    (show (u.gcd v : ℝ) ≤ thinHighGcdCap n by exact_mod_cast gcd).trans (Nat.floor_le (by positivity))
  have h : (n : ℝ)*(u.gcd v : ℝ) ≤ (weilNearProductCap n : ℝ) := by
    calc
      _ ≤ N*N^(1/4096 : ℝ) := mul_le_mul_of_nonneg_left gcdR N0.le
      _ = N^(1+1/4096 : ℝ) := by rw [Real.rpow_add N0,Real.rpow_one]
      _ ≤ p := Real.rpow_le_rpow_of_exponent_le N1 (by norm_num)
      _ ≤ _ := by simpa only [weilNearProductCap,Nat.cast_mul,Nat.cast_ofNat] using floor
  exact (show n*(u.gcd v) ≤ weilNearProductCap n by exact_mod_cast h).trans_lt prod

theorem norm_inner_low_far_atom_le_one {n u v : ℕ} (n1 : 1 ≤ n)
    (u0 : 0 < u) (v0 : 0 < v) (gcd : u.gcd v ≤ thinHighGcdCap n)
    (prod : weilNearProductCap n < u*v) :
    ‖innerLowFarAtom n u v‖ ≤ 1 := by
  have sparse := inner_low_far_product_above_normalized n1 gcd prod
  have count := progression_pair_at_most_one (l := 0) (p := 0) (r := n/u) (s := n/v) u0 v0 le_rfl sparse
  let A := (progressionPairSolutions n u v 0 (n/u) 0 (n/v)).card
  let B := (u.gcd v : ℝ)*((n : ℝ)/((u : ℝ)*(v : ℝ)))
  have B0 : 0 ≤ B := by unfold B; positivity
  have B1 : B ≤ 1 := by
    have prod0 : 0 < (u : ℝ)*(v : ℝ) := by
      have a : (0 : ℝ) < u := by exact_mod_cast u0
      have b : (0 : ℝ) < v := by exact_mod_cast v0
      positivity
    unfold B
    rw [← mul_div_assoc]
    apply (div_le_iff₀ prod0).mpr
    rw [one_mul,mul_comm]
    exact_mod_cast sparse.le
  have cast : innerLowFarAtom n u v = (((A : ℝ)-B : ℝ) : ℂ) := by
    unfold innerLowFarAtom A B
    push_cast
    rfl
  rw [cast,Complex.norm_real,Real.norm_eq_abs,abs_le]
  have A1 : (A : ℝ) ≤ 1 := by unfold A; exact_mod_cast count
  have A0 : (0 : ℝ) ≤ A := by positivity
  exact ⟨by linarith only [A0,B1],by linarith only [A1,B0]⟩

def innerLowFarDiagonalGate (n u v : ℕ) : Prop :=
  u ≤ v+⌊(n : ℝ)^(2/5 : ℝ)⌋₊ ∧ v ≤ u+⌊(n : ℝ)^(2/5 : ℝ)⌋₊

def innerLowFarDiagonal (n : ℕ) : ℂ :=
  innerLowFarWeighted n (fun u v => if innerLowFarDiagonalGate n u v then innerLowFarAtom n u v else 0)

def innerLowFarOffDiagonal (n : ℕ) : ℂ :=
  innerLowFarWeighted n (fun u v => if innerLowFarDiagonalGate n u v then 0 else innerLowFarAtom n u v)

theorem inner_low_far_discrepancy_split (n : ℕ) :
    innerLowFarCountDiscrepancy n=innerLowFarOffDiagonal n+innerLowFarDiagonal n := by
  unfold innerLowFarCountDiscrepancy innerLowFarOffDiagonal innerLowFarDiagonal innerLowFarWeighted
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases gate : innerLowFarGate n i j <;>
    by_cases diag : innerLowFarDiagonalGate n (leftBilinearStep i) (rightLowWaveStep j) <;>
    simp [gate,diag,innerLowFarAtom]

set_option maxHeartbeats 1500000 in
theorem inner_low_far_diagonal_saving : saving innerLowFarDiagonal := by
  apply saving_of_weil_near_growth _ 3 (by norm_num)
  intro n n1 T T1 divs
  let K := ⌊(n : ℝ)^(2/5 : ℝ)⌋₊
  let A := ⌊(n : ℝ)^(37/64 : ℝ)⌋₊
  let J := longRightLowItems n
  let I := bilateralLeftWaveItems n
  let u := leftBilinearStep
  let v := rightLowWaveStep
  let a := leftPrimeWeight n
  let b := rightLowWaveWeight
  let L := logBudget n
  let W := T^3*L
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have nR0 := zero_lt_one.trans_le nR
  have W0 : 0 ≤ W := mul_nonneg (pow_nonneg (zero_le_one.trans T1) 3) (zero_le_one.trans (one_le_logBudget n))
  have AN : A ≤ n := Nat.floor_le_of_le (Real.rpow_le_self_of_one_le nR (by norm_num))
  have divN (m : ℕ) (hm : m ≤ n) : (m.divisors.card : ℝ) ≤ T := by
    apply divs m (hm.trans ?_)
    have p : n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
    omega
  have jr (j : RightLowWaveIndex) (hj : j ∈ J) : v j ∈ Icc 1 A :=
    mem_Icc.mpr ⟨(mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))).1,
      Nat.le_floor (long_right_low_step_le_power hj)⟩
  have wtR : (∑ j ∈ J, ‖b j‖) ≤ W*(A : ℝ) :=
    sum_norm_le_of_step_mass J v b jr (fun v hv => long_right_low_step_mass T1 divN v (Icc_subset_Icc_right AN hv))
  let geo (i : ℕ × ℕ) (j : RightLowWaveIndex) := innerLowFarDiagonalGate n (u i) (v j)
  let G (j : RightLowWaveIndex) := I.filter fun i => geo i j
  have massI := prime_left_mass_of_subset (show I ⊆ bilateralLeftWaveItems n from rfl.ge) T1 divN
  have wtL (j : RightLowWaveIndex) : (∑ i ∈ G j, ‖a i‖) ≤ W*(2*(K : ℝ)+1) := by
    let M := Icc (max 1 (v j-K)) (min n (v j+K))
    have maps (i : ℕ × ℕ) (hi : i ∈ G j) : u i ∈ M := by
      have reach : u i ≤ v j+K ∧ v j ≤ u i+K := (mem_filter.mp hi).2
      have ir := mem_Icc.mp (bilateral_left_step_range (mem_filter.mp hi).1)
      exact mem_Icc.mpr ⟨max_le ir.1 (by omega),le_min ir.2 reach.1⟩
    rw [← sum_fiberwise_of_maps_to maps]
    have count : M.card ≤ 2*K+1 :=
      (card_le_card (show M ⊆ Icc (v j-K) (v j+K) from
        Icc_subset_Icc (le_max_right _ _) (min_le_right _ _))).trans (by rw [Nat.card_Icc]; omega)
    calc
      _ ≤ ∑ _m ∈ M, W := by
        refine sum_le_sum fun m hm => ?_
        exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
          (fun _ _ _ => norm_nonneg _)).trans
          (massI m (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _) hm))
      _ = (M.card : ℝ)*W := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        rw [mul_comm W]
        apply mul_le_mul_of_nonneg_right _ W0
        exact_mod_cast count
  let f (i : ℕ × ℕ) (j : RightLowWaveIndex) :=
    if innerLowFarGate n i j then a i*b j*(if geo i j then innerLowFarAtom n (u i) (v j) else 0) else 0
  have point (j : RightLowWaveIndex) (hj : j ∈ J) (i : ℕ × ℕ) (hi : i ∈ I) :
      ‖f i j‖ ≤ if geo i j then ‖a i‖*‖b j‖ else 0 := by
    by_cases diagonal : geo i j
    · rw [if_pos diagonal]
      unfold f
      by_cases h : innerLowFarGate n i j
      · rw [if_pos h,if_pos diagonal,norm_mul,norm_mul]
        have u0 := (mem_Icc.mp (bilateral_left_step_range hi)).1
        have v0 := (mem_Icc.mp (jr j hj)).1
        have gcd : (u i).gcd (v j) ≤ thinHighGcdCap n := h.1.2.2.1.1.2.2.1
        have far : weilNearProductCap n < u i*v j := lt_of_not_ge h.2.2
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (norm_inner_low_far_atom_le_one n1 u0 v0 gcd far) (by positivity : 0≤‖a i‖*‖b j‖)
      · simp [h] <;> positivity
    · unfold f
      simp [diagonal]
  have row (j : RightLowWaveIndex) (hj : j ∈ J) :
      ‖∑ i ∈ I, f i j‖ ≤ (W*(2*(K : ℝ)+1))*‖b j‖ := by
    calc
      _ ≤ ∑ i ∈ I, ‖f i j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ I, if geo i j then ‖a i‖*‖b j‖ else 0 := sum_le_sum (fun i hi => point j hj i hi)
      _ = (∑ i ∈ G j, ‖a i‖)*‖b j‖ := by unfold G; rw [← sum_filter,sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (wtL j) (norm_nonneg _)
  have mass : (2*(K : ℝ)+1)*(A : ℝ) ≤ 3*(n : ℝ)^(8191/8192 : ℝ) := by
    have kBound : (K : ℝ) ≤ (n : ℝ)^(2/5 : ℝ) := Nat.floor_le (by positivity)
    have oneLe : 1 ≤ (n : ℝ)^(2/5 : ℝ) := Real.one_le_rpow nR (by norm_num)
    have aBound : (A : ℝ) ≤ (n : ℝ)^(37/64 : ℝ) := Nat.floor_le (by positivity)
    calc
      _ ≤ (3*(n : ℝ)^(2/5 : ℝ))*(n : ℝ)^(37/64 : ℝ) :=
        mul_le_mul (by linarith only [kBound,oneLe]) aBound (by positivity) (by positivity)
      _ = 3*(n : ℝ)^(2/5+37/64 : ℝ) := by rw [mul_assoc,← Real.rpow_add nR0]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le nR (by norm_num)) (by norm_num)
  change ‖∑ i ∈ I, ∑ j ∈ J, f i j‖ ≤ _
  rw [sum_comm]
  calc
    _ ≤ ∑ j ∈ J, ‖∑ i ∈ I, f i j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, W*(2*(K : ℝ)+1)*‖b j‖ := sum_le_sum row
    _ = (W*(2*(K : ℝ)+1))*(∑ j ∈ J, ‖b j‖) := (mul_sum ..).symm
    _ ≤ (W*(2*(K : ℝ)+1))*(W*(A : ℝ)) := mul_le_mul_of_nonneg_left wtR (by positivity)
    _ = ((2*(K : ℝ)+1)*(A : ℝ))*T^6*L^2 := by unfold W; ring
    _ ≤ 3*(n : ℝ)^(8191/8192 : ℝ)*T^9*L^5 := by
      have pT : T^6 ≤ T^9 := pow_le_pow_right₀ T1 (by decide)
      have pL : L^2 ≤ L^5 := pow_le_pow_right₀ (one_le_logBudget n) (by decide)
      gcongr

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_far_divisor_fibres -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

theorem full_progression_count_eq_divisor_fibres {n u v : ℕ} (u0 : 0 < u) (v0 : 0 < v) :
    (progressionPairSolutions n u v 0 (n/u) 0 (n/v)).card =
      ((Icc 1 (n-1)).filter (fun t => u ∣ t ∧ v ∣ n-t)).card := by
  apply le_antisymm (progression_pair_solutions_card_le_divisor_fibres u0 v0)
  refine card_le_card_of_injOn (fun t => (t/u,(n-t)/v)) ?_ ?_
  · intro t ht
    obtain ⟨h,d₁,d₂⟩ := mem_filter.mp ht
    have tEnd := (mem_Icc.mp h).2
    have tPos := (mem_Icc.mp h).1
    have tN : t ≤ n := by omega
    have right : 1 ≤ n-t := by omega
    have stepL : u*(t/u)=t := Nat.mul_div_cancel' d₁
    have stepR : v*((n-t)/v)=n-t := Nat.mul_div_cancel' d₂
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨?_,?_⟩,mem_Ioc.mpr ⟨?_,?_⟩⟩,?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd tPos d₁) u0
    · exact Nat.div_le_div_right tN
    · exact Nat.div_pos (Nat.le_of_dvd right d₂) v0
    · exact Nat.div_le_div_right (Nat.sub_le _ _)
    · simpa only [stepL,stepR] using Nat.add_sub_of_le tN
  · intro t ht s hs eq
    have h : t/u=s/u := congrArg Prod.fst eq
    rw [← Nat.mul_div_cancel' (mem_filter.mp ht).2.1,
      ← Nat.mul_div_cancel' (mem_filter.mp hs).2.1,h]

private theorem weighted_pair_divisor_sum_le {n t : ℕ} {T : ℝ}
    (t0 : 0 < t) (tn : t ≤ n) (T1 : 1 ≤ T)
    (divs : ∀ r≤n, (r.divisors.card : ℝ) ≤ T) :
    (∑ i ∈ (bilateralLeftWaveItems n).filter (fun i => leftBilinearStep i ∣ t), ‖leftPrimeWeight n i‖) ≤
      T^4*logBudget n := by
  let I := bilateralLeftWaveItems n
  let u := leftBilinearStep
  let F := I.filter (fun i => u i ∣ t)
  have maps (i : ℕ × ℕ) (hi : i ∈ F) : u i ∈ t.divisors :=
    Nat.mem_divisors.mpr ⟨(mem_filter.mp hi).2,t0.ne'⟩
  have h := prime_left_mass_of_subset (filter_subset (fun i => u i ∣ t) I) T1 divs
  change (∑ i ∈ F, ‖leftPrimeWeight n i‖) ≤ _
  rw [← sum_fiberwise_of_maps_to maps]
  calc
    _ ≤ ∑ _ ∈ t.divisors, T^3*logBudget n := sum_le_sum (fun a ha =>
      h a (mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 t0,
        (Nat.le_of_dvd t0 (Nat.mem_divisors.mp ha).1).trans tn⟩))
    _ = (t.divisors.card : ℝ)*(T^3*logBudget n) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ T*(T^3*logBudget n) := mul_le_mul_of_nonneg_right (divs _ tn)
      (mul_nonneg (pow_nonneg (zero_le_one.trans T1) _) (zero_le_one.trans (one_le_logBudget n)))
    _ = _ := by ring

private theorem weighted_right_divisor_sum_le {n t : ℕ} {T : ℝ}
    (t0 : 0 < t) (tn : t ≤ n) (T1 : 1 ≤ T)
    (divs : ∀ r≤n, (r.divisors.card : ℝ) ≤ T) :
    (∑ j ∈ (longRightLowItems n).filter (fun j => rightLowWaveStep j ∣ t), ‖rightLowWaveWeight j‖) ≤
      T^4*logBudget n := by
  let J := longRightLowItems n
  let v := rightLowWaveStep
  let F := J.filter (fun j => v j ∣ t)
  have maps (j : RightLowWaveIndex) (hj : j ∈ F) : v j ∈ t.divisors :=
    Nat.mem_divisors.mpr ⟨(mem_filter.mp hj).2,t0.ne'⟩
  change (∑ j ∈ F, ‖rightLowWaveWeight j‖) ≤ _
  rw [← sum_fiberwise_of_maps_to maps]
  calc
    _ ≤ ∑ _ ∈ t.divisors, T^3*logBudget n := by
      refine sum_le_sum fun a ha => ?_
      have dvd := (Nat.mem_divisors.mp ha).1
      have haN : a ∈ Icc 1 n :=
        mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos dvd t0,(Nat.le_of_dvd t0 dvd).trans tn⟩
      exact (sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (filter_subset _ _))
        (fun _ _ _ => norm_nonneg _)).trans (long_right_low_step_mass T1 divs a haN)
    _ = (t.divisors.card : ℝ)*(T^3*logBudget n) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ T*(T^3*logBudget n) := mul_le_mul_of_nonneg_right (divs _ tn)
      (mul_nonneg (pow_nonneg (zero_le_one.trans T1) _) (zero_le_one.trans (one_le_logBudget n)))
    _ = _ := by ring

theorem norm_inner_low_weighted_divisor_fibre_le {n t : ℕ} {T : ℝ} (ht : t ∈ Icc 1 (n-1))
    (T1 : 1 ≤ T) (divs : ∀ r≤n, (r.divisors.card : ℝ) ≤ T)
    (keep : ℕ × ℕ → RightLowWaveIndex → Prop) :
    ‖∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ longRightLowItems n,
      if leftBilinearStep i ∣ t ∧ rightLowWaveStep j ∣ n-t ∧ keep i j then
        leftPrimeWeight n i*rightLowWaveWeight j else 0‖ ≤ T^8*logBudget n^2 := by
  let a := leftPrimeWeight n
  let b := rightLowWaveWeight
  let I := bilateralLeftWaveItems n
  let J := longRightLowItems n
  let LI := I.filter (fun i => leftBilinearStep i ∣ t)
  let RJ := J.filter (fun j => rightLowWaveStep j ∣ n-t)
  have t0 := (mem_Icc.mp ht).1
  have tLt : t<n := by have h := (mem_Icc.mp ht).2; omega
  have right : 0 < n-t := Nat.sub_pos_of_lt tLt
  have lBound := weighted_pair_divisor_sum_le t0 tLt.le T1 divs
  have rBound := weighted_right_divisor_sum_le right (Nat.sub_le _ _) T1 divs
  let F (i : ℕ × ℕ) (j : RightLowWaveIndex) :=
    if leftBilinearStep i ∣ t ∧ rightLowWaveStep j ∣ n-t ∧ keep i j then a i*b j else 0
  let M (i : ℕ × ℕ) (j : RightLowWaveIndex) :=
    if leftBilinearStep i ∣ t ∧ rightLowWaveStep j ∣ n-t then ‖a i‖*‖b j‖ else 0
  have point (i : ℕ × ℕ) (j : RightLowWaveIndex) : ‖F i j‖ ≤ M i j := by
    by_cases l : leftBilinearStep i ∣ t <;> by_cases r : rightLowWaveStep j ∣ n-t <;>
      by_cases k : keep i j <;> simp [F,M,l,r,k,norm_mul] <;> positivity
  have sumEq : (∑ i ∈ I, ∑ j ∈ J, M i j) =
      (∑ i ∈ LI, ‖a i‖)*(∑ j ∈ RJ, ‖b j‖) := by
    rw [sum_mul_sum]
    unfold LI
    rw [sum_filter]
    refine sum_congr rfl fun i _ => ?_
    by_cases l : leftBilinearStep i ∣ t
    · unfold RJ
      rw [if_pos l,sum_filter]
      refine sum_congr rfl fun j _ => ?_
      simp [M,l]
    · rw [if_neg l]
      exact sum_eq_zero fun j _ => by simp [M,l]
  change ‖∑ i ∈ I, ∑ j ∈ J,F i j‖ ≤ _
  calc
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, ‖F i j‖ := (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ _ := sum_le_sum (fun i _ => sum_le_sum (fun j _ => point i j))
    _ = _ := sumEq
    _ ≤ (T^4*logBudget n)*(T^4*logBudget n) :=
      mul_le_mul lBound rBound (sum_nonneg fun _ _ => norm_nonneg _)
        (mul_nonneg (pow_nonneg (zero_le_one.trans T1) _) (zero_le_one.trans (one_le_logBudget n)))
    _ = _ := by ring

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_inner_low_far_bulk -/
section

namespace GoldbachTypeII13

open Finset DyadicMixedB4EnergyTail
open scoped Classical

noncomputable section

def innerLowEdgeCut (n : ℕ) : ℕ := ⌊(n : ℝ)^(63/64 : ℝ)⌋₊

def innerLowEdgeTargets (n : ℕ) : Finset ℕ :=
  (Icc 1 (n-1)).filter fun t => t ≤ innerLowEdgeCut n ∨ n-t ≤ innerLowEdgeCut n

def innerLowWeightedEdge (P : ℕ → ℕ × ℕ → RightLowWaveIndex → Prop) (n : ℕ) : ℂ :=
  ∑ t ∈ innerLowEdgeTargets n,
    ∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ longRightLowItems n,
      if leftBilinearStep i ∣ t ∧ rightLowWaveStep j ∣ n-t ∧ P n i j then
        leftPrimeWeight n i*rightLowWaveWeight j else 0

theorem saving_inner_low_weighted_edge (P : ℕ → ℕ × ℕ → RightLowWaveIndex → Prop) :
    saving (innerLowWeightedEdge P) := by
  apply saving_of_weil_near_growth _ 2 (by norm_num)
  intro n n1 T T1 divs
  let C := innerLowEdgeCut n
  let F := innerLowEdgeTargets n
  let L := logBudget n
  have nR : (1 : ℝ) ≤ n := by exact_mod_cast n1
  have divN (r : ℕ) (hr : r ≤ n) : (r.divisors.card : ℝ) ≤ T := by
    apply divs r (hr.trans ?_)
    have le : n ≤ n^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (show 1 ≤ 3 by decide)
    omega
  have cover : F ⊆ Icc 1 C ∪ Ico (n-C) n := by
    intro t ht
    have b := mem_Icc.mp (mem_filter.mp ht).1
    obtain ⟨_,h | h⟩ := mem_filter.mp ht
    · exact mem_union.mpr (Or.inl (mem_Icc.mpr ⟨b.1,h⟩))
    · have hC : n-t ≤ C := h
      exact mem_union.mpr (Or.inr (mem_Ico.mpr ⟨by omega,by omega⟩))
  have count : F.card ≤ 2*C := by
    refine (card_le_card cover).trans ((card_union_le ..).trans ?_)
    rw [Nat.card_Icc,Nat.card_Ico]
    omega
  have real_count : (F.card : ℝ) ≤ 2*(n : ℝ)^(8191/8192 : ℝ) := by
    have cast : (F.card : ℝ) ≤ 2*(C : ℝ) := by exact_mod_cast count
    exact cast.trans (mul_le_mul_of_nonneg_left ((Nat.floor_le (by positivity)).trans
      (Real.rpow_le_rpow_of_exponent_le nR (by norm_num))) (by norm_num))
  unfold innerLowWeightedEdge
  calc
    _ ≤ ∑ t ∈ F, ‖∑ i ∈ bilateralLeftWaveItems n, ∑ j ∈ longRightLowItems n,
          if leftBilinearStep i ∣ t ∧ rightLowWaveStep j ∣ n-t ∧ P n i j then
            leftPrimeWeight n i*rightLowWaveWeight j else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ F,T^8*L^2 := sum_le_sum (fun t ht =>
      norm_inner_low_weighted_divisor_fibre_le (mem_filter.mp ht).1 T1 divN (P n))
    _ = (F.card : ℝ)*(T^8*L^2) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ (2*(n : ℝ)^(8191/8192 : ℝ))*(T^9*L^5) := by
      have pwT : T^8 ≤ T^9 := pow_le_pow_right₀ T1 (by decide)
      have pwL : L^2 ≤ L^5 := pow_le_pow_right₀ (one_le_logBudget n) (by decide)
      gcongr
    _ = _ := by ring

def innerLowFarBulkAtom (n u v : ℕ) : ℂ :=
  (((Icc 1 (n-1)).filter
      (fun t => u ∣ t ∧ v ∣ n-t ∧ innerLowEdgeCut n < t ∧ innerLowEdgeCut n < n-t)).card : ℂ)-
    ((u.gcd v : ℝ)*((n : ℝ)/((u : ℝ)*(v : ℝ))) : ℂ)

def innerLowFarBulk (n : ℕ) : ℂ :=
  innerLowFarWeighted n (fun u v => if innerLowFarDiagonalGate n u v then 0 else innerLowFarBulkAtom n u v)

def innerLowFarNonDiagonalPair (n : ℕ) (i : ℕ × ℕ) (j : RightLowWaveIndex) : Prop :=
  innerLowFarGate n i j ∧ ¬innerLowFarDiagonalGate n (leftBilinearStep i) (rightLowWaveStep j)

set_option maxHeartbeats 1400000 in
theorem inner_low_far_off_diagonal_eq_bulk_and_edge (n : ℕ) :
    innerLowFarOffDiagonal n=innerLowFarBulk n+innerLowWeightedEdge innerLowFarNonDiagonalPair n := by
  let I := bilateralLeftWaveItems n
  let J := longRightLowItems n
  let F := innerLowEdgeTargets n
  let P := innerLowFarNonDiagonalPair n
  let u := leftBilinearStep
  let v := rightLowWaveStep
  let w (i : ℕ × ℕ) (j : RightLowWaveIndex) := leftPrimeWeight n i*rightLowWaveWeight j
  let g (i : ℕ × ℕ) (j : RightLowWaveIndex) (t : ℕ) :=
    if u i ∣ t ∧ v j ∣ n-t ∧ P i j then w i j else 0
  have edge_order : innerLowWeightedEdge innerLowFarNonDiagonalPair n =
      ∑ i ∈ I, ∑ j ∈ J, ∑ t ∈ F, g i j t := by
    change (∑ t ∈ F, ∑ i ∈ I, ∑ j ∈ J, g i j t) = _
    rw [sum_comm (s := F) (t := I)]
    exact sum_congr rfl fun _ _ => sum_comm
  rw [edge_order]
  unfold innerLowFarOffDiagonal innerLowFarBulk innerLowFarWeighted
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  have i0 := (mem_Icc.mp (bilateral_left_step_range hi)).1
  have j0 := (mem_Icc.mp (bilateral_right_low_step_range (long_right_low_subset n hj))).1
  let ok := innerLowFarGate n i j
  let dk := innerLowFarDiagonalGate n (u i) (v j)
  by_cases hk : ok <;> by_cases hd : dk
  · dsimp only [ok,dk,u,v] at hk hd
    simp [hk,hd,g,P,innerLowFarNonDiagonalPair]
  · dsimp only [ok,dk,u,v] at hk hd
    rw [if_pos hk,if_pos hk]
    dsimp only
    rw [if_neg hd,if_neg hd]
    have sa : (∑ t ∈ F,g i j t) = w i j * (#(F.filter (fun t => u i ∣ t ∧ v j ∣ n-t)) : ℂ) := by
      have h : P i j := ⟨hk,hd⟩
      simp only [g,h,and_true]
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      ring
    let K := (Icc 1 (n-1)).filter (fun t => u i ∣ t ∧ v j ∣ n-t)
    let E := F.filter (fun t => u i ∣ t ∧ v j ∣ n-t)
    let B := (Icc 1 (n-1)).filter
      (fun t => u i ∣ t ∧ v j ∣ n-t ∧ innerLowEdgeCut n < t ∧ innerLowEdgeCut n < n-t)
    have part : K=B∪E := by
      ext t
      simp only [K,B,E,F,innerLowEdgeTargets,mem_filter,mem_union]
      by_cases h₁ : t ≤ innerLowEdgeCut n <;> by_cases h₂ : n-t ≤ innerLowEdgeCut n <;>
        simp [h₁,h₂,lt_of_not_ge,not_lt_of_ge] <;> omega
    have disj : Disjoint B E := by
      refine disjoint_left.mpr fun t hb he => ?_
      have h := (mem_filter.mp hb).2.2.2
      rcases (mem_filter.mp (mem_filter.mp he).1).2 with left | right
      · exact h.1.not_ge left
      · exact h.2.not_ge right
    have eq : #K=#B+#E := by rw [part,card_union_of_disjoint disj]
    rw [sa]
    unfold innerLowFarAtom innerLowFarBulkAtom
    rw [full_progression_count_eq_divisor_fibres i0 j0]
    change w i j*((#K : ℂ)-_) = w i j*((#B : ℂ)-_)+ w i j*(#E : ℂ)
    rw [eq,Nat.cast_add]
    ring
  · dsimp only [ok,dk,u,v] at hk hd
    simp [hk,hd,g,P,innerLowFarNonDiagonalPair]
  · dsimp only [ok,dk,u,v] at hk hd
    simp [hk,hd,g,P,innerLowFarNonDiagonalPair]

end

end GoldbachTypeII13

end

/- Source PEqualNP.Outside.L_b13_post_noon_inner_low -/
section

namespace GoldbachTypeII13

open DyadicMixedB4EnergyTail

noncomputable section

theorem inner_low_far_diagonal_and_target_edges_saving :
    saving (fun n => innerLowFarCountDiscrepancy n - innerLowFarBulk n) := by
  have small : saving (fun n => innerLowFarDiagonal n + innerLowWeightedEdge innerLowFarNonDiagonalPair n) :=
    saving_sum_two inner_low_far_diagonal_saving (saving_inner_low_weighted_edge innerLowFarNonDiagonalPair)
  have eq (n : ℕ) : innerLowFarCountDiscrepancy n - innerLowFarBulk n =
      innerLowFarDiagonal n + innerLowWeightedEdge innerLowFarNonDiagonalPair n := by
    rw [inner_low_far_discrepancy_split, inner_low_far_off_diagonal_eq_bulk_and_edge]
    abel
  rw [funext eq]
  exact small

end

end GoldbachTypeII13

end

end B13InnerLowFarDiagonalAndEdgesSavingProof

set_option maxHeartbeats 4000000 in
theorem Conjectures.Goldbach.B13InnerLowFarDiagonalAndEdgesSaving :
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
    let edge := fun n : ℕ => ⌊(n : ℝ)^(63/64 : ℝ)⌋₊
    let C := fun (n g h : ℕ) => ((Finset.Icc 1 (n-1)).filter
      (fun t => g ∣ t ∧ h ∣ n-t ∧ edge n < t ∧ edge n < n-t)).card
    let diagonal := fun (n g h : ℕ) =>
      g ≤ h+⌊(n : ℝ)^(2/5 : ℝ)⌋₊ ∧ h ≤ g+⌊(n : ℝ)^(2/5 : ℝ)⌋₊
    let farCount := fun n : ℕ =>
      ∑ i ∈ X n, ∑ j ∈ longLow n,
        let g := u i
        let h := vl j
        @ite ℂ (lowKept n g h ∧ g.gcd h ∣ n ∧ ¬(g*h ≤ narrowProduct n)) (Classical.propDecidable _)
          (w n i*((-(μ j.2 : ℂ))*(Λ j.1 : ℂ))*
            (@ite ℂ (diagonal n g h) (Classical.propDecidable _) 0
              ((C n g h : ℂ) - ((g.gcd h : ℝ)*((n : ℝ)/((g : ℝ)*(h : ℝ))) : ℂ)))) 0
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
      ‖farRaw n-farCount n‖ ≤ e*(n : ℝ) := by
  exact B13InnerLowFarDiagonalAndEdgesSavingProof.GoldbachTypeII13.inner_low_far_diagonal_and_target_edges_saving
