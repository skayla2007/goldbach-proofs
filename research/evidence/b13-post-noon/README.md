# B13 residual energy equivalence

`Conjectures.Goldbach.B13FrozenIffThreeEnergyEstimates` gives both directions between the frozen B13 proposition and the conjunction of the three proposed energy estimates. Each proposition in its type is written out in full. The proof uses the four-block signed reduction and the three low-interior savings. It applies the square to the joint residual.

The Lean file contains its supporting proofs and imports Mathlib. The companion `.statement` is the expected type for the independent checker. The route tasks each use one of the three conjuncts.

## Reproduce the check

From the repository's `lean` directory with its pinned toolchain and Mathlib cache:

```bash
lake exe cache get
lake build checklemma
src=../research/evidence/b13-post-noon/lean
build=$(mktemp -d)
module=Conjectures/Goldbach/B13FrozenIffThreeEnergyEstimates
mkdir -p "$build/Conjectures/Goldbach"
lake env lean --root="$src" --tstack=400000 -DautoImplicit=false \
  -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -DmaxHeartbeats=4000000 \
  -o "$build/$module.olean" "$src/$module.lean"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"
  "$2" Conjectures.Goldbach.B13FrozenIffThreeEnergyEstimates "$3" check' \
  _ "$build" .lake/build/bin/checklemma ../research/evidence/b13-post-noon/equivalence.statement
```

The supporting sources record their provenance next to their statements and definitions. The reference Lean file retains the modular-hyperbola code's Apache 2.0 attribution.
