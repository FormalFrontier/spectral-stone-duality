# Examples for Spectral Stone duality

The [aggregate import](../SpectralStoneDuality.lean) publicly re-exports the library
leaves described in the [module table](../README.md#modules-and-examples). The three existing example modules are
[`Examples/SpectralStoneDuality.lean`](../Examples/SpectralStoneDuality.lean),
[`Examples/LimitCylinderDescent.lean`](../Examples/LimitCylinderDescent.lean), and
[`Examples/FiniteCylinderDescent.lean`](../Examples/FiniteCylinderDescent.lean).
The separately built
[`SpectralStoneDualityExamples/GenericPointRemoval.lean`](../SpectralStoneDualityExamples/GenericPointRemoval.lean)
compares discrete incidence boundaries with non-discrete complements and
exhibits a noninjective gluing map.
The [generic-point reindexing examples](../SpectralStoneDualityExamples/GenericPointReindex.lean)
test empty, singleton, two-point permutation and universe-lifted closed-point
indices. These points belong to the independent fork, not to a topology
inherited by any ambient endpoint set.
The [subspace specialization examples](../SpectralStoneDualityExamples/SubspaceStrictSpecializations.lean)
compare ambient and relative boundaries in a proper closed component of a
non-`T₀` space and give independent containment and genericity obstructions.
The separately built
[`SpectralStoneDualityExamples/Soberification.lean`](../SpectralStoneDualityExamples/Soberification.lean)
exercises the reflection on empty and non-separated spaces, `Prop` and the
infinite cofinite space. The
[`SpectralStoneDualityExamples/LatticeExtensive.lean`](../SpectralStoneDualityExamples/LatticeExtensive.lean)
clients cover finite disjoint families, base change and a non-disjoint repeated
summand. The [closed-generization examples](../SpectralStoneDualityExamples/NhdsKer.lean)
contrast the upper-set topology on two points with an indiscrete space.
The [finite-preservation examples](../SpectralStoneDualityExamples/LatticePreserves.lean)
test identity, a nonconstant Boolean-square projection, the one-element lattice,
and constant maps that preserve binary operations but fail a nullary law.
The [cofinite examples](../SpectralStoneDualityExamples/Cofinite.lean) test the
empty space, discrete two-point space, and infinite irreducible Nat space.
The [finite-space examples](../SpectralStoneDualityExamples/FiniteSobriety.lean)
contrast the existing discrete-space route with finite quasi-sobriety on `Prop`
and indiscrete `Bool`, and test the infinite cofinite obstruction.
The [locally closed examples](../SpectralStoneDualityExamples/LocallyClosed.lean)
test empty and proper finite subspaces, a noninjective inducing map on a non-`T₀`
space, and a compact subset of an infinite discrete space.
The [constructible-subspace examples](../SpectralStoneDualityExamples/ConstructibleSubspace.lean)
include empty and whole subspaces and a proper constructibly closed subset of
the non-Hausdorff two-point upper-set space that is not generization-stable.
In an infinite Boolean product, compact-open cylinders have a non-open
intersection.
The [finite-coordinate examples](../SpectralStoneDualityExamples/FiniteCoordinates.lean)
include empty and singleton spaces, Sierpiński patterns, a non-`T₀` surjectivity
case, nonquotient finite stages and strict three-point refinements.
The [finite-coordinate limit examples](../SpectralStoneDualityExamples/FiniteCoordinateLimits.lean)
test empty and non-`T₀` boundaries and identify canonical lifts for indiscrete
two-point and spectral Sierpiński spaces.
The [limit-map examples](../SpectralStoneDualityExamples/LimitMaps.lean) exercise
the induced-map theorems on finite spectral stages, including a surjection onto
a two-point space, a nonsurjective closed-point map into non-Hausdorff
Sierpiński space, and an empty-domain boundary.
These are separate example modules, not exported by
`SpectralStoneDuality`. `Examples.SpectralStoneDuality` exposes the public theorem
`SpectralStoneDualityExamples.natRefinement`; its other named clients remain private. The
[mathematical guide](Guide.md) gives conventions and proof outlines.
