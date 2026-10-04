# Spectral Stone duality

A Lean library for prime-ideal spectra, the contravariant equivalence of bounded
distributive lattices with spectral spaces, and compact-open topology of spectral
limits and arbitrary subspaces. It also provides the soberification of any
topological space. Import the whole library with `import SpectralStoneDuality`
or select one of its twenty-one leaves below.

## Headline results

- **Prime spectrum and compact opens.** For a bounded distributive lattice `A`,
  [`PrimeIdealSpectrum`](SpectralStoneDuality/PrimeSpectrum.lean) consists of prime
  **order ideals**. The opens `D(I)` are primes *not containing* the ideal `I`;
  every open arises this way, and `D(I)` is compact (quasi-compact, not
  necessarily Hausdorff) exactly when `I` is principal. Specialization is
  inclusion of prime ideals. The trivial lattice is permitted and has an empty
  spectrum. See the [spectrum guide](docs/Guide.md#prime-spectra-and-the-open-set-convention).
- **Spectral Stone duality.** Bounded lattice homomorphisms induce contravariant
  spectral maps; compact opens recover the lattice, and points of a spectral
  space are recovered from its compact-open lattice. The natural equivalence is
  [`SpectralStoneDuality.stoneDuality : BddDistLatᵒᵖ ≌ SpectralCat`](SpectralStoneDuality/Equivalence.lean).
  Its space-side reconstruction uses sobriety; it does not assert a duality for
  arbitrary spaces. See [maps and reconstruction](docs/Guide.md#maps-reconstruction-and-naturality).
- **Finite compact-open reconstruction.** At each finite set of compact opens,
  realized membership patterns form a finite spectral space with its Sierpiński
  product-subtype topology. Restriction maps are continuous and surjective.
  Evaluation into compatible families induces the topology when compact opens
  form a basis. It is injective when compact opens form a basis and the space
  is `T₀`. It is surjective when compact opens form a basis and the space is
  compact, quasi-separated and quasi-sober; this does not require `T₀`.
  Thus [`spaceHomeomorph`](SpectralStoneDuality/FiniteCoordinates.lean) identifies
  any spectral space with its compatible finite patterns. The compatible-family
  cone is limiting for any topological space, and the point-evaluation cone is
  limiting for spectral spaces; see [finite-coordinate limits](SpectralStoneDuality/FiniteCoordinates/Limits.lean)
  and the [finite-coordinate guide](docs/Guide.md#finite-compact-open-coordinates).
- **Thin-lattice finite coproducts.** In the order category of a distributive
  lattice with bottom, finite joins are universal coproducts without requiring
  a top element. In any lattice with bottom, a finite coproduct is disjoint
  exactly when summands at distinct indices have meet bottom. Such disjoint
  coproducts stay disjoint after base change in the distributive case; every
  finite coproduct's injections generate a covering sieve for the extensive
  topology. This does
  not assert that every finite coproduct is disjoint or that the category is
  `FinitaryExtensive`. See [thin lattices](SpectralStoneDuality/CategoryTheory/Lattice/Extensive.lean).
- **Finite preservation and lattice maps.** A functor between the order
  categories of bounded lattices preserves finite limits and finite colimits
  exactly when its object map is a bounded lattice homomorphism. The two maps
  recover each other; no distributivity or shared carrier universe is needed.
  Empty diagrams detect top and bottom, while binary discrete diagrams detect
  meets and joins. See [preservation](SpectralStoneDuality/CategoryTheory/Lattice/Preserves.lean).
- **Soberification.** For any topological space, the topology on its nonempty
  irreducible closed subsets yields a `T₀` quasi-sober space. The unit sends
  a point to its singleton closure; continuous maps into `T₀` quasi-sober
  spaces extend uniquely, giving a left adjoint to their inclusion in `TopCat`.
  No separation, compactness or spectrality is required of the input. This
  general-topology reflection is separate from the spectral-space
  reconstruction in Stone duality. See [topology](SpectralStoneDuality/Topology/Soberification.lean)
  and [adjunction](SpectralStoneDuality/Topology/Category/Soberification.lean).
- **Finite quasi-sobriety.** Every finite irreducible subset of any topological
  space contains a generic point of its closure. In particular, every finite
  topological space is quasi-sober, including the empty space and spaces that
  are not `T₀`; sobriety additionally requires `T₀`. See
  [finite topology](SpectralStoneDuality/Topology/Finite.lean).
- **Cofinite quasi-sobriety.** `CofiniteTopology.quasiSober_iff_finite X`
  characterizes quasi-sobriety by `Finite X`, without a nonemptiness
  hypothesis: empty and finite cofinite spaces are sober, whereas an infinite
  cofinite space is `T₁` but not quasi-sober. See [cofinite topology](SpectralStoneDuality/Topology/Cofinite.lean).
- **Closed points among generizations.** In any `T₀` space, the original point
  is the unique closed point of its generization subspace `nhdsKer {x}`:
  [`isClosed_singleton_nhdsKer_iff`](SpectralStoneDuality/Topology/NhdsKer.lean)
  characterizes every closed singleton in that subspace. No sobriety or
  spectrality is needed. See [closed generizations](docs/Guide.md#closed-generizations).
- **Limits and cylinder bases.** Small cofiltered diagrams of spectral spaces
  with **spectral transition maps** have spectral limits and spectral
  projections. Compact-open inverse-image cylinders form a basis for a supplied
  `IsLimit` cone or the chosen limit. The separate limit-nonemptiness theorem
  additionally assumes every stage nonempty; the basis results do not.
  See [limits](SpectralStoneDuality/Limits.lean) and the
  [cylinder-basis supplement](docs/CompactOpenBasis.md).
- **Maps of cofiltered spectral limits.** Given a natural transformation of
  small cofiltered diagrams with spectral source and target stages, spectral
  source transitions, spectral component maps, and arbitrary supplied `IsLimit`
  cones, the induced map is spectral when target transitions are spectral
  (`isSpectralMap_isLimit_map`), surjective when each component is surjective
  (`surjective_isLimit_map`), and closed when each component is a closed map
  (`isClosedMap_isLimit_map`). Surjectivity and closedness do not require spectral
  target transitions; no result assumes nonempty stages or Hausdorff spaces.
  See [limit maps](SpectralStoneDuality/LimitMaps.lean).
- **Subspaces and descent.** A compact open of *any* subspace of a prespectral
  space lifts to an ambient compact open; closedness is unnecessary. A map to
  that subspace is spectral when its composite with the inclusion is spectral.
  For an actual limiting cone, compact-open/merely-open cylinder containment
  descends over an `Over` witness. Finite, possibly empty, labelled families
  descend coherently, including whole-stage covers. These results do not require
  surjective arrows or inhabited stages, and do not construct sheaves or their
  gluing. See [subspaces](SpectralStoneDuality/Subspace.lean),
  [single-cylinder descent](docs/LimitCylinderDescent.md) and
  [finite-cylinder descent](docs/FiniteCylinderDescent.md).
- **Compact locally closed subspaces.** Inducing spectral maps into prespectral
  quasi-separated spaces preserve quasi-separatedness without injectivity.
  A compact locally closed subset is retrocompact, and its ordinary subtype
  is prespectral, compact and quasi-separated, even when the ambient space is
  not compact. These conclusions do not assert sobriety. See
  [locally closed topology](SpectralStoneDuality/Topology/LocallyClosed.lean).

## Modules and examples

| Public leaf (`SpectralStoneDuality.*`) | Main interface |
| --- | --- |
| [`PrimeSpectrum`](SpectralStoneDuality/PrimeSpectrum.lean) | Prime order ideals, `D(I)`, specialization, compact opens |
| [`Functoriality`](SpectralStoneDuality/Functoriality.lean) | Contravariant `spectrumComap`, `compactOpenOrderIso` |
| [`Category`](SpectralStoneDuality/Category.lean) | `SpectralCat` with spectral-map morphisms and both functors |
| [`Reconstruction`](SpectralStoneDuality/Reconstruction.lean) | `spaceToSpectrum`, `spaceSpectrumHomeomorph`, `spaceUnitIso` |
| [`FiniteCoordinates`](SpectralStoneDuality/FiniteCoordinates.lean) | Realized finite Sierpiński coordinates, restrictions and spectral-space homeomorphism |
| [`FiniteCoordinates.Limits`](SpectralStoneDuality/FiniteCoordinates/Limits.lean) | Compatible-family limit cones for all spaces and evaluation limit cones for spectral spaces |
| [`Equivalence`](SpectralStoneDuality/Equivalence.lean) | `stoneDuality` |
| [`Limits`](SpectralStoneDuality/Limits.lean) | Cofiltered spectral limits, projections and set bases |
| [`LimitMaps`](SpectralStoneDuality/LimitMaps.lean) | Spectral, surjective and closed maps of supplied cofiltered limit cones |
| [`CompactOpenBasis`](SpectralStoneDuality/CompactOpenBasis.lean) | Open-cylinder bases for actual cones and chosen limits |
| [`Subspace`](SpectralStoneDuality/Subspace.lean) | Ambient compact-open lifts and spectral-map detection |
| [`Topology.LocallyClosed`](SpectralStoneDuality/Topology/LocallyClosed.lean) | Inducing spectral maps and compact locally closed subspaces |
| [`LimitCylinderDescent`](SpectralStoneDuality/LimitCylinderDescent.lean) | Eventual containment and eventually-full neighborhoods |
| [`FiniteCylinderDescent`](SpectralStoneDuality/FiniteCylinderDescent.lean) | Coherent finite families and whole-stage covers |
| [`Topology.NhdsKer`](SpectralStoneDuality/Topology/NhdsKer.lean) | Unique closed point among generizations in a `T₀` space |
| [`CategoryTheory.Lattice.Extensive`](SpectralStoneDuality/CategoryTheory/Lattice/Extensive.lean) | Universal finite joins, conditional disjointness and extensive-topology coverings |
| [`CategoryTheory.Lattice.Preserves`](SpectralStoneDuality/CategoryTheory/Lattice/Preserves.lean) | Finite-(co)limit preservation, bounded lattice maps and their equivalence |
| [`Topology.Soberification`](SpectralStoneDuality/Topology/Soberification.lean) | Irreducible-closed topology, unit, open-set equivalence and universal extension |
| [`Topology.Category.Soberification`](SpectralStoneDuality/Topology/Category/Soberification.lean) | Reflective `SoberTopCat` and soberification adjunction |
| [`Topology.Finite`](SpectralStoneDuality/Topology/Finite.lean) | Generic points of finite irreducible sets; finite-space quasi-sobriety |
| [`Topology.Cofinite`](SpectralStoneDuality/Topology/Cofinite.lean) | Cofinite quasi-sobriety iff finiteness, infinite obstruction |

The [aggregate import](SpectralStoneDuality.lean) publicly re-exports these
leaves. The three existing example modules are
[`Examples/SpectralStoneDuality.lean`](Examples/SpectralStoneDuality.lean),
[`Examples/LimitCylinderDescent.lean`](Examples/LimitCylinderDescent.lean), and
[`Examples/FiniteCylinderDescent.lean`](Examples/FiniteCylinderDescent.lean).
The separately built
[`SpectralStoneDualityExamples/Soberification.lean`](SpectralStoneDualityExamples/Soberification.lean)
exercises the reflection on empty and non-separated spaces, `Prop` and the
infinite cofinite space. The
[`SpectralStoneDualityExamples/LatticeExtensive.lean`](SpectralStoneDualityExamples/LatticeExtensive.lean)
clients cover finite disjoint families, base change and a non-disjoint repeated
summand. The [closed-generization examples](SpectralStoneDualityExamples/NhdsKer.lean)
contrast the upper-set topology on two points with an indiscrete space.
The [finite-preservation examples](SpectralStoneDualityExamples/LatticePreserves.lean)
test identity, a nonconstant Boolean-square projection, the one-element lattice,
and constant maps that preserve binary operations but fail a nullary law.
The [cofinite examples](SpectralStoneDualityExamples/Cofinite.lean) test the
empty space, discrete two-point space, and infinite irreducible Nat space.
The [finite-space examples](SpectralStoneDualityExamples/FiniteSobriety.lean)
contrast the existing discrete-space route with finite quasi-sobriety on `Prop`
and indiscrete `Bool`, and test the infinite cofinite obstruction.
The [locally closed examples](SpectralStoneDualityExamples/LocallyClosed.lean)
test empty and proper finite subspaces, a noninjective inducing map on a non-`T₀`
space, and a compact subset of an infinite discrete space.
The [finite-coordinate examples](SpectralStoneDualityExamples/FiniteCoordinates.lean)
include empty and singleton spaces, Sierpiński patterns, a non-`T₀` surjectivity
case, nonquotient finite stages and strict three-point refinements.
The [finite-coordinate limit examples](SpectralStoneDualityExamples/FiniteCoordinateLimits.lean)
test empty and non-`T₀` boundaries and identify canonical lifts for indiscrete
two-point and spectral Sierpiński spaces.
The [limit-map examples](SpectralStoneDualityExamples/LimitMaps.lean) exercise
the induced-map theorems on finite spectral stages, including a surjection onto
a two-point space, a nonsurjective closed-point map into non-Hausdorff
Sierpiński space, and an empty-domain boundary.
These are separate example modules, not exported by
`SpectralStoneDuality`. `Examples.SpectralStoneDuality` exposes the public theorem
`SpectralStoneDualityExamples.natRefinement`; its other named clients remain private. The
[mathematical guide](docs/Guide.md) gives conventions and proof outlines.

## Build and documentation

Install [elan](https://github.com/leanprover/elan); this repository pins Lean
`v4.34.0-rc2`, mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`
and the officially published `ideal-completion` dependency
`001e3b7508184ecd51e0d86177cb1d54508bf59d`. The resolved graph is in
[`lake-manifest.json`](lake-manifest.json). The ideal-completion GitHub
repository is private; building requires authorized access. Fetch the matching
precompiled mathlib cache **before** a build, including after changing pins or
replacing `.lake`; stop and diagnose if the cache fetch fails:

```sh
lake exe cache get
lake --wfail build
```

The default build includes the library and the `SpectralStoneDualityExamples`
target, whose [example roots are listed in the Guide](docs/Guide.md).
Following the same cache prerequisite,
`lake --wfail build SpectralStoneDualityExamples` selects the example target.
A successful build alone does not check transitive axiom dependencies. Build
and complete private-inclusive axiom-audit evidence applies when the relevant
Lean source, build targets and configuration, resolved dependencies, toolchain
and checker inputs and required coverage match. A prose-only commit needs no
repeat proof checks; renew only affected checks for changed inputs or missing
coverage.

The [API reference](docs/API.md) contains **99 historical native display sites
from seven leaves**, not a current census of all declarations or modules.
The later cylinder leaves have [manual cylinder-basis](docs/CompactOpenBasis.md),
[single-cylinder](docs/LimitCylinderDescent.md) and
[finite-cylinder](docs/FiniteCylinderDescent.md) supplements. The native output's
body and [fixed input/output manifest](docs/api-manifest.json) describe an
earlier snapshot: the manifest's API hash does not cover this reference's later
introduction or the aggregate, Examples and Lake inputs in this checkout. The
[reproduction notes](docs/README.md) distinguish analyzed and translated
inputs and show how to use the older public snapshot; the fixed adapter cannot
certify the changed inputs in this checkout.

In an earlier nine-source snapshot, a cache fetch took 95.087 s, a build
14.013 s and a separate public-import client 3.004 s under a 23-GiB whole-job
cgroup. A distinct cached default build took 15 s under a 15-GiB cgroup; its
pre-existing cgroup `memory.peak` included cache-download page cache and cannot
isolate build memory. Native doc-gen `single` steps took 2.5–3.1 s each and
`fromDb` took 1.27 s **excluding setup**. About 7.8 GiB of cached dependency
storage is a disk observation, not a RAM requirement. These historical
observations are not portable limits: they used an older internal
ideal-completion commit with the same dependency tree and do not measure a
fetch or build at the official GitHub pin.

## Attribution and scope

Authors: Formal Frontier Agents. Original project contributions are licensed
under [Apache-2.0](LICENSE). This collective authorship does not identify a
copyright holder or suggest endorsement by the source authors. Lean and mathlib
provide foundational order, topology and category APIs; the separately
maintained ideal-completion library provides ideal-completion results.
[Credits and provenance](docs/CREDITS.md) distinguish original Anchor
expression, subsequent project adaptations and independent dependency authors.

Fujiwara and Kato, *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5), Chapter 0, §2.2,
is a motivating reference, not a claim of full source formalization. No source
PDF or excerpt is bundled. Coverage and source-specific correspondence belong
in the source repository, not in this reusable library.
