# Compact-open cylinder descent in spectral limits

Import `SpectralStoneDuality.LimitCylinderDescent`. Let `J` be a small cofiltered
category, `F : J ⥤ TopCat.{max v u}` a diagram whose objects are spectral spaces
and whose transition maps are spectral, and `i : J`. The public theorems are:

- `SpectralStoneDuality.limitCylinder_subset_iff_eventually F i hX hmap C hC U V hUopen hUcompact hVopen`:
  for a **supplied actual cone** `C : Cone F` and its limit witness
  `hC : IsLimit C`, the inclusion
  `C.π.app i ⁻¹' U ⊆ C.π.app i ⁻¹' V` holds if and only if there is an
  `X : Over i` with `F.map X.hom ⁻¹' U ⊆ F.map X.hom ⁻¹' V`. Here `U` is
  open and compact and `V` is open; both stage preimages are subsets of
  `F.obj X.left`.
- `SpectralStoneDuality.chosenLimitCylinder_subset_iff_eventually` states the
  same equivalence for the chosen limit projection `limit.π F i` when
  `[HasLimit F]` is available.
- `SpectralStoneDuality.exists_compactOpen_eventually_full F i hX hmap C hC U hUopen hRange`:
  if the range of `C.π.app i` lies in an open set `U`, there is an open,
  compact `W` containing that range, contained in `U`, and an `X : Over i`
  such that `F.map X.hom ⁻¹' W = Set.univ`.

No stage needs to be nonempty, no transition map needs to be surjective, and
the limit cone may have an empty vertex. In particular, the eventually-full
conclusion is meaningful even when the chosen stage is empty. Named actual-cone,
neighborhood and chosen-limit clients are in
[`Examples/LimitCylinderDescent.lean`](../Examples/LimitCylinderDescent.lean),
the second explicit root of `SpectralStoneDualityExamples`.

## Proof and existing APIs

If no stage witnesses cylinder containment, every locally closed counterexample
set `F.map X.hom ⁻¹' U \ F.map X.hom ⁻¹' V` is nonempty. Spectrality of the
transitions makes its compact-open part compact, so the counterexample set is
compact and locally closed. The private subspace lemmas establish its
retrocompactness, quasi-separatedness, and quasi-sobriety and thereby its
spectrality. The restricted maps remain spectral by the existing
`SpectralStoneDuality.isSpectralMap_to_subtype_of_comp` API. The existing
`SpectralStoneDuality.nonempty_limit_of_spectral` theorem yields a compatible
counterexample family over `Over i`. Initiality of `Over.forget i` and the
**supplied** `hC` send that family into `C.pt`, contradicting the cylinder
containment. The reverse direction follows from the cone triangle.

For the neighborhood theorem, the existing
`SpectralStoneDuality.compactSpace_limit_of_spectral` result and the canonical
homeomorphism between the concrete limit and `C.pt` make the projection range
compact. Compact-open interpolation supplies `W`; cylinder descent for
`Set.univ` and `W` supplies the eventually-full stage. The existing spectral
limit and compact-open basis APIs are reused, not re-proved.

At this Lean/mathlib pin the published `constructibleDiagram` definition is
not `@[expose]`. A downstream module cannot identify its object types
definitionally with `WithConstructibleTopology` for the closed-counterexample
construction. The present proof uses locally closed spectral subspaces instead;
exposing the diagram is only a possible separately reviewed maintenance change,
not a prerequisite or an additional dependency of this API.

## Origin and scope

The compact locally closed, closed-embedding/quasiseparation and counterexample
set/diagram/map/cone proofs **closely adapt original project Lean expression**
by Anchor (source maintainer). A collaborating Formal Frontier agent assembled
the reusable actual-cone `hC`, chosen-limit and eventually-full interfaces,
clients and this guide; a separate contributor adapted the paths and namespaces
for this library without changing the mathematical proof payloads. Anchor
registered the public import and example root. This is substantive expression
reuse, not merely mathematical inspiration. See the [credits](CREDITS.md) for
project origin and third-party attribution; no source-book excerpt or source
research checkout is imported.

The results allow empty stages and nonsurjective arrows and do not establish a
source-coverage milestone or a sheaf-section theorem. Review, proof-integrity
and release evidence apply to exact candidate revisions, not to this guide.
