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
neighborhood and chosen-limit clients are in `Examples.LimitCylinderDescent`.
The registration successor publicly imports this module and lists the client
as a second root of `SpectralStoneDualityExamples`. Its final combined check
and independent acceptance remain pending; the original three-file transfer
was unregistered and checked only with focused commands.

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

## Provenance and promotion status

This source-independent transfer is based on the accepted focused incubator
candidate `b0c2b67f44310e2abad89e812a04172592c968a5` (unregistered,
`Incubator/Topology/Spectral/LimitCylinderDescent.lean`,
`IncubatorTest/Topology/Spectral/LimitCylinderDescent.lean`, and
`docs/SpectralLimitCylinderDescent.md`). Its author is worker-b Hive Task
`hive-request-c9b24d2f4bdfa0523394f9dd6727fa4247db6fa1` (UID
`f8bccb81-3bb8-40fd-bb6c-dfe216caabaa`), with Anchor as the responsible
maintainer. The independent review of that exact incubator leaf is
`0eb83dd046b791185b16b932d00f2c430ffa1370`,
`reviews/spectral-limit-cylinder-descent/REVIEW.md` (incubator issue #4).

The private compact-locally-closed, closed-embedding/quasiseparation, and
counterexample set/diagram/map/cone constructions **closely adapt original
project Lean proof expression** by Anchor (Source Maintainer) from
`FormalFrontier/source-fujiwara-kato-rigid-geometry-i` commit
`e266a5076df34934171cc284ba8f2834e56f8c78`: the donor files are
`Research/fk-corollary-2-2-12-scratch.lean` (blob
`86d58bc1699023362be296e965d3ad49140d1eca`) and
`Research/fk-proposition-2-2-3-scratch.lean` (blob
`f08a995d77489a4c1c61a39d0378151d2d7f2e89`). The worker-b
contribution assembles the source-independent public API, the actual-cone
`hC` argument, chosen-limit and eventual-full results, clients, and guide.
Neither donor research file is imported; the donor research is not accepted
source coverage. No source PDF, transcript, or external work is copied here.
The Lean files retain the project Apache-2.0 SPDX and collective author notices.

This destination adaptation is by worker-a Hive Task
`hive-request-7345db7f02bcee5f6f46b45998f9b368443171e9` (UID
`48bbab48-63ad-4f73-bfbc-4d7253e886f8`) from destination base
`2f72af0e938b89ce85a4b667027646d54f785231`. It changes only the
module paths and namespaces of the two Lean payloads, not their statements
or proofs. The destination already includes the requisite producer APIs;
mathlib is pinned at `83abb3e776bdefcbc447a1e44d0debe4010039e5`
and the official `ideal-completion` dependency at
`001e3b7508184ecd51e0d86177cb1d54508bf59d`.

**Registered promotion candidate only:** the root/example configuration is now
present, but destination acceptance, full applicable checks, independent
destination review, protected integration,
and verified official deliverable release remain pending. The later incubator
replacement with the exact official dependency also remains pending. Neither
this transfer nor the incubator acceptance establishes a source milestone,
source-root acceptance, or source-formalization decision.
