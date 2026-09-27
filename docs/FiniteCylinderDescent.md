<!-- SPDX-License-Identifier: Apache-2.0 -->

# Finite compact-open cylinder descent

Import `SpectralStoneDuality.FiniteCylinderDescent`. For a small cofiltered
category `J : Type v`, a diagram `D : J ⥤ TopCat.{max v u}` with spectral
stage spaces and spectral transition maps, and an **actual specified**
`C : Cone D` with `hC : IsLimit C`, the following API works for every
`i : J` and every `[Finite α]`. The indexing type `α` may be empty; no
stage or limit is assumed inhabited, and transition maps need not be surjective.

- `SpectralStoneDuality.exists_finiteCompactOpen_cylinders D C hC hX hmap i U hU`
  returns `X : Over i` and compact opens `V a` on `D.obj X.left` such that
  every *labelled* compact open `U a` is exactly
  `(Opens.map (C.π.app X.left)).obj (V a)`.
- `SpectralStoneDuality.finiteCylinder_subset_eventually D C hC hX hmap i A B hA hAB`
  turns finitely many inclusions of inverse images of compact-open `A a`
  into open `B a` under `C.π.app i` into simultaneous inclusions under
  `D.map X.hom` for **one** `X : Over i`.
- `SpectralStoneDuality.exists_finiteCompactOpen_fullStageCover D C hC hX hmap i U A hU hCover hTarget`
  descends a finite compact-open cover `⨆ a, U a = ⊤` of `C.pt` into a
  finite compact-open cover `⨆ a, V a = ⊤` of an **entire** stage. It preserves
  `U a = (Opens.map (C.π.app X.left)).obj (V a)` and enforces
  `V a ≤ (Opens.map (D.map X.hom)).obj (A a)` for every label.

`Examples.FiniteCylinderDescent` provides four import-only named clients for
these actual-cone interfaces in
`SpectralStoneDualityExamples.FiniteCylinder`. Its empty-family client deduces
an eventual empty stage when the supplied limit is empty: the empty cover
has no labelled opens and is **not** treated as an impossible case.

## Proof and dependency boundaries

The private single-compact-open helper applies mathlib's
`eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open` to the existing
`SpectralStoneDuality.compactOpenCylinders_isBasis` for the specified cone.
`IsCofiltered.inf_objs_exists` moves the finitely many basis cylinders to
one stage and unions their compact-open pullbacks. A further common stage
keeps all family labels and supplies an arrow to `i`. For simultaneous
containment, the published parent theorem
`SpectralStoneDuality.limitCylinder_subset_iff_eventually` supplies a stage
for each label; mathlib's `IsCofiltered.wideCospan` supplies **commuting
triangles** for the finite family of arrows into `i`, not merely arrows to
their domains. Finally the first two results align the labelled cover and
targets; applying parent cylinder descent to `univ` and the finite union
forces the cover to equal the entire later stage.

The parent `SpectralStoneDuality.LimitCylinderDescent` is integrated at
deliverable commit `ec25325f882df909055d62e61c390066aec91ad9`, tree
`9f6a8b5a8639398f1fc3f956d26ab3dd95bc204c`, and separately published
at official GitHub release `5e2cf4120087d32b1456e0244de46741d85dc83d`
with the same tree. This project pins Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and the published
`ideal-completion` dependency at `001e3b7508184ecd51e0d86177cb1d54508bf59d`.
This module adds no incubator or source-research dependency, sheaf construction,
native colimit `IsIso` endpoint, or source-coverage claim.

## Provenance and status

The accepted **source** is the focused, unregistered incubator leaf
`bd82bf269e4d16bc2ca9bd8f312e0af50649869d`, tree
`80079c8d57bd95312c1032b68a8d15a3e322f2fd`, comprising the producer,
four named clients and guide. Its author is worker-b Hive Task
`hive-request-1365e777e728ab94ed1310b0b8cf71258cc1e36b`, UID
`89236f48-cfbf-4aa2-a592-5b4eaaa8469e`. Its independent source review
is by worker-a Hive Task
`hive-request-465a3f8e6bef790c3343e1e017d44821174bb338`, UID
`d7eee5b0-115e-4a5d-998b-887adb1695fb`, at review commit
`937e38cd68edeadc846fbcc5fd4549eef86828b6` in
`reviews/finite-cylinder-descent/REVIEW.md`. Anchor leaf-accepted that
source at incubator issue #4 comment 52349; this does not register it in
incubator roots or accept this destination transfer.

The private single-cylinder finite-subcover, common-stage, pullback-union
and cone-triangle steps, and the finite labelled common-stage selection,
**closely adapt original project Lean proof expression** by Anchor from
`source-fujiwara-kato-rigid-geometry-i` commit
`e266a5076df34934171cc284ba8f2834e56f8c78`:
`Research/fk-cofiltered-compact-opens-scratch.lean` (blob
`d1fc65316460737e6ca28d0189af3e135680a477`) and
`Research/fk-proposition-3-1-10-finite-stage-descent-probe.lean` (blob
`2ae99dbfc3bdc9f197ce8e3c81a7059146e05ee8`). These are original
project proof expressions, **not merely ideas**, and are credited as such;
they are not imports or accepted source correspondence. The coherent
`wideCospan` argument and whole-stage cover assembly are the new
source-independent contribution. The separate parent cylinder theorem
credits its worker-b author Task
`hive-request-c9b24d2f4bdfa0523394f9dd6727fa4247db6fa1`, UID
`f8bccb81-3bb8-40fd-bb6c-dfe216caabaa`, and its own original Anchor
proof donors in `docs/LimitCylinderDescent.md`. Both Lean payloads retain
their Apache-2.0 SPDX and collective author notices.

This **destination adapter** is by worker-a Hive Task
`hive-request-797a8df70fd7324d0d13e121375992410210e406`, UID
`8754cac4-b56b-4795-93bc-17323f7314d6`, under Anchor as responsible
maintainer in spectral-stone-duality issue #17. It transfers the source
proofs without changing their mathematics. Anchor's subsequent source-only
registration retains both Lean blobs from `77b6f14`, adds the aggregate public
import and a **third explicit Examples root**, and updates documentation,
credits and metadata. This fourteen-module destination candidate remains
**unaccepted**. The cache-first focused producer and direct-client builds and
seven-producer/four-client standard-axiom origin checks are separate from the
new combined-root required CI. Retained unsupported Lake-j and missing output-
directory trials are failures, not successful checks. Fresh independent
destination review, owner acceptance, full applicable checks, integration,
verified official release, and reviewed incubator replacement remain separate
gates. No Fujiwara--Kato source milestone or sheaf-section theorem is decided.
