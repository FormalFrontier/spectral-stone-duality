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

The [single-cylinder module](LimitCylinderDescent.md) supplies the containment
and eventually-full arguments. Mathlib supplies the finite compact-open
subcover and cofiltered-refinement formalizations used here. The finite
subcover and common-stage argument follows the technique in Fujiwara and
Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5, Chapter 0,
§2.2(c), Proposition 2.2.9; their proposition does not state the labelled
whole-stage-cover theorem. These results do not supply a sheaf gluing or
section-colimit `IsIso` endpoint.

## Origin and scope

The single-cylinder finite-subcover, common-stage, pullback-union and
cone-triangle Lean proofs and finite labelled selection closely adapt
Anchor's original project expression. Other Formal Frontier contributors
developed the finite-family interfaces, coherent `wideCospan` argument and
whole-stage cover. The [credits](CREDITS.md) distinguish this project
expression from Mathlib's formalization and Fujiwara–Kato's mathematical
technique. No book asset or excerpt is included.

These statements include empty label families and potentially empty stages;
they do not prove a sheaf gluing theorem.
