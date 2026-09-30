# Compact-open cylinder bases: manual API supplement

This supplement documents the eight public declarations in
[`SpectralStoneDuality.CompactOpenBasis`](../SpectralStoneDuality/CompactOpenBasis.lean).
Import that module directly, or `import SpectralStoneDuality` for the aggregate
public API. This module was added **after** the frozen seven-leaf native doc-gen4
input; none of its names occurs in the 99 native display records in
[`API.md`](API.md) or the historical [`api-manifest.json`](api-manifest.json).
The declarations here are documented manually, not newly generated doc-gen4
records. The [API reproduction notes](README.md) explain why the historical
manifest does not enumerate this module; use the imports above for its actual
interfaces rather than inferring an absence from native display counts.

## Specified cofiltered limiting cone

Fix `J : Type v`, `[Category.{w} J]`, a diagram
`D : J ⥤ TopCat.{max v u}` and a **specified** `C : Cone D`. The three
declarations in `SpectralStoneDuality` are:

| Declaration | Interface |
| --- | --- |
| `compactOpenCylinderIndex D` | `Σ j : J, {U : Opens (D.obj j) // IsCompact (U : Set (D.obj j))}` |
| `compactOpenCylinder D C k` | An `Opens C.pt`, defined by `(Opens.map (C.π.app k.1)).obj k.2.1` for `k : compactOpenCylinderIndex D` |
| `compactOpenCylinders_isBasis D C hC hX hmap` | `Opens.IsBasis (Set.range (compactOpenCylinder D C))` |

The two definitions require only the category and diagram (and `C` for the
cylinder); cofilteredness is needed **only for the theorem**. The basis theorem
requires `[IsCofiltered J]`, `hC : IsLimit C`,
`hX : ∀ j, SpectralSpace (D.obj j)`, and
`hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (D.map f)`.
Its proof applies mathlib's native cofiltered-limit set-basis theorem to
compact opens at each stage and identifies its sets with the coercions of
the cylinder opens. It does **not** identify `C` with a particular concrete
model of the limit, assume nonempty stage spaces or strengthen the topology.

## Chosen categorical limit

With the same diagram and category parameters, additionally assume
`[HasLimit D]`. Then
`chosenLimitCompactOpenCylinder D k : Opens ((limit D : TopCat.{max v u}))`
is the inverse image of the compact open in `k` along `limit.π D k.1`.
The definition does not require cofilteredness. The theorem
`chosenLimitCompactOpenCylinders_isBasis D hX hmap` additionally requires
`[IsCofiltered J]` and says
`Opens.IsBasis (Set.range (chosenLimitCompactOpenCylinder D))` using the
same spectral-stage and spectral-arrow hypotheses. Its proof applies the
specified-cone theorem to `limit.cone D` and `limit.isLimit D`; this is a
statement about the actual chosen limit and literal `limit.π`.

## Directed inverse systems

Fix `I : Type v` with `[Preorder I]`.
For `E : Iᵒᵖ ⥤ TopCat.{v}`, the declarations are:

| Declaration | Interface |
| --- | --- |
| `directedCompactOpenCylinderIndex E` | `Σ i : I, {U : Opens (E.obj (op i)) // IsCompact (U : Set (E.obj (op i)))}` |
| `directedCompactOpenCylinder E k` | For `[HasLimit E]`, an `Opens ((limit E : TopCat.{v}))`, pulled back along `limit.π E (op k.1)` |
| `directedCompactOpenCylinders_isBasis E hX hmap` | For `[HasLimit E]`, `Opens.IsBasis (Set.range (directedCompactOpenCylinder E))` |

The two definitions require only `[Preorder I]` (and `[HasLimit E]` for the
cylinder). The basis theorem additionally requires `[IsDirectedOrder I]` and
`[Nonempty I]`. Here `hX : ∀ i : I, SpectralSpace (E.obj (op i))` and
`hmap : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsSpectralMap (E.map f)`.
Directedness and nonemptiness of the **index** imply `IsFiltered I` and hence
cofilteredness of `Iᵒᵖ`; these are not assumptions that the stages are
inhabited. The basis is a reindexing of the chosen-limit basis by `op`/`unop`.
In particular, the import-only [examples](../Examples/SpectralStoneDuality.lean)
instantiate a constant diagram with empty stage spaces without asserting a
point of its limit, and obtain a pointwise refinement for an arbitrary
`Natᵒᵖ` diagram conditional on a given point.

This API is distinct from the `Limits` module's compact-open **set** basis on
`TopCat.limitCone`: no declaration or proof in `Limits` was changed.
