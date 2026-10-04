/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Spectral.Basic

public section

set_option warningAsError true

/-!
# Compact-open cylinder bases for cofiltered limits

Inverse images of compact opens along the components of any specified limiting
cone form an `Opens.IsBasis`. The chosen-limit version uses the actual `limit.π`
maps, and the directed version uses stages indexed by a nonempty directed
preorder. No nonemptiness of the stage spaces or the limit is needed.

## References

- Mathlib, `Topology.Category.TopCat.Limits.Cofiltered` and
  `Topology.Spectral.Basic`, for the cofiltered-limit basis theorem and
  compact-open stage bases. The specified-cone and chosen-limit open-cylinder
  interfaces refine this existing formalization.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

noncomputable section

namespace SpectralStoneDuality

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable (D : J ⥤ TopCat.{max v u}) (C : Cone D)

/-- A stage of a diagram together with a compact open at that stage. -/
@[expose]
def compactOpenCylinderIndex :=
  Σ j : J, {U : Opens (D.obj j) // IsCompact (U : Set (D.obj j))}

/-- The inverse image of a compact open under a specified cone projection. -/
@[expose]
def compactOpenCylinder (k : compactOpenCylinderIndex D) : Opens C.pt :=
  (Opens.map (C.π.app k.1)).obj k.2.1

/-- Compact-open stage cylinders form a basis for any specified limiting cone. -/
theorem compactOpenCylinders_isBasis (hC : IsLimit C)
    (hX : ∀ j, SpectralSpace (D.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (D.map f)) :
    Opens.IsBasis (Set.range (compactOpenCylinder D C)) := by
  let _ (j : J) : SpectralSpace (D.obj j) := hX j
  have hNative : IsTopologicalBasis
      {W : Set C.pt | ∃ (j : J) (V : Set (D.obj j)),
        (IsOpen V ∧ IsCompact V) ∧ W = C.π.app j ⁻¹' V} := by
    apply TopCat.isTopologicalBasis_cofiltered_limit D C hC
      (fun j ↦ {V : Set (D.obj j) | IsOpen V ∧ IsCompact V})
    · intro j
      exact PrespectralSpace.isTopologicalBasis
    · intro j
      exact ⟨isOpen_univ, isCompact_univ⟩
    · intro j U V hU hV
      exact ⟨hU.1.inter hV.1, hU.2.inter_of_isOpen hV.2 hU.1 hV.1⟩
    · intro i j f V hV
      exact ⟨hV.1.preimage (hmap f).continuous,
        (hmap f).isCompact_preimage_of_isOpen hV.1 hV.2⟩
  change IsTopologicalBasis
    (((↑) : Opens C.pt → Set C.pt) '' Set.range (compactOpenCylinder D C))
  convert hNative using 1
  ext W
  constructor
  · rintro ⟨_, ⟨⟨j, ⟨U, hUc⟩⟩, rfl⟩, rfl⟩
    exact ⟨j, U, ⟨U.isOpen, hUc⟩, rfl⟩
  · rintro ⟨j, V, ⟨hVo, hVc⟩, rfl⟩
    let U : Opens (D.obj j) := ⟨V, hVo⟩
    exact ⟨compactOpenCylinder D C ⟨j, ⟨U, hVc⟩⟩,
      ⟨⟨j, ⟨U, hVc⟩⟩, rfl⟩, rfl⟩

/-- A compact-open stage cylinder on the actual chosen limit of a diagram. -/
@[expose]
def chosenLimitCompactOpenCylinder [HasLimit D]
    (k : compactOpenCylinderIndex D) : Opens ((limit D : TopCat.{max v u})) :=
  (Opens.map (limit.π D k.1)).obj k.2.1

/-- Compact-open cylinders form a basis on the chosen limit, using its `limit.π`. -/
theorem chosenLimitCompactOpenCylinders_isBasis [HasLimit D]
    (hX : ∀ j, SpectralSpace (D.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (D.map f)) :
    Opens.IsBasis (Set.range (chosenLimitCompactOpenCylinder D)) := by
  exact compactOpenCylinders_isBasis D (limit.cone D) (limit.isLimit D) hX hmap

variable {I : Type v} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- An index for compact-open cylinders of an inverse system over `Iᵒᵖ`. -/
@[expose]
def directedCompactOpenCylinderIndex (E : Iᵒᵖ ⥤ TopCat.{v}) :=
  Σ i : I, {U : Opens (E.obj (op i)) // IsCompact (U : Set (E.obj (op i)))}

/-- A cylinder indexed by `I`, using the actual chosen-limit projection. -/
@[expose]
def directedCompactOpenCylinder (E : Iᵒᵖ ⥤ TopCat.{v}) [HasLimit E]
    (k : directedCompactOpenCylinderIndex E) : Opens ((limit E : TopCat.{v})) :=
  (Opens.map (limit.π E (op k.1))).obj k.2.1

/-- For a nonempty directed preorder, chosen-limit stage cylinders form a basis. -/
theorem directedCompactOpenCylinders_isBasis (E : Iᵒᵖ ⥤ TopCat.{v}) [HasLimit E]
    (hX : ∀ i : I, SpectralSpace (E.obj (op i)))
    (hmap : ∀ {a b : Iᵒᵖ} (f : a ⟶ b), IsSpectralMap (E.map f)) :
    Opens.IsBasis (Set.range (directedCompactOpenCylinder E)) := by
  let _ : IsFiltered I := isFiltered_of_directed_le_nonempty I
  have h := chosenLimitCompactOpenCylinders_isBasis E
    (fun j ↦ hX (unop j)) hmap
  convert h using 1
  ext U
  constructor
  · rintro ⟨⟨i, V⟩, rfl⟩
    exact ⟨⟨op i, V⟩, rfl⟩
  · rintro ⟨⟨j, V⟩, rfl⟩
    exact ⟨⟨unop j, V⟩, rfl⟩

end SpectralStoneDuality
