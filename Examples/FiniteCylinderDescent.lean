/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.FiniteCylinderDescent

public section

set_option warningAsError true

/-!
# External clients of finite spectral-cylinder descent

These named clients use the public family API with a supplied actual limiting
cone. No client assumes the sought stage, arrows, or descended opens.
-/

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u v

namespace SpectralStoneDualityExamples.FiniteCylinder

theorem actualCone_finiteCompactOpen_labels
    {J : Type v} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ TopCat.{max v u}) (C : Cone D) (hC : IsLimit C)
    (hX : ∀ j, SpectralSpace (D.obj j))
    (hmap : ∀ {j k : J} (f : j ⟶ k), IsSpectralMap (D.map f))
    (i : J) {α : Type*} [Finite α] (U : α → Opens C.pt)
    (hU : ∀ a, IsCompact (U a : Set C.pt)) :
    ∃ (X : Over i) (V : α → Opens (D.obj X.left)),
      (∀ a, IsCompact (V a : Set (D.obj X.left))) ∧
      ∀ a, U a = (Opens.map (C.π.app X.left)).obj (V a) :=
  SpectralStoneDuality.exists_finiteCompactOpen_cylinders D C hC hX hmap i U hU

theorem actualCone_finiteCylinder_containment
    {J : Type v} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ TopCat.{max v u}) (C : Cone D) (hC : IsLimit C)
    (hX : ∀ j, SpectralSpace (D.obj j))
    (hmap : ∀ {j k : J} (f : j ⟶ k), IsSpectralMap (D.map f))
    (i : J) {α : Type*} [Finite α] (A B : α → Opens (D.obj i))
    (hA : ∀ a, IsCompact (A a : Set (D.obj i)))
    (hAB : ∀ a, (Opens.map (C.π.app i)).obj (A a) ≤
      (Opens.map (C.π.app i)).obj (B a)) :
    ∃ X : Over i, ∀ a,
      (Opens.map (D.map X.hom)).obj (A a) ≤
        (Opens.map (D.map X.hom)).obj (B a) :=
  SpectralStoneDuality.finiteCylinder_subset_eventually D C hC hX hmap
    i A B hA hAB

theorem actualCone_finiteCompactOpen_fullStageCover
    {J : Type v} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ TopCat.{max v u}) (C : Cone D) (hC : IsLimit C)
    (hX : ∀ j, SpectralSpace (D.obj j))
    (hmap : ∀ {j k : J} (f : j ⟶ k), IsSpectralMap (D.map f))
    (i : J) {α : Type*} [Finite α]
    (U : α → Opens C.pt) (A : α → Opens (D.obj i))
    (hU : ∀ a, IsCompact (U a : Set C.pt))
    (hCover : ⨆ a, U a = ⊤)
    (hTarget : ∀ a, U a ≤ (Opens.map (C.π.app i)).obj (A a)) :
    ∃ (X : Over i) (V : α → Opens (D.obj X.left)),
      (∀ a, IsCompact (V a : Set (D.obj X.left))) ∧
      (⨆ a, V a) = ⊤ ∧
      (∀ a, U a = (Opens.map (C.π.app X.left)).obj (V a)) ∧
      ∀ a, V a ≤ (Opens.map (D.map X.hom)).obj (A a) :=
  SpectralStoneDuality.exists_finiteCompactOpen_fullStageCover D C hC hX hmap
    i U A hU hCover hTarget

/-- An empty compact-open family on an empty actual limit descends to an empty
stage, not a contradiction or a hidden inhabitance assumption. -/
theorem actualCone_emptyFamily_eventually_empty
    {J : Type v} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ TopCat.{max v u}) (C : Cone D) (hC : IsLimit C)
    (hX : ∀ j, SpectralSpace (D.obj j))
    (hmap : ∀ {j k : J} (f : j ⟶ k), IsSpectralMap (D.map f))
    (i : J) [IsEmpty C.pt] :
    ∃ X : Over i, IsEmpty (D.obj X.left) := by
  have hCover : (⨆ a : Empty, (isEmptyElim a : Opens C.pt)) = ⊤ := by
    apply top_unique
    intro x _
    exact isEmptyElim x
  obtain ⟨X, V, _hV, hFull, _hCylinder, _hTarget⟩ :=
    actualCone_finiteCompactOpen_fullStageCover D C hC hX hmap i
      (fun a : Empty ↦ isEmptyElim a) (fun a : Empty ↦ isEmptyElim a)
      (fun a ↦ isEmptyElim a) hCover (fun a ↦ isEmptyElim a)
  refine ⟨X, ⟨fun x ↦ ?_⟩⟩
  have hx : x ∈ (⨆ a : Empty, V a) := by
    rw [hFull]
    trivial
  simp at hx

end SpectralStoneDualityExamples.FiniteCylinder
