/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.LimitCylinderDescent

public section

set_option warningAsError true

/-!
# Direct clients of eventual cylinder descent

These named theorems exercise the public API for a supplied limiting cone and
for the chosen limit. Neither client assumes nonempty stages or surjective maps.
-/

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u v

namespace SpectralStoneDualityExamples.Cylinder

theorem actualCone_compactOpenCylinder_descends
    {J : Type v} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u}) (C : Cone F) (hC : IsLimit C)
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    (i : J) (U V : Set (F.obj i))
    (hUopen : IsOpen U) (hUcompact : IsCompact U) (hVopen : IsOpen V)
    (hLimit : C.π.app i ⁻¹' U ⊆ C.π.app i ⁻¹' V) :
    ∃ X : Over i, F.map X.hom ⁻¹' U ⊆ F.map X.hom ⁻¹' V :=
  (SpectralStoneDuality.limitCylinder_subset_iff_eventually F i hX hmap
    C hC U V hUopen hUcompact hVopen).mp hLimit

theorem actualCone_neighborhood_eventually_full
    {J : Type v} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u}) (C : Cone F) (hC : IsLimit C)
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    (i : J) (U : Set (F.obj i)) (hUopen : IsOpen U)
    (hRange : Set.range (C.π.app i) ⊆ U) :
    ∃ W : Opens (F.obj i), IsCompact (W : Set (F.obj i)) ∧
      Set.range (C.π.app i) ⊆ W ∧ (W : Set (F.obj i)) ⊆ U ∧
      ∃ X : Over i, F.map X.hom ⁻¹' (W : Set (F.obj i)) = Set.univ := by
  obtain ⟨W, hWopen, hWcompact, hRangeW, hWU, X, hXW⟩ :=
    SpectralStoneDuality.exists_compactOpen_eventually_full F i hX hmap
      C hC U hUopen hRange
  exact ⟨⟨W, hWopen⟩, hWcompact, hRangeW, hWU, X, hXW⟩

theorem chosenLimit_compactOpenCylinder_descends
    {J : Type v} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u}) [HasLimit F]
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {a b : J} (f : a ⟶ b), IsSpectralMap (F.map f))
    (i : J) (U V : Set (F.obj i))
    (hUopen : IsOpen U) (hUcompact : IsCompact U) (hVopen : IsOpen V) :
    (limit.π F i) ⁻¹' U ⊆ (limit.π F i) ⁻¹' V ↔
      ∃ X : Over i, F.map X.hom ⁻¹' U ⊆ F.map X.hom ⁻¹' V :=
  SpectralStoneDuality.chosenLimitCylinder_subset_iff_eventually F i hX hmap
    U V hUopen hUcompact hVopen

end SpectralStoneDualityExamples.Cylinder
