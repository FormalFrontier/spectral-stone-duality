/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.LimitCylinderDescent
public import SpectralStoneDuality.CompactOpenBasis
public import Mathlib.Topology.Compactness.Bases

public section

set_option warningAsError true

/-!
# Finite compact-open cylinders over a specified spectral limit

Finite families of compact opens of an actual limiting cone descend together to
one stage. Finite containments of compact-open cylinders into open cylinders
also hold together at one stage, with coherent arrows in a cofiltered category.
These facts give a finite, compact-open whole-stage cover respecting target opens.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.2(c), Proposition 2.2.9, for the finite-subcover and common-stage
  argument behind compact-open descent. The labelled finite-family and
  whole-stage covering statements are stronger interfaces, not source claims.
- Mathlib, `Topology.Compactness.Bases` and `CategoryTheory.Filtered.Basic`,
  for finite compact-open subcovers and coherent cofiltered refinements.
-/

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u v

noncomputable section

namespace SpectralStoneDuality

variable {J : Type v} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ TopCat.{max v u}) (C : Cone D)

omit [IsCofiltered J] in
private theorem cylinder_comp {j k : J} (f : j ⟶ k)
    (U : Opens (D.obj k)) :
    (Opens.map (C.π.app j)).obj ((Opens.map (D.map f)).obj U) =
      (Opens.map (C.π.app k)).obj U := by
  rw [← Opens.map_comp_obj, C.w f]

omit [IsCofiltered J] in
private theorem compactOpen_preimage
    (hmap : ∀ {j k : J} (f : j ⟶ k), IsSpectralMap (D.map f))
    {j k : J} (f : j ⟶ k) (U : Opens (D.obj k))
    (hU : IsCompact (U : Set (D.obj k))) :
    IsCompact ((Opens.map (D.map f)).obj U : Set (D.obj j)) := by
  change IsCompact ((D.map f) ⁻¹' (U : Set (D.obj k)))
  exact hU.preimage_of_isOpen (hmap f) U.isOpen

private theorem exists_compactOpen_cylinder (hC : IsLimit C)
    (hX : ∀ j, SpectralSpace (D.obj j))
    (hmap : ∀ {j k : J} (f : j ⟶ k), IsSpectralMap (D.map f))
    (U : Opens C.pt) (hU : IsCompact (U : Set C.pt)) :
    ∃ (j : J) (V : Opens (D.obj j)), IsCompact (V : Set (D.obj j)) ∧
      U = (Opens.map (C.π.app j)).obj V := by
  classical
  let b (k : SpectralStoneDuality.compactOpenCylinderIndex D) : Set C.pt :=
    SpectralStoneDuality.compactOpenCylinder D C k
  have hBasis : IsTopologicalBasis (Set.range b) := by
    have hb := SpectralStoneDuality.compactOpenCylinders_isBasis D C hC hX hmap
    change IsTopologicalBasis
      (((↑) : Opens C.pt → Set C.pt) ''
        Set.range (SpectralStoneDuality.compactOpenCylinder D C)) at hb
    convert hb using 1
    ext T
    simp [b]
  obtain ⟨s, hsFinite, hUnion⟩ :=
    eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open
      b hBasis (U : Set C.pt) hU U.isOpen
  let _ : Fintype s := hsFinite.fintype
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists
    (Finset.univ.image (fun k : s ↦ k.1.1))
  let arrow (k : s) : j ⟶ k.1.1 :=
    (hj (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)).some
  let V : Opens (D.obj j) :=
    ⨆ k : s, (Opens.map (D.map (arrow k))).obj k.1.2.1
  have hCylinder (k : s) :
      (Opens.map (C.π.app j)).obj
          ((Opens.map (D.map (arrow k))).obj k.1.2.1) =
        SpectralStoneDuality.compactOpenCylinder D C k.1 :=
    cylinder_comp D C (arrow k) k.1.2.1
  refine ⟨j, V, ?_, ?_⟩
  · simpa only [V, Opens.coe_iSup] using
      (isCompact_iUnion fun k : s ↦ compactOpen_preimage D hmap
        (arrow k) k.1.2.1 k.1.2.2)
  · have hOpen : U = ⨆ k : s, SpectralStoneDuality.compactOpenCylinder D C k.1 := by
      apply SetLike.coe_injective
      simpa only [Opens.coe_iSup, Set.iUnion_subtype, b] using hUnion
    calc
      U = ⨆ k : s, SpectralStoneDuality.compactOpenCylinder D C k.1 := hOpen
      _ = ⨆ k : s, (Opens.map (C.π.app j)).obj
            ((Opens.map (D.map (arrow k))).obj k.1.2.1) := by
        apply iSup_congr
        intro k
        exact (hCylinder k).symm
      _ = (Opens.map (C.π.app j)).obj V := by
        simp only [V, Opens.map_iSup, Function.comp_def]

/-- A finite, possibly empty, labelled family of compact opens of an actual
limiting cone is the pullback of compact opens at one stage over `i`. -/
theorem exists_finiteCompactOpen_cylinders {α : Type*} [Finite α]
    (hC : IsLimit C) (hX : ∀ j, SpectralSpace (D.obj j))
    (hmap : ∀ {j k : J} (f : j ⟶ k), IsSpectralMap (D.map f))
    (i : J) (U : α → Opens C.pt)
    (hU : ∀ a, IsCompact (U a : Set C.pt)) :
    ∃ (X : Over i) (V : α → Opens (D.obj X.left)),
      (∀ a, IsCompact (V a : Set (D.obj X.left))) ∧
      ∀ a, U a = (Opens.map (C.π.app X.left)).obj (V a) := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  have hOne (a : α) := exists_compactOpen_cylinder D C hC hX hmap (U a) (hU a)
  choose stage V hV using hOne
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists
    (insert i (Finset.univ.image stage))
  let q : k ⟶ i := (hk (Finset.mem_insert_self i _)).some
  let arrow (a : α) : k ⟶ stage a :=
    (hk (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨a, Finset.mem_univ a, rfl⟩))).some
  refine ⟨Over.mk q, fun a ↦ (Opens.map (D.map (arrow a))).obj (V a), ?_, ?_⟩
  · intro a
    exact compactOpen_preimage D hmap (arrow a) (V a) (hV a).1
  · intro a
    exact (hV a).2.trans (cylinder_comp D C (arrow a) (V a)).symm

/-- A finite family of compact-open to open cylinder inclusions is witnessed
simultaneously at a single coherent stage over `i`. -/
theorem finiteCylinder_subset_eventually {α : Type*} [Finite α]
    (hC : IsLimit C) (hX : ∀ j, SpectralSpace (D.obj j))
    (hmap : ∀ {j k : J} (f : j ⟶ k), IsSpectralMap (D.map f))
    (i : J) (A B : α → Opens (D.obj i))
    (hA : ∀ a, IsCompact (A a : Set (D.obj i)))
    (hAB : ∀ a, (Opens.map (C.π.app i)).obj (A a) ≤
      (Opens.map (C.π.app i)).obj (B a)) :
    ∃ X : Over i, ∀ a,
      (Opens.map (D.map X.hom)).obj (A a) ≤
        (Opens.map (D.map X.hom)).obj (B a) := by
  classical
  have hOne (a : α) : ∃ X : Over i,
      D.map X.hom ⁻¹' (A a : Set (D.obj i)) ⊆
        D.map X.hom ⁻¹' (B a : Set (D.obj i)) :=
    (limitCylinder_subset_iff_eventually D i hX hmap C hC
      (A a : Set (D.obj i)) (B a : Set (D.obj i))
      (A a).isOpen (hA a) (B a).isOpen).mp (hAB a)
  choose X hStage using hOne
  obtain ⟨k, fki, arrow, hcomm⟩ :=
    IsCofiltered.wideCospan (fun a : α ↦ (X a).hom)
  refine ⟨Over.mk fki, ?_⟩
  intro a
  change D.map fki ⁻¹' (A a : Set (D.obj i)) ⊆
    D.map fki ⁻¹' (B a : Set (D.obj i))
  rw [← hcomm a, D.map_comp]
  intro x hx
  exact hStage a hx

/-- A finite compact-open cover of a supplied spectral limit, subordinate to
target opens at one stage, descends to a whole-stage compact-open cover.
The conclusion also applies to the empty family and an empty limit. -/
theorem exists_finiteCompactOpen_fullStageCover {α : Type*} [Finite α]
    (hC : IsLimit C) (hX : ∀ j, SpectralSpace (D.obj j))
    (hmap : ∀ {j k : J} (f : j ⟶ k), IsSpectralMap (D.map f))
    (i : J) (U : α → Opens C.pt) (A : α → Opens (D.obj i))
    (hU : ∀ a, IsCompact (U a : Set C.pt))
    (hCover : ⨆ a, U a = ⊤)
    (hTarget : ∀ a, U a ≤ (Opens.map (C.π.app i)).obj (A a)) :
    ∃ (X : Over i) (V : α → Opens (D.obj X.left)),
      (∀ a, IsCompact (V a : Set (D.obj X.left))) ∧
      (⨆ a, V a) = ⊤ ∧
      (∀ a, U a = (Opens.map (C.π.app X.left)).obj (V a)) ∧
      ∀ a, V a ≤ (Opens.map (D.map X.hom)).obj (A a) := by
  classical
  obtain ⟨X, V, hV, hCylinder⟩ :=
    exists_finiteCompactOpen_cylinders D C hC hX hmap i U hU
  let B (a : α) : Opens (D.obj X.left) := (Opens.map (D.map X.hom)).obj (A a)
  have hAtX (a : α) : (Opens.map (C.π.app X.left)).obj (V a) ≤
      (Opens.map (C.π.app X.left)).obj (B a) := by
    rw [← hCylinder a, cylinder_comp D C X.hom (A a)]
    exact hTarget a
  obtain ⟨Y, hY⟩ := finiteCylinder_subset_eventually D C hC hX hmap
    X.left V B hV hAtX
  let W (a : α) : Opens (D.obj Y.left) :=
    (Opens.map (D.map Y.hom)).obj (V a)
  have hWCylinder (a : α) : U a =
      (Opens.map (C.π.app Y.left)).obj (W a) :=
    (hCylinder a).trans (cylinder_comp D C Y.hom (V a)).symm
  have hWTarget (a : α) : W a ≤
      (Opens.map (D.map (Y.hom ≫ X.hom))).obj (A a) := by
    simpa only [W, B, ← Opens.map_comp_obj, ← D.map_comp] using hY a
  have hLimitCover : (Opens.map (C.π.app Y.left)).obj (⨆ a, W a) = ⊤ := by
    rw [Opens.map_iSup]
    calc
      (⨆ a, (Opens.map (C.π.app Y.left)).obj (W a)) = ⨆ a, U a := by
        apply iSup_congr
        intro a
        exact (hWCylinder a).symm
      _ = ⊤ := hCover
  let _ : SpectralSpace (D.obj Y.left) := hX Y.left
  have hLimitInclusion : (C.π.app Y.left) ⁻¹' (Set.univ : Set (D.obj Y.left)) ⊆
      (C.π.app Y.left) ⁻¹'
        ((⨆ a, W a : Opens (D.obj Y.left)) : Set (D.obj Y.left)) := by
    intro x _
    have hx : x ∈ (Opens.map (C.π.app Y.left)).obj (⨆ a, W a) := by
      rw [hLimitCover]
      trivial
    exact hx
  obtain ⟨Z, hZ⟩ := (limitCylinder_subset_iff_eventually D Y.left hX hmap
    C hC Set.univ (⨆ a, W a : Opens (D.obj Y.left))
    isOpen_univ isCompact_univ (⨆ a, W a).isOpen).mp hLimitInclusion
  let T (a : α) : Opens (D.obj Z.left) :=
    (Opens.map (D.map Z.hom)).obj (W a)
  have hStageCover : (⨆ a, T a) = ⊤ := by
    have hTop : (Opens.map (D.map Z.hom)).obj (⨆ a, W a) = ⊤ := by
      apply top_unique
      intro x _
      exact hZ (Set.mem_univ x)
    simpa only [T, Opens.map_iSup, Function.comp_def] using hTop
  refine ⟨Over.mk (Z.hom ≫ Y.hom ≫ X.hom), T, ?_, hStageCover, ?_, ?_⟩
  · intro a
    exact compactOpen_preimage D hmap Z.hom (W a)
      (compactOpen_preimage D hmap Y.hom (V a) (hV a))
  · intro a
    exact (hWCylinder a).trans (cylinder_comp D C Z.hom (W a)).symm
  · intro a
    have hPull := (Opens.map (D.map Z.hom)).map (homOfLE (hWTarget a))
    have hLe : T a ≤ (Opens.map (D.map Z.hom)).obj
        ((Opens.map (D.map (Y.hom ≫ X.hom))).obj (A a)) := hPull.le
    simpa only [Over.mk_left, Over.mk_hom, T,
      ← Opens.map_comp_obj, ← D.map_comp, Category.assoc] using hLe

end SpectralStoneDuality
