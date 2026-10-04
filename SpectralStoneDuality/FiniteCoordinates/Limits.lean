/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.FiniteCoordinates
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Finite-coordinate cones

Finite families of compact opens form a diagram of realized Sierpiński patterns: an inclusion
`F ⊆ G` induces a restriction from the stage at `G` to the stage at `F`. Compatible families
and point evaluations give cones over this diagram. Compatible families form a limit cone
for any topological space; point evaluations form a limit cone for spectral spaces.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace SpectralStoneDuality.FiniteCoordinates

variable {X : Type u} [TopologicalSpace X]

/-- The contravariant diagram of realized finite compact-open membership patterns. -/
def stageDiagram (X : Type u) [TopologicalSpace X] :
    (Finset (CompactOpens X))ᵒᵖ ⥤ TopCat.{u} where
  obj F := TopCat.of (Stage F.unop)
  map {F G} f := TopCat.ofHom ⟨restrict (leOfHom f.unop), continuous_restrict _⟩
  map_id F := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro v
    exact congrFun (restrict_id (X := X) F.unop) v
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro v
    exact (congrFun (restrict_comp (X := X) (leOfHom g.unop) (leOfHom f.unop)) v).symm

@[simp] theorem stageDiagram_obj (F : (Finset (CompactOpens X))ᵒᵖ) :
    (stageDiagram X).obj F = TopCat.of (Stage F.unop) := rfl

@[simp] theorem stageDiagram_map_apply {F G : (Finset (CompactOpens X))ᵒᵖ}
    (f : F ⟶ G) (v : Stage F.unop) :
    (stageDiagram X).map f v = restrict (leOfHom f.unop) v := rfl

/-- Compatible families, with their stage projections, form a cone. -/
def familyCone (X : Type u) [TopologicalSpace X] : Cone (stageDiagram X) where
  pt := TopCat.of (Family X)
  π := {
    app := fun F => TopCat.ofHom
      ⟨fun z => z.1 F.unop, (continuous_apply F.unop).comp continuous_subtype_val⟩
    naturality := by
      intro F G f
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      exact (Family.restrict_apply z G.unop F.unop (leOfHom f.unop)).symm }

@[simp] theorem familyCone_π_apply (F : (Finset (CompactOpens X))ᵒᵖ)
    (z : Family X) : (familyCone X).π.app F z = z.1 F.unop := rfl

/-- Projecting a compatible family after forgetting coordinates agrees with projecting
directly to the smaller stage. -/
theorem familyCone_restrict_apply {F G : Finset (CompactOpens X)} (hFG : F ⊆ G)
    (z : Family X) :
    (stageDiagram X).map (homOfLE hFG).op
        ((familyCone X).π.app (Opposite.op G) z) =
      (familyCone X).π.app (Opposite.op F) z :=
  congrArg
    (fun f : (familyCone X).pt ⟶ (stageDiagram X).obj (Opposite.op F) => f z)
    ((familyCone X).w (homOfLE hFG).op)

/-- The map to compatible families induced by any cone of finite stages. -/
def familyLift (c : Cone (stageDiagram X)) : c.pt ⟶ TopCat.of (Family X) :=
  TopCat.ofHom {
    toFun := fun x => ⟨fun F => c.π.app (Opposite.op F) x, fun F G hFG => by
      have h := congrArg (fun f : c.pt ⟶ (stageDiagram X).obj (Opposite.op F) => f x)
        (c.w (homOfLE hFG).op)
      change restrict hFG (c.π.app (Opposite.op G) x) =
        c.π.app (Opposite.op F) x at h
      exact h⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_pi fun F => (c.π.app (Opposite.op F)).hom.continuous }

@[simp] theorem familyLift_apply (c : Cone (stageDiagram X)) (x : c.pt)
    (F : Finset (CompactOpens X)) : (familyLift c x).1 F = c.π.app (Opposite.op F) x := rfl

/-- The constructed lift commutes with all finite-stage projections. -/
theorem familyLift_fac (c : Cone (stageDiagram X)) (F : (Finset (CompactOpens X))ᵒᵖ) :
    familyLift c ≫ (familyCone X).π.app F = c.π.app F := by
  ext x
  rfl

/-- The compatible-family cone is limiting for any topological space. -/
noncomputable def familyConeIsLimit (X : Type u) [TopologicalSpace X] :
    IsLimit (familyCone X) := by
  refine ⟨familyLift, familyLift_fac, ?_⟩
  intro c m hm
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply Family.ext
  intro F
  have h := congrArg
    (fun f : c.pt ⟶ (stageDiagram X).obj (Opposite.op F) => f x)
    (hm (Opposite.op F))
  exact h

/-- Point evaluation at every finite stage forms a cone. -/
def evaluationCone (X : Type u) [TopologicalSpace X] : Cone (stageDiagram X) where
  pt := TopCat.of X
  π := {
    app := fun F => TopCat.ofHom ⟨point F.unop, continuous_point _⟩
    naturality := by
      intro F G f
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      exact (restrict_point (leOfHom f.unop) x).symm }

@[simp] theorem evaluationCone_π_apply (F : (Finset (CompactOpens X))ᵒᵖ)
    (x : X) : (evaluationCone X).π.app F x = point F.unop x := rfl

@[simp] theorem evaluationCone_π_coordinate (F : Finset (CompactOpens X))
    (U : Coordinates F) (x : X) :
    ((evaluationCone X).π.app (Opposite.op F) x).1 U ↔ x ∈ (U.1 : Set X) := Iff.rfl

/-- Finite-stage evaluation is compatible with every refinement of coordinates. -/
theorem evaluationCone_restrict_apply {F G : Finset (CompactOpens X)} (hFG : F ⊆ G)
    (x : X) :
    (stageDiagram X).map (homOfLE hFG).op
        ((evaluationCone X).π.app (Opposite.op G) x) =
      (evaluationCone X).π.app (Opposite.op F) x :=
  congrArg
    (fun f : (evaluationCone X).pt ⟶ (stageDiagram X).obj (Opposite.op F) => f x)
    ((evaluationCone X).w (homOfLE hFG).op)

/-- The family lift of the evaluation cone is the existing coordinate evaluation map. -/
theorem familyLift_evaluation_apply (x : X) :
    familyLift (evaluationCone X) x = toFamily x := by
  apply Family.ext
  intro F
  rfl

/-- Coordinate evaluation agrees with the spectral-space reconstruction homeomorphism. -/
theorem familyLift_evaluation_eq_spaceHomeomorph [SpectralSpace X] (x : X) :
    familyLift (evaluationCone X) x = spaceHomeomorph X x := by
  rw [familyLift_evaluation_apply, spaceHomeomorph_apply]

/-- For a spectral space, finite-stage evaluations form a limiting cone. -/
noncomputable def evaluationConeIsLimit (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] : IsLimit (evaluationCone X) := by
  have hLift : (familyConeIsLimit X).lift (evaluationCone X) =
      familyLift (evaluationCone X) := by
    apply (familyConeIsLimit X).hom_ext
    intro F
    rw [(familyConeIsLimit X).fac]
    exact (familyLift_fac (evaluationCone X) F).symm
  have hHomeo : familyLift (evaluationCone X) =
      (TopCat.isoOfHomeo (spaceHomeomorph X)).hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact familyLift_evaluation_eq_spaceHomeomorph (X := X) x
  haveI : IsIso ((familyConeIsLimit X).lift (evaluationCone X)) := by
    rw [hLift, hHomeo]
    exact (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of (Family X))
      (spaceHomeomorph X)).isIso_hom
  exact (familyConeIsLimit X).ofPointIso

end SpectralStoneDuality.FiniteCoordinates
