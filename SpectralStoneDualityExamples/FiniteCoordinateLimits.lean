/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.FiniteCoordinates.Limits

/-!
# Finite-coordinate cone examples

Empty, Sierpiński, and indiscrete spaces give boundary cases for finite-stage evaluations
without using any limiting property. The universal-lift examples for the indiscrete and
Sierpiński spaces apply the proved limiting properties.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open SpectralStoneDuality.FiniteCoordinates

namespace SpectralStoneDualityExamples.FiniteCoordinateLimits

section Empty

local instance : TopologicalSpace Empty := ⊥

example : IsCofiltered ((Finset (CompactOpens Empty))ᵒᵖ) := inferInstance

example (F : Finset (CompactOpens Empty)) :
    IsEmpty ((stageDiagram Empty).obj (Opposite.op F)) := by
  refine ⟨fun v => ?_⟩
  obtain ⟨x, _⟩ := v.2
  exact x.elim

example : IsEmpty (familyCone Empty).pt := by
  refine ⟨fun z => ?_⟩
  obtain ⟨x, _⟩ := (z.1 ∅).2
  exact x.elim

end Empty

section Sierpinski

private def positiveOpen : CompactOpens Prop where
  carrier := {True}
  isCompact' := (Set.toFinite {True}).isCompact
  isOpen' := isOpen_singleton_true

example : (evaluationCone Prop).π.app (Opposite.op {positiveOpen}) True ≠
    (evaluationCone Prop).π.app (Opposite.op {positiveOpen}) False := by
  intro h
  have hval := congrArg (fun v : Stage ({positiveOpen} : Finset (CompactOpens Prop)) =>
    v.1 ⟨positiveOpen, Finset.mem_singleton_self _⟩) h
  have htrue : ((evaluationCone Prop).π.app (Opposite.op {positiveOpen}) True).1
      ⟨positiveOpen, Finset.mem_singleton_self _⟩ :=
    (evaluationCone_π_coordinate {positiveOpen}
      ⟨positiveOpen, Finset.mem_singleton_self _⟩ True).2 (by simp [positiveOpen])
  have hfalse : ¬ ((evaluationCone Prop).π.app (Opposite.op {positiveOpen}) False).1
      ⟨positiveOpen, Finset.mem_singleton_self _⟩ := by
    intro hfalse
    have := (evaluationCone_π_coordinate {positiveOpen}
      ⟨positiveOpen, Finset.mem_singleton_self _⟩ False).1 hfalse
    simp [positiveOpen] at this
  exact hfalse (Eq.mp hval htrue)

example :
    (evaluationConeIsLimit Prop).lift (familyCone Prop) =
      TopCat.ofHom ⟨(spaceHomeomorph Prop).symm,
        (spaceHomeomorph Prop).symm.continuous⟩ := by
  apply (evaluationConeIsLimit Prop).hom_ext
  intro F
  rw [(evaluationConeIsLimit Prop).fac]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change z.1 F.unop = point F.unop ((spaceHomeomorph Prop).symm z)
  simpa only [spaceHomeomorph_apply, toFamily_apply] using
    (congrArg (fun w : Family Prop => w.1 F.unop)
      ((spaceHomeomorph Prop).apply_symm_apply z)).symm

end Sierpinski

section NonT0

local instance : TopologicalSpace (Fin 2) := ⊤

/-- In the indiscrete two-point space, all finite-stage evaluations agree at distinct points. -/
example : (∀ F : Finset (CompactOpens (Fin 2)),
    (evaluationCone (Fin 2)).π.app (Opposite.op F) (0 : Fin 2) =
      (evaluationCone (Fin 2)).π.app (Opposite.op F) (1 : Fin 2)) ∧ (0 : Fin 2) ≠ 1 := by
  constructor
  · intro F
    apply Stage.ext
    intro U
    have hmem : (0 : Fin 2) ∈ (U.1 : Set (Fin 2)) ↔
        (1 : Fin 2) ∈ (U.1 : Set (Fin 2)) := by
      rcases (TopologicalSpace.isOpen_top_iff (U.1 : Set (Fin 2))).mp U.1.isOpen with h | h
      · simp [h]
      · simp [h]
    exact (evaluationCone_π_coordinate F U (0 : Fin 2)).trans
      (hmem.trans (evaluationCone_π_coordinate F U (1 : Fin 2)).symm)
  · decide

example (x : Fin 2) :
    (familyConeIsLimit (Fin 2)).lift (evaluationCone (Fin 2)) x = toFamily x := by
  have h : (familyConeIsLimit (Fin 2)).lift (evaluationCone (Fin 2)) =
      familyLift (evaluationCone (Fin 2)) := by
    apply (familyConeIsLimit (Fin 2)).hom_ext
    intro F
    rw [(familyConeIsLimit (Fin 2)).fac]
    exact (familyLift_fac (evaluationCone (Fin 2)) F).symm
  rw [h]
  exact familyLift_evaluation_apply x

end NonT0

end SpectralStoneDualityExamples.FiniteCoordinateLimits
