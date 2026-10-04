/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.FiniteCoordinates
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Finite-coordinate boundary examples

Empty spaces have empty stages and no compatible families; singletons have singleton stages.
A single coordinate on a discrete two-point space retains the Sierpiński topology, not
the discrete quotient topology. Strict refinements of three-point coordinates retain
the first coordinate while forgetting the others.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set TopologicalSpace Topology SpectralStoneDuality.FiniteCoordinates

namespace SpectralStoneDualityExamples.FiniteCoordinates

private theorem specializes_single_coordinate {X : Type*} [TopologicalSpace X]
    (U : CompactOpens X) (x y : X) (hy : y ∉ (U : Set X)) :
    point {U} x ⤳ point {U} y := by
  rw [specializes_iff]
  intro V h
  have hV : V.1 = U := Finset.mem_singleton.mp V.2
  exact False.elim (hy (by simpa only [hV] using (point_coordinate {U} V y).mp h))

private theorem not_t1_single_coordinate {X : Type*} [TopologicalSpace X]
    (U : CompactOpens X) (x y : X) (hx : x ∈ (U : Set X))
    (hy : y ∉ (U : Set X)) : ¬ T1Space (Stage ({U} : Finset (CompactOpens X))) := by
  intro ht1
  have hxy : point {U} x = point {U} y :=
    t1Space_iff_specializes_imp_eq.mp ht1 (specializes_single_coordinate U x y hy)
  have hx' : (point {U} x).1 ⟨U, Finset.mem_singleton_self U⟩ :=
    (point_coordinate _ _ _).mpr hx
  rw [hxy] at hx'
  exact hy ((point_coordinate _ _ _).mp hx')

section Empty

local instance : TopologicalSpace Empty := ⊥

example (F : Finset (CompactOpens Empty)) : IsEmpty (Stage F) := by
  refine ⟨fun v => ?_⟩
  obtain ⟨x, _⟩ := v.2
  exact x.elim

example : IsEmpty (Family Empty) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨x, _⟩ := (z.1 ∅).2
  exact x.elim

end Empty

section Singleton

local instance : TopologicalSpace PUnit := ⊥

example (F : Finset (CompactOpens PUnit)) : Nonempty (Stage F) :=
  ⟨point F PUnit.unit⟩

example : Nonempty (Family PUnit) := ⟨toFamily PUnit.unit⟩

example (F : Finset (CompactOpens PUnit)) (v w : Stage F) : v = w := by
  obtain ⟨x, rfl⟩ := surjective_point F v
  obtain ⟨y, rfl⟩ := surjective_point F w
  exact congrArg (point F) (Subsingleton.elim x y)

end Singleton

section Sierpinski

private def positiveOpen : CompactOpens Prop where
  carrier := {True}
  isCompact' := (Set.toFinite {True}).isCompact
  isOpen' := isOpen_singleton_true

example : (point {positiveOpen} True).1 ⟨positiveOpen, Finset.mem_singleton_self _⟩ := by
  simp [positiveOpen]

example : ¬ (point {positiveOpen} False).1
    ⟨positiveOpen, Finset.mem_singleton_self _⟩ := by
  simp [positiveOpen]

example : coordinateValue (toFamily True) positiveOpen ∧
    ¬ coordinateValue (toFamily False) positiveOpen := by
  simp [positiveOpen]

example : ¬ T1Space (Stage ({positiveOpen} : Finset (CompactOpens Prop))) :=
  not_t1_single_coordinate positiveOpen True False
    (by simp [positiveOpen]) (by simp [positiveOpen])

example : SpectralSpace Prop := inferInstance

example : (spaceHomeomorph Prop) True ≠ (spaceHomeomorph Prop) False := by
  intro h
  exact Eq.mp ((spaceHomeomorph Prop).injective h) True.intro

example : ¬ T1Space Prop := by
  intro h
  have hspec : (True : Prop) ⤳ False :=
    (specializes_iff_nhds).2 (by rw [nhds_false]; exact le_top)
  exact Eq.mp (t1Space_iff_specializes_imp_eq.mp h hspec) True.intro

end Sierpinski

section NonT0

local instance : TopologicalSpace (Fin 2) := ⊤

example : Function.Surjective (toFamily (X := Fin 2)) :=
  surjective_toFamily

example : ¬ Function.Injective (toFamily (X := Fin 2)) := by
  have hmem (U : CompactOpens (Fin 2)) :
      (0 : Fin 2) ∈ (U : Set (Fin 2)) ↔ (1 : Fin 2) ∈ (U : Set (Fin 2)) := by
    rcases (TopologicalSpace.isOpen_top_iff (U : Set (Fin 2))).mp U.isOpen with h | h
    · simp [h]
    · simp [h]
  have heq : toFamily (0 : Fin 2) = toFamily (1 : Fin 2) := by
    apply Family.ext_coordinate
    intro F U
    change (0 : Fin 2) ∈ (U.1 : Set (Fin 2)) ↔ (1 : Fin 2) ∈ (U.1 : Set (Fin 2))
    exact hmem U.1
  exact fun hinj => (by decide : (0 : Fin 2) ≠ 1) (hinj heq)

end NonT0

section TwoPoints

local instance : TopologicalSpace (Fin 2) := ⊥

private def singletonOpen : CompactOpens (Fin 2) where
  carrier := {0}
  isCompact' := (Set.toFinite {0}).isCompact
  isOpen' := isOpen_discrete _

private def oneCoordinate : Finset (CompactOpens (Fin 2)) := {singletonOpen}

example : (point oneCoordinate 0).1
    ⟨singletonOpen, Finset.mem_singleton_self _⟩ := by
  simp [singletonOpen]

example : ¬ (point oneCoordinate 1).1
    ⟨singletonOpen, Finset.mem_singleton_self _⟩ := by
  simp [singletonOpen]

example : Function.Bijective (point oneCoordinate (X := Fin 2)) := by
  constructor
  · intro x y h
    fin_cases x <;> fin_cases y
    all_goals first | rfl | (
      have hval := congrArg (fun v : Stage oneCoordinate =>
        v.1 ⟨singletonOpen, Finset.mem_singleton_self _⟩) h
      simp [point, membership, singletonOpen] at hval)
  · exact surjective_point oneCoordinate

private theorem stage_not_t1 : ¬ T1Space (Stage oneCoordinate) :=
  not_t1_single_coordinate singletonOpen 0 1
    (by simp [singletonOpen]) (by simp [singletonOpen])

example : ¬ T1Space (Stage oneCoordinate) := stage_not_t1

example : ¬ IsQuotientMap (point oneCoordinate (X := Fin 2)) := by
  intro hq
  apply stage_not_t1
  refine ⟨fun v => ?_⟩
  exact hq.isCoinducing.isClosed_preimage.mp (isClosed_discrete _)

end TwoPoints

section Refinement

local instance : TopologicalSpace (Fin 3) := ⊥

private def singletonOpen3 (index : Fin 3) : CompactOpens (Fin 3) where
  carrier := {index}
  isCompact' := (Set.toFinite {index}).isCompact
  isOpen' := isOpen_discrete _

private theorem singletonOpen3_injective : Function.Injective singletonOpen3 := by
  intro index other h
  have hmem : index ∈ (singletonOpen3 other : Set (Fin 3)) := by
    rw [← h]
    simp [singletonOpen3]
  simpa [singletonOpen3] using hmem

private def firstCoordinates : Finset (CompactOpens (Fin 3)) := {singletonOpen3 0}

private noncomputable def secondCoordinates : Finset (CompactOpens (Fin 3)) := by
  classical
  exact {singletonOpen3 0, singletonOpen3 1}

private noncomputable def thirdCoordinates : Finset (CompactOpens (Fin 3)) := by
  classical
  exact {singletonOpen3 0, singletonOpen3 1, singletonOpen3 2}

private theorem first_subset_second : firstCoordinates ⊆ secondCoordinates := by
  classical
  simp [firstCoordinates, secondCoordinates]

private theorem second_subset_third : secondCoordinates ⊆ thirdCoordinates := by
  classical
  simp [secondCoordinates, thirdCoordinates]

example : firstCoordinates ⊂ secondCoordinates ∧ secondCoordinates ⊂ thirdCoordinates := by
  classical
  constructor
  · exact Finset.ssubset_iff_subset_ne.mpr ⟨first_subset_second, by
      intro h
      have hmem : singletonOpen3 1 ∈ firstCoordinates := h ▸ (by simp [secondCoordinates])
      have h01 : (0 : Fin 3) = 1 := singletonOpen3_injective
        (Finset.mem_singleton.mp (by simpa [firstCoordinates] using hmem)).symm
      exact (by decide : (0 : Fin 3) ≠ 1) h01⟩
  · exact Finset.ssubset_iff_subset_ne.mpr ⟨second_subset_third, by
      intro h
      have hmem : singletonOpen3 2 ∈ secondCoordinates := h ▸ (by simp [thirdCoordinates])
      have hmem' : singletonOpen3 2 = singletonOpen3 0 ∨
          singletonOpen3 2 = singletonOpen3 1 := by simpa [secondCoordinates] using hmem
      rcases hmem' with h20 | h21
      · exact (by decide : (2 : Fin 3) ≠ 0) (singletonOpen3_injective h20)
      · exact (by decide : (2 : Fin 3) ≠ 1) (singletonOpen3_injective h21)⟩

example : restrict first_subset_second (point secondCoordinates 1) =
    restrict first_subset_second (point secondCoordinates 2) ∧
    point secondCoordinates 1 ≠ point secondCoordinates 2 := by
  constructor
  · rw [restrict_point, restrict_point]
    apply Stage.ext
    intro U
    have hU : U.1 = singletonOpen3 0 := Finset.mem_singleton.mp U.2
    simp [point_coordinate, hU, singletonOpen3]
  · intro h
    have hval := congrArg (fun v : Stage secondCoordinates =>
      v.1 ⟨singletonOpen3 1, by simp [secondCoordinates]⟩) h
    simp [point_coordinate, singletonOpen3] at hval

example : (restrict (first_subset_second.trans second_subset_third)
      (point thirdCoordinates 0)).1
      ⟨singletonOpen3 0, by simp [firstCoordinates]⟩ ∧
    ¬ (restrict (first_subset_second.trans second_subset_third)
      (point thirdCoordinates 1)).1
      ⟨singletonOpen3 0, by simp [firstCoordinates]⟩ := by
  rw [restrict_comp first_subset_second second_subset_third]
  simp [singletonOpen3]

end Refinement

end SpectralStoneDualityExamples.FiniteCoordinates
