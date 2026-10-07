/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.GenericPointRemoval
public import Mathlib.Topology.Specialization
public import Mathlib.Topology.Inseparable
public import Mathlib.Order.Max

/-!
# Generic-point removal: empty, chain and shared-specialization examples

The empty and singleton cases have no boundary incidences. A three-point
chain has two discrete boundary incidences but a non-discrete complement.
In a three-point `V`, two different incidences map to the same point of the
complement. Its continuity and pushout conclusions use the general criteria,
while the premises and boundary checks are established directly.

## References

- Mathlib contributors, specialization orders, finite Alexandrov spaces and
  upper-set topologies.
- Formal Frontier Agents, `ValuationIntegers.FiniteIntersections.Spectrum`,
  for the independent generic-point fork.
- Stefan Schröer, *A simple proof for Hochster's Theorem*, §2, motivates
  the finite-space square; Ershov's antecedent is credited indirectly.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open Set TopologicalSpace Topology
open Topology.GenericPointRemoval

namespace SpectralStoneDualityExamples.GenericPointRemoval

section Empty

local instance : TopologicalSpace Empty := ⊥

private def emptyG : Set Empty := ∅

private theorem empty_onlyGenerizations : HasOnlyGenerizations emptyG := by
  intro η
  exact η.2.elim

example : IsEmpty (Boundary emptyG) :=
  ⟨fun p => (p.1.2).elim⟩

example : CategoryTheory.IsPushout (boundaryFork emptyG) (boundaryRest emptyG)
    (forkTotal emptyG) (restTotal emptyG) :=
  isPushout emptyG empty_onlyGenerizations

end Empty

section Singleton

local instance : TopologicalSpace PUnit := ⊥

private def singletonG : Set PUnit := Set.univ

private theorem singleton_onlyGenerizations : HasOnlyGenerizations singletonG := by
  intro _ x _
  exact Subsingleton.elim _ _

example : IsEmpty (Boundary singletonG) :=
  ⟨fun p => p.2.1.2 (Set.mem_univ _)⟩

example : forkTotal singletonG
    ⟨(⟨PUnit.unit, Set.mem_univ _⟩ : singletonG), .generic⟩ = PUnit.unit := by
  simp

example : CategoryTheory.IsPushout (boundaryFork singletonG) (boundaryRest singletonG)
    (forkTotal singletonG) (restTotal singletonG) :=
  isPushout singletonG singleton_onlyGenerizations

end Singleton

section ThreePointChain

local notation "Chain" => Fin 3

local instance : TopologicalSpace Chain := Topology.upperSet Chain

private def chainG : Set Chain := {2}

private def chainTop : chainG := ⟨2, by simp [chainG]⟩

private theorem chain_onlyGenerizations : HasOnlyGenerizations chainG := by
  intro η x hx
  have hη : η.1 = (2 : Chain) := by simpa [chainG] using η.2
  have hle : η.1 ≤ x := Topology.IsUpperSet.specializes_iff_le.mp hx
  rw [hη] at hle
  exact (le_antisymm (Fin.le_last x) hle).trans hη.symm

private def chainLow : Strict chainG chainTop :=
  ⟨⟨0, by simp [chainG]⟩, Topology.IsUpperSet.specializes_iff_le.mpr (by decide)⟩

private def chainMiddle : Strict chainG chainTop :=
  ⟨⟨1, by simp [chainG]⟩, Topology.IsUpperSet.specializes_iff_le.mpr (by decide)⟩

example : chainLow ≠ chainMiddle := by
  intro h
  have hv := congrArg (fun σ : Strict chainG chainTop => (σ.1 : Chain)) h
  simp [chainLow, chainMiddle] at hv

example : IsOpen ({WithGenericPoint.generic,
    WithGenericPoint.closed chainLow} :
      Set (WithGenericPoint (Strict chainG chainTop))) :=
  (WithGenericPoint.isOpen_iff _).mpr (Or.inr (by simp))

private theorem chain_rest_not_discrete :
    ¬ DiscreteTopology (Rest chainG) := by
  intro hd
  let low : Rest chainG := ⟨0, by simp [chainG]⟩
  let middle : Rest chainG := ⟨1, by simp [chainG]⟩
  have hspec : middle ⤳ low := (subtype_specializes_iff middle low).mpr
    (Topology.IsUpperSet.specializes_iff_le.mpr (by decide))
  have hopen : IsOpen ({low} : Set (Rest chainG)) := isOpen_discrete _
  have hmem : middle ∈ ({low} : Set (Rest chainG)) :=
    (specializes_iff_forall_open.mp hspec) _ hopen (by simp)
  have heq : (1 : Chain) = 0 := congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)
  exact (by decide : (1 : Chain) ≠ 0) heq

example : ¬ DiscreteTopology (Rest chainG) := chain_rest_not_discrete

example : DiscreteTopology (TopCat.discrete.obj (Boundary chainG)) := inferInstance

example : boundaryRest chainG ⟨chainTop, chainLow⟩ = chainLow.1 :=
  boundaryRest_apply chainG chainTop chainLow

example : CategoryTheory.IsPushout (boundaryFork chainG) (boundaryRest chainG)
    (forkTotal chainG) (restTotal chainG) :=
  isPushout chainG chain_onlyGenerizations

/-- A gluing map whose target universe is unrelated to that of the
three-point space. -/
private noncomputable def chainGlue {W : Type v} [TopologicalSpace W]
    (h : C(Forks chainG, W)) (q : C(Rest chainG, W))
    (hcompat : ∀ (η : chainG) (σ : Strict chainG η), h ⟨η, .closed σ⟩ = q σ.1) :
    C(Chain, W) :=
  ⟨extend chainG h q,
    continuous_extend chainG chain_onlyGenerizations h q h.continuous q.continuous hcompat⟩

example {W : Type v} [TopologicalSpace W]
    (h : C(Forks chainG, W)) (q : C(Rest chainG, W))
    (hcompat : ∀ (η : chainG) (σ : Strict chainG η), h ⟨η, .closed σ⟩ = q σ.1) :
    chainGlue h q hcompat (2 : Chain) = h ⟨chainTop, .generic⟩ := by
  change extend chainG h q (2 : Chain) = h ⟨chainTop, .generic⟩
  exact extend_generic chainG h q chainTop

end ThreePointChain

section SharedSpecialization

local notation "V" => WithGenericPoint Bool

local instance : TopologicalSpace V := Topology.upperSet V

private def left : V := .closed false
private def right : V := .closed true
private def shared : V := .generic
private def chosen : Set V := {left, right}

private def leftGeneric : chosen := ⟨left, by simp [chosen]⟩
private def rightGeneric : chosen := ⟨right, by simp [chosen]⟩
private def sharedRest : Rest chosen := ⟨shared, by simp [chosen, shared, left, right]⟩

private theorem chosen_onlyGenerizations : HasOnlyGenerizations chosen := by
  intro η x hx
  have hη : η.1 = left ∨ η.1 = right := by simpa [chosen] using η.2
  have hneq : η.1 ≠ (WithGenericPoint.generic : V) := by
    rcases hη with hη | hη <;> simp [hη, left, right]
  have hle : η.1 ≤ x := Topology.IsUpperSet.specializes_iff_le.mp hx
  cases x with
  | generic =>
    rcases hle with h | h <;> exact (hneq h).elim
  | closed b =>
    rcases hle with h | h
    · exact (hneq h).elim
    · exact h.symm

private def leftIncidence : Strict chosen leftGeneric :=
  ⟨sharedRest, Topology.IsUpperSet.specializes_iff_le.mpr
    (WithGenericPoint.generic_le _)⟩

private def rightIncidence : Strict chosen rightGeneric :=
  ⟨sharedRest, Topology.IsUpperSet.specializes_iff_le.mpr
    (WithGenericPoint.generic_le _)⟩

private theorem same_rest : boundaryRest chosen ⟨leftGeneric, leftIncidence⟩ =
    boundaryRest chosen ⟨rightGeneric, rightIncidence⟩ := by
  calc
    boundaryRest chosen ⟨leftGeneric, leftIncidence⟩ = leftIncidence.1 :=
      boundaryRest_apply chosen leftGeneric leftIncidence
    _ = sharedRest := rfl
    _ = rightIncidence.1 := rfl
    _ = boundaryRest chosen ⟨rightGeneric, rightIncidence⟩ :=
      (boundaryRest_apply chosen rightGeneric rightIncidence).symm

example : boundaryRest chosen ⟨leftGeneric, leftIncidence⟩ =
    boundaryRest chosen ⟨rightGeneric, rightIncidence⟩ := same_rest

private theorem boundaryRest_not_injective : ¬ Function.Injective (boundaryRest chosen) := by
  intro hinj
  have heq := hinj same_rest
  have hleft : left = right := congrArg (fun p : Boundary chosen => (p.1 : V)) heq
  exact (by simp [left, right] : left ≠ right) hleft

example : ¬ Function.Injective (boundaryRest chosen) := boundaryRest_not_injective

example : CategoryTheory.IsPushout (boundaryFork chosen) (boundaryRest chosen)
    (forkTotal chosen) (restTotal chosen) :=
  isPushout chosen chosen_onlyGenerizations

end SharedSpecialization

section FiniteT0

variable {X : Type u} [TopologicalSpace X] [T0Space X]

private def maximalGenerics : Set X :=
  {x | IsMax (Specialization.toEquiv x)}

private theorem maximal_onlyGenerizations :
    HasOnlyGenerizations (maximalGenerics (X := X)) := by
  intro η x hx
  exact Specialization.toEquiv.injective
    (η.2.eq_of_le (Specialization.toEquiv_le_toEquiv.mpr hx)).symm

variable [Finite X]

example : CategoryTheory.IsPushout (boundaryFork (maximalGenerics (X := X)))
    (boundaryRest (maximalGenerics (X := X)))
    (forkTotal (maximalGenerics (X := X)))
    (restTotal (maximalGenerics (X := X))) :=
  isPushout (maximalGenerics (X := X)) maximal_onlyGenerizations

end FiniteT0

end SpectralStoneDualityExamples.GenericPointRemoval
