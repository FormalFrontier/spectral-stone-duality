/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.SubspaceStrictSpecializations
public import Mathlib.Topology.Inseparable
public import Mathlib.Data.Set.Finite.Range

/-!
# Subspace strict-specialization examples

A proper closed component has a nonempty strict boundary even though the
ambient space is not `T₀`. A singleton has no strict indices. Two further
spaces distinguish the containment and selected-point hypotheses: a subset
missing a specialization, and an indiscrete space with a non-strict boundary
incidence.

## References

- Mathlib contributors, specialization in subtypes, sum topologies, and
  finite upper-set topologies.
- Formal Frontier Agents, `SpectralStoneDualityExamples.GenericPointRemoval`,
  for finite specialization-boundary examples; the components and negative
  tests here concern ambient/subspace indices.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set TopologicalSpace Topology
open Topology.GenericPointRemoval

namespace SpectralStoneDualityExamples.SubspaceStrictSpecializations

section ProperClosedNonT0

local instance : TopologicalSpace (Fin 2) := Topology.upperSet (Fin 2)
local instance : TopologicalSpace Bool := ⊤

private abbrev Ambient := Fin 2 ⊕ Bool

private def closedPart : Set Ambient := Set.range (Sum.inl : Fin 2 → Ambient)

private theorem closedPart_closed : IsClosed closedPart := isClosed_range_inl

private theorem closedPart_proper : closedPart ≠ (Set.univ : Set Ambient) := by
  intro heq
  have h : (Sum.inr false : Ambient) ∈ closedPart := heq.symm ▸ Set.mem_univ _
  simp [closedPart] at h

private def chosen : Set closedPart := {z | (z : Ambient) = Sum.inl (1 : Fin 2)}

private def generic : chosen :=
  ⟨⟨Sum.inl 1, ⟨1, rfl⟩⟩, rfl⟩

private theorem chosen_onlyGenerizations : HasOnlyGenerizations chosen := by
  intro η x hx
  have hη : (η.1 : Ambient) = Sum.inl (1 : Fin 2) := η.2
  obtain ⟨a, ha⟩ := x.2
  have hspec : (Sum.inl a : Ambient) ⤳ Sum.inl (1 : Fin 2) := by
    rw [ha]
    exact hη ▸ (subtype_specializes_iff _ _).1 hx
  have hle : (1 : Fin 2) ≤ a :=
    Topology.IsUpperSet.specializes_iff_le.mp
      (Topology.IsEmbedding.inl.isInducing.specializes_iff.mp hspec)
  have ha1 : a = 1 := le_antisymm (Fin.le_last a) hle
  apply Subtype.ext
  calc
    (x : Ambient) = Sum.inl a := ha.symm
    _ = Sum.inl 1 := congrArg Sum.inl ha1
    _ = (η.1 : Ambient) := hη.symm

private def strictEndpoint :
    {σ : Ambient // (generic.1 : Ambient) ⤳ σ ∧ ¬ σ ⤳ (generic.1 : Ambient)} := by
  refine ⟨Sum.inl 0, ?_, ?_⟩
  · apply Topology.IsEmbedding.inl.isInducing.specializes_iff.mpr
    exact Topology.IsUpperSet.specializes_iff_le.mpr (by decide)
  · intro h
    have hle : (1 : Fin 2) ≤ 0 :=
      Topology.IsUpperSet.specializes_iff_le.mp
        (Topology.IsEmbedding.inl.isInducing.specializes_iff.mp h)
    exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) hle

private def boundaryEndpoint : Strict chosen generic := by
  refine ⟨⟨⟨Sum.inl 0, ⟨0, rfl⟩⟩, ?_⟩, ?_⟩
  · intro h
    have heq : (0 : Fin 2) = 1 := Sum.inl_injective h
    exact (by decide : (0 : Fin 2) ≠ 1) heq
  · exact (subtype_specializes_iff _ _).mpr strictEndpoint.2.1

example : Nonempty (Strict chosen generic) := ⟨boundaryEndpoint⟩

example : Finite {σ : Ambient // (generic.1 : Ambient) ⤳ σ ∧
    ¬ σ ⤳ (generic.1 : Ambient)} :=
  finite_ambientStrict (Z := closedPart) (generic.1 : Ambient)
    (closure_minimal (Set.singleton_subset_iff.mpr generic.1.2) closedPart_closed)
    (Set.finite_range (Sum.inl : Fin 2 → Ambient))

example : IsOpen chosen := isOpen_selected chosen_onlyGenerizations

example : IsClosed (closedPart \ (Subtype.val '' chosen)) :=
  isClosed_remainder closedPart_closed chosen_onlyGenerizations

example : ((ambientStrictEquiv generic closedPart_closed chosen_onlyGenerizations
    strictEndpoint).1.1 : Ambient) = Sum.inl 0 := by
  simpa only [ambientStrictEquiv_apply_val] using
    (show strictEndpoint.1 = Sum.inl (0 : Fin 2) from rfl)

example : ((ambientStrictEquiv generic closedPart_closed
    chosen_onlyGenerizations).symm boundaryEndpoint).1 = Sum.inl 0 := by
  simpa only [ambientStrictEquiv_symm_apply_val] using
    (show (boundaryEndpoint.1.1 : Ambient) = Sum.inl (0 : Fin 2) from rfl)

private theorem ambient_not_t0 : ¬ T0Space Ambient := by
  have hspec (a b : Bool) : (Sum.inr a : Ambient) ⤳ Sum.inr b := by
    apply Topology.IsEmbedding.inr.isInducing.specializes_iff.mpr
    apply specializes_iff_nhds.mpr
    simp only [IndiscreteTopology.nhds_eq]
    exact le_rfl
  intro hT0
  have heq := (t0Space_iff_inseparable Ambient).mp hT0
    (Sum.inr false) (Sum.inr true)
    (inseparable_iff_specializes_and.mpr ⟨hspec false true, hspec true false⟩)
  exact (by decide : false ≠ true) (Sum.inr_injective heq)

example : ¬ T0Space Ambient := ambient_not_t0
example : IsClosed closedPart ∧ closedPart ≠ Set.univ :=
  ⟨closedPart_closed, closedPart_proper⟩

end ProperClosedNonT0

section Singleton

local instance : TopologicalSpace PUnit := ⊤

private def singleZ : Set PUnit := Set.univ
private def singleG : Set singleZ := Set.univ
private def singleEta : singleG := ⟨⟨PUnit.unit, Set.mem_univ _⟩, Set.mem_univ _⟩

example : IsEmpty {σ : PUnit // (singleEta.1 : PUnit) ⤳ σ ∧
    ¬ σ ⤳ (singleEta.1 : PUnit)} :=
  ⟨fun σ => σ.2.2 (Specializes.of_eq (Subsingleton.elim σ.1 (singleEta.1 : PUnit)))⟩

example : IsEmpty (Strict singleG singleEta) :=
  ⟨fun τ => τ.1.2 (Set.mem_univ _)⟩

end Singleton

section MissingContainment

local instance : TopologicalSpace (Fin 2) := Topology.upperSet (Fin 2)

private def missingZ : Set (Fin 2) := {1}
private def missingG : Set missingZ := Set.univ
private def missingEta : missingG := ⟨⟨1, by simp [missingZ]⟩, Set.mem_univ _⟩

private theorem missing_onlyGenerizations : HasOnlyGenerizations missingG := by
  intro η x _
  apply Subtype.ext
  have hx : (x : Fin 2) = 1 := Set.mem_singleton_iff.mp x.2
  have hη : (η.1 : Fin 2) = 1 := Set.mem_singleton_iff.mp η.1.2
  exact hx.trans hη.symm

private theorem missing_spec : (missingEta.1 : Fin 2) ⤳ (0 : Fin 2) :=
  Topology.IsUpperSet.specializes_iff_le.mpr (by decide)

private theorem missing_reverse : ¬ (0 : Fin 2) ⤳ (missingEta.1 : Fin 2) := by
  intro h
  exact (by decide : ¬ ((1 : Fin 2) ≤ 0))
    (Topology.IsUpperSet.specializes_iff_le.mp h)

example : ¬ closure ({(missingEta.1 : Fin 2)} : Set (Fin 2)) ⊆ missingZ := by
  intro hcontain
  have hmem : (0 : Fin 2) ∈ missingZ := hcontain (Specializes.mem_closure missing_spec)
  simp [missingZ] at hmem

example : ¬ IsClosed missingZ := by
  intro hZ
  have hmem : (0 : Fin 2) ∈ missingZ :=
    missing_spec.mem_closed hZ (by simp [missingZ])
  simp [missingZ] at hmem

example : HasOnlyGenerizations missingG := missing_onlyGenerizations
example : Nonempty {σ : Fin 2 // (missingEta.1 : Fin 2) ⤳ σ ∧
    ¬ σ ⤳ (missingEta.1 : Fin 2)} :=
  ⟨⟨0, missing_spec, missing_reverse⟩⟩
example : IsEmpty (Strict missingG missingEta) :=
  ⟨fun τ => τ.1.2 (Set.mem_univ _)⟩

end MissingContainment

section MissingGenericity

local instance : TopologicalSpace Bool := ⊤

private def allPoints : Set Bool := Set.univ
private def nonGeneric : Set allPoints := {z | (z : Bool) = false}
private def selected : nonGeneric :=
  ⟨⟨false, Set.mem_univ _⟩, rfl⟩

example : IsClosed allPoints := isClosed_univ

example : closure ({(selected.1 : Bool)} : Set Bool) ⊆ allPoints :=
  Set.subset_univ _

private theorem any_specializes (a b : Bool) : a ⤳ b := by
  apply specializes_iff_nhds.mpr
  simp only [IndiscreteTopology.nhds_eq]
  exact le_rfl

example : ¬ HasOnlyGenerizations nonGeneric := by
  intro hG
  have heq : (true : Bool) = false := congrArg Subtype.val
    (hG selected ⟨true, Set.mem_univ _⟩
      ((subtype_specializes_iff _ _).mpr (any_specializes true false)))
  exact (by decide : true ≠ false) heq

example : Nonempty (Strict nonGeneric selected) := by
  refine ⟨⟨⟨⟨true, Set.mem_univ _⟩, ?_⟩, ?_⟩⟩
  · exact (by decide : true ≠ false)
  · exact (subtype_specializes_iff _ _).mpr (any_specializes false true)

example : IsEmpty {σ : Bool // (selected.1 : Bool) ⤳ σ ∧
    ¬ σ ⤳ (selected.1 : Bool)} :=
  ⟨fun σ => σ.2.2 (any_specializes σ.1 false)⟩

end MissingGenericity

end SpectralStoneDualityExamples.SubspaceStrictSpecializations
