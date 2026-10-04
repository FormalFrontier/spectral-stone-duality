/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality
public import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Closed points among generizations

In the upper-set topology on `Fin 2`, both points lie in the generization
subspace of the bottom point, but only the bottom point is closed there.
For indiscrete `Bool`, the original singleton need not be closed without `T₀`.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.1(a), for the closed-generization observation.
- Mathlib, `Topology.NhdsKer` and `Topology.Order.UpperLowerSetTopology`,
  for specialization and the upper-set example.
-/

@[expose] public section

open Set TopologicalSpace

namespace SpectralStoneDualityExamples

section UpperSet

private abbrev TwoPointUpper := Topology.WithUpperSet (Fin 2)

private def bottom : TwoPointUpper := Topology.WithUpperSet.toUpperSet 0
private def top : TwoPointUpper := Topology.WithUpperSet.toUpperSet 1

private instance : T0Space TwoPointUpper :=
  (t0Space_iff_inseparable TwoPointUpper).2 (by
    intro left right h
    obtain ⟨hleft, hright⟩ := inseparable_iff_specializes_and.mp h
    apply Topology.WithUpperSet.ofUpperSet_inj.mp
    apply le_antisymm
    · exact Topology.WithUpperSet.ofUpperSet_le_iff.mpr
        (Topology.IsUpperSet.specializes_iff_le.mp hright)
    · exact Topology.WithUpperSet.ofUpperSet_le_iff.mpr
        (Topology.IsUpperSet.specializes_iff_le.mp hleft))

private theorem allGenerizations : nhdsKer ({bottom} : Set TwoPointUpper) = Set.univ := by
  rw [Topology.IsUpperSet.nhdsKer_singleton]
  ext point
  change (0 : Fin 2) ≤ Topology.WithUpperSet.ofUpperSet point ↔ True
  simp

private theorem closedBottomAndNonclosedTop :
    ∃ z : nhdsKer ({bottom} : Set TwoPointUpper),
      (z : TwoPointUpper) ≠ bottom ∧
      IsClosed ({(⟨bottom, mem_nhdsKer_singleton.mpr (specializes_refl bottom)⟩ :
        nhdsKer ({bottom} : Set TwoPointUpper))} :
          Set (nhdsKer ({bottom} : Set TwoPointUpper))) ∧
      ¬ IsClosed ({z} : Set (nhdsKer ({bottom} : Set TwoPointUpper))) := by
  let z : nhdsKer ({bottom} : Set TwoPointUpper) := ⟨top, allGenerizations.symm ▸ (mem_univ top)⟩
  refine ⟨z, ?_, isClosed_singleton_nhdsKer bottom, ?_⟩
  · change (1 : Fin 2) ≠ 0
    decide
  · intro hclosed
    have heq := (isClosed_singleton_nhdsKer_iff bottom z).mp hclosed
    change (1 : Fin 2) = 0 at heq
    exact (by decide : (1 : Fin 2) ≠ 0) heq

end UpperSet

section Indiscrete

local instance : TopologicalSpace Bool := ⊤

private theorem originalNotClosed :
    ¬ IsClosed ({(⟨false, mem_nhdsKer_singleton.mpr (specializes_refl false)⟩ :
      nhdsKer ({false} : Set Bool))} : Set (nhdsKer ({false} : Set Bool))) := by
  intro hclosed
  have hspec (left right : Bool) : left ⤳ right := by
    apply specializes_iff_nhds.mpr
    simp only [IndiscreteTopology.nhds_eq]
    exact le_rfl
  let original : nhdsKer ({false} : Set Bool) :=
    ⟨false, mem_nhdsKer_singleton.mpr (specializes_refl false)⟩
  let other : nhdsKer ({false} : Set Bool) :=
    ⟨true, mem_nhdsKer_singleton.mpr (hspec true false)⟩
  have hmem : other ∈ ({original} : Set (nhdsKer ({false} : Set Bool))) :=
    ((subtype_specializes_iff original other).mpr (hspec false true)).mem_closed
      hclosed (by simp)
  have hfalse : (true : Bool) = false := congrArg Subtype.val (by simpa using hmem)
  simp at hfalse

end Indiscrete

end SpectralStoneDualityExamples
