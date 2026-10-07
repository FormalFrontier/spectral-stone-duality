/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.GenericPoint
public import Mathlib.Logic.Equiv.Bool

/-!
# Relabelling independent generic-point forks

An empty index leaves the generic point, a singleton index adds exactly one
closed point, and Boolean negation exchanges two distinct closed points.
Universe lifting tests relabelling between index types in independent universes.

## References

- Mathlib contributors, `Equiv.boolNot` and `Equiv.ulift`.
- `Topology.WithGenericPoint` for the independent fork and its topology.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open Topology

namespace SpectralStoneDualityExamples.GenericPointReindex

example : Nonempty (WithGenericPoint Empty) := ⟨.generic⟩

example (x : WithGenericPoint Empty) : x = .generic := by
  cases x with
  | generic => rfl
  | closed i => exact i.elim

example : ∃ x : WithGenericPoint PUnit, x ≠ .generic :=
  ⟨.closed PUnit.unit, by simp⟩

example (x : WithGenericPoint PUnit) : x = .generic ∨ x = .closed PUnit.unit := by
  cases x with
  | generic => exact Or.inl rfl
  | closed i => cases i; exact Or.inr rfl

example : IsClosed ({WithGenericPoint.closed PUnit.unit} :
    Set (WithGenericPoint PUnit)) := WithGenericPoint.closed_isClosed PUnit.unit

private theorem closed_false_ne_closed_true :
    (WithGenericPoint.closed false : WithGenericPoint Bool) ≠ .closed true := by
  intro h
  exact (by decide : false ≠ true) (WithGenericPoint.closed.inj h)

example : (WithGenericPoint.closed false : WithGenericPoint Bool) ≠ .closed true :=
  closed_false_ne_closed_true

example : IsClosed ({WithGenericPoint.closed false} : Set (WithGenericPoint Bool)) ∧
    IsClosed ({WithGenericPoint.closed true} : Set (WithGenericPoint Bool)) :=
  ⟨WithGenericPoint.closed_isClosed false, WithGenericPoint.closed_isClosed true⟩

example : Equiv.boolNot false = true ∧ Equiv.boolNot true = false := by decide

example : (WithGenericPoint.reindex Equiv.boolNot)
    (.closed false) = .closed true := by simp

example : (WithGenericPoint.reindex Equiv.boolNot).symm
    (.closed true) = .closed false := by simp

example : ((WithGenericPoint.reindex Equiv.boolNot).trans
    (WithGenericPoint.reindex Equiv.boolNot))
    (.closed false) = .closed false := by simp

example : (WithGenericPoint.reindex (Equiv.boolNot.trans Equiv.boolNot))
    (.closed false) = .closed false := by
  rw [WithGenericPoint.reindex_trans]
  simp

example : (WithGenericPoint.reindex Equiv.boolNot.symm)
    (.closed true) = .closed false := by
  rw [WithGenericPoint.reindex_symm]
  simp

example : WithGenericPoint.reindex (Equiv.boolNot.trans Equiv.boolNot) =
    Homeomorph.refl (WithGenericPoint Bool) := by
  have h : Equiv.boolNot.trans Equiv.boolNot = Equiv.refl Bool := by
    ext x
    cases x <;> decide
  rw [h, WithGenericPoint.reindex_refl]

example : (Equiv.ulift.{u, 0}.symm : Bool ≃ ULift.{u} Bool) false = ⟨false⟩ := rfl

example : (WithGenericPoint.reindex (Equiv.ulift.{u, 0}.symm :
    Bool ≃ ULift.{u} Bool)) (.closed false) = .closed ⟨false⟩ := by simp

example : (WithGenericPoint.reindex (Equiv.ulift.{u, 0}.symm :
    Bool ≃ ULift.{u} Bool)).symm (.closed ⟨true⟩) = .closed true := by simp

end SpectralStoneDualityExamples.GenericPointReindex
