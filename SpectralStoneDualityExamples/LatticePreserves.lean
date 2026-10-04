/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.CategoryTheory.Lattice.Preserves

/-!
# Examples of finite-(co)limit preservation for bounded lattices

Identity, a nonconstant projection of a Boolean square, and the one-element
lattice instantiate the bounded lattice map associated to a preserving functor.
The constant-bottom and constant-top order functors preserve binary meets and
joins but fail to preserve a nullary operation. Their opposite one-sided
finite-preservation instances follow from Mathlib independently of the
construction of a bounded lattice homomorphism from a functor.
The Boolean square carries its order category, rather than the product
category structure on two copies of the Boolean order category.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.2(b), for finite-(co)limit preservation by maps of bounded
  distributive lattices; the example API does not assume distributivity.
- Mathlib, `CategoryTheory.Limits.Preserves.Lattice`, for the forward
  preservation instances used by the examples.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

local instance : SmallCategory (Bool × Bool) := Preorder.smallCategory (Bool × Bool)

private def firstProjection : BoundedLatticeHom (Bool × Bool) Bool where
  toFun := Prod.fst
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl

example : PreservesFiniteLimits
    (OrderHom.ofClass (BoundedLatticeHom.id Bool)).toFunctor := inferInstance

example : ((OrderHom.ofClass (BoundedLatticeHom.id Bool)).toFunctor).toBoundedLatticeHom
    = BoundedLatticeHom.id Bool := BoundedLatticeHom.toFunctor_toBoundedLatticeHom _

example : PreservesFiniteColimits (OrderHom.ofClass firstProjection).toFunctor :=
  inferInstance

example : ((OrderHom.ofClass firstProjection).toFunctor).toBoundedLatticeHom (true, false)
    = true := by
  simp [firstProjection]

example : ((OrderHom.ofClass firstProjection).toFunctor).toBoundedLatticeHom
    = firstProjection := BoundedLatticeHom.toFunctor_toBoundedLatticeHom _

example : (BoundedLatticeHom.equivFiniteLimitColimitPreservingFunctor firstProjection).val.obj
    (true, false) = true := rfl

example : (BoundedLatticeHom.equivFiniteLimitColimitPreservingFunctor firstProjection).val.obj
    (false, true) = false := rfl

example : ((OrderHom.ofClass (BoundedLatticeHom.id (Fin 1))).toFunctor).toBoundedLatticeHom
    = BoundedLatticeHom.id (Fin 1) := BoundedLatticeHom.toFunctor_toBoundedLatticeHom _

example (a : Fin 1) :
    ((OrderHom.ofClass (BoundedLatticeHom.id (Fin 1))).toFunctor).obj a = 0 :=
  Subsingleton.elim _ _

private def constantBottom : SupBotHom Bool Bool where
  toFun := fun _ => ⊥
  map_sup' _ _ := by simp
  map_bot' := rfl

private def constantTop : InfTopHom Bool Bool where
  toFun := fun _ => ⊤
  map_inf' _ _ := by simp
  map_top' := rfl

example : PreservesFiniteColimits (OrderHom.ofClass constantBottom).toFunctor :=
  inferInstance

example : PreservesFiniteLimits (OrderHom.ofClass constantTop).toFunctor :=
  inferInstance

example (a b : Bool) :
    ((OrderHom.ofClass constantBottom).toFunctor).obj (a ⊓ b) =
      ((OrderHom.ofClass constantBottom).toFunctor).obj a ⊓
        ((OrderHom.ofClass constantBottom).toFunctor).obj b := by
  simp [constantBottom]

example (a b : Bool) :
    ((OrderHom.ofClass constantBottom).toFunctor).obj (a ⊔ b) =
      ((OrderHom.ofClass constantBottom).toFunctor).obj a ⊔
        ((OrderHom.ofClass constantBottom).toFunctor).obj b := by
  simp [constantBottom]

example (a b : Bool) :
    ((OrderHom.ofClass constantTop).toFunctor).obj (a ⊔ b) =
      ((OrderHom.ofClass constantTop).toFunctor).obj a ⊔
        ((OrderHom.ofClass constantTop).toFunctor).obj b := by
  simp [constantTop]

example (a b : Bool) :
    ((OrderHom.ofClass constantTop).toFunctor).obj (a ⊓ b) =
      ((OrderHom.ofClass constantTop).toFunctor).obj a ⊓
        ((OrderHom.ofClass constantTop).toFunctor).obj b := by
  simp [constantTop]

example : ((OrderHom.ofClass constantBottom).toFunctor).obj ⊤ ≠ (⊤ : Bool) := by
  decide

example : ((OrderHom.ofClass constantTop).toFunctor).obj ⊥ ≠ (⊥ : Bool) := by
  decide

example : ¬ PreservesFiniteLimits (OrderHom.ofClass constantBottom).toFunctor := by
  intro h
  exact (by decide : ((OrderHom.ofClass constantBottom).toFunctor).obj ⊤ ≠ (⊤ : Bool))
    ((OrderHom.ofClass constantBottom).toFunctor.map_top_of_preservesFiniteLimits)

example : ¬ PreservesFiniteColimits (OrderHom.ofClass constantTop).toFunctor := by
  intro h
  exact (by decide : ((OrderHom.ofClass constantTop).toFunctor).obj ⊥ ≠ (⊥ : Bool))
    ((OrderHom.ofClass constantTop).toFunctor.map_bot_of_preservesFiniteColimits)
