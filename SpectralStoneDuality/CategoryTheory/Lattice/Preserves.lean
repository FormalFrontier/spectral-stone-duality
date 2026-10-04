/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Lattice
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Finite-limit and finite-colimit preserving functors of bounded lattices

The underlying order category of a bounded lattice has finite limits given by
finite meets and finite colimits given by finite joins. A functor between two
such categories preserving both kinds of finite diagrams therefore determines
a bounded lattice homomorphism. Conversely, the functor associated to a
bounded lattice homomorphism preserves both kinds of diagrams.

These are functors between the order categories of lattice elements, not
functors between categories whose objects are lattices.
Distributivity in the motivating special case is unnecessary for this
finite-(co)limit characterization.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §1.2(e) and §2.2(b), for the order-category convention and the
  finite-(co)limit description of maps of bounded distributive lattices.
  The characterization here works without distributivity.
- Mathlib, `CategoryTheory.Limits.Preserves.Lattice` and
  `CategoryTheory.Limits.Preorder`, for the forward preservation instances
  and finite-diagram descriptions used in the converse.
-/

@[expose] public section

universe u v

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {A : Type u} {B : Type v}

/-- A functor preserving finite limits preserves the top element of order categories. -/
theorem map_top_of_preservesFiniteLimits [PartialOrder A] [OrderTop A]
    [PartialOrder B] [OrderTop B] (F : A ⥤ B) [PreservesFiniteLimits F] :
    F.obj ⊤ = ⊤ := by
  apply le_antisymm le_top
  exact ((Preorder.isTerminalTop A).isTerminalObj F (⊤ : A)).from (⊤ : B) |>.le

/-- A functor preserving finite limits preserves binary infima of order categories. -/
theorem map_inf_of_preservesFiniteLimits [SemilatticeInf A]
    [SemilatticeInf B] (F : A ⥤ B) [PreservesFiniteLimits F]
    (a b : A) : F.obj (a ⊓ b) = F.obj a ⊓ F.obj b := by
  exact ((mapIsLimitOfPreservesOfIsLimit F _ _
    (Preorder.isLimitBinaryFan a b)).conePointUniqueUpToIso
      (Preorder.isLimitBinaryFan (F.obj a) (F.obj b))).to_eq

/-- A functor preserving finite colimits preserves the bottom element of order categories. -/
theorem map_bot_of_preservesFiniteColimits [PartialOrder A] [OrderBot A]
    [PartialOrder B] [OrderBot B] (F : A ⥤ B) [PreservesFiniteColimits F] :
    F.obj ⊥ = ⊥ := by
  apply le_antisymm
  · exact ((Preorder.isInitialBot A).isInitialObj F (⊥ : A)).to (⊥ : B) |>.le
  · exact bot_le

/-- A functor preserving finite colimits preserves binary suprema of order categories. -/
theorem map_sup_of_preservesFiniteColimits [SemilatticeSup A]
    [SemilatticeSup B] (F : A ⥤ B) [PreservesFiniteColimits F]
    (a b : A) : F.obj (a ⊔ b) = F.obj a ⊔ F.obj b := by
  exact ((mapIsColimitOfPreservesOfIsColimit F _ _
    (Preorder.isColimitBinaryCofan a b)).coconePointUniqueUpToIso
      (Preorder.isColimitBinaryCofan (F.obj a) (F.obj b))).to_eq

/-- A finite-limit- and finite-colimit-preserving functor between the order
categories of bounded lattices, as a bounded lattice homomorphism. -/
def toBoundedLatticeHom [Lattice A] [BoundedOrder A] [Lattice B] [BoundedOrder B]
    (F : A ⥤ B) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    BoundedLatticeHom A B where
  toFun := F.obj
  map_sup' := F.map_sup_of_preservesFiniteColimits
  map_inf' := F.map_inf_of_preservesFiniteLimits
  map_top' := F.map_top_of_preservesFiniteLimits
  map_bot' := F.map_bot_of_preservesFiniteColimits

@[simp]
theorem toBoundedLatticeHom_apply [Lattice A] [BoundedOrder A]
    [Lattice B] [BoundedOrder B] (F : A ⥤ B)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (a : A) :
    F.toBoundedLatticeHom a = F.obj a := rfl

/-- Reinterpreting the bounded lattice map of a preserving functor as an order
functor recovers the original functor. -/
theorem toBoundedLatticeHom_toFunctor [Lattice A] [BoundedOrder A]
    [Lattice B] [BoundedOrder B] (F : A ⥤ B)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (OrderHom.ofClass F.toBoundedLatticeHom).toFunctor = F := by
  apply (OrderHom.equivFunctor (X := A) (Y := B)).symm.injective
  ext a
  rfl

end CategoryTheory.Functor

namespace BoundedLatticeHom

open CategoryTheory CategoryTheory.Limits

variable {A : Type u} {B : Type v} [Lattice A] [BoundedOrder A]
    [Lattice B] [BoundedOrder B]

/-- Reinterpreting a bounded lattice homomorphism as a functor and recovering
its object map gives back the original homomorphism. -/
@[simp]
theorem toFunctor_toBoundedLatticeHom (f : BoundedLatticeHom A B) :
    ((OrderHom.ofClass f).toFunctor).toBoundedLatticeHom = f := by
  ext a
  rfl

/-- Bounded lattice homomorphisms correspond to functors of their order
categories preserving finite limits and finite colimits. This generalizes the
bounded distributive-lattice statement in Fujiwara--Kato,
*Foundations of Rigid Geometry I*, §2.2(b), without distributivity. -/
def equivFiniteLimitColimitPreservingFunctor :
    BoundedLatticeHom A B ≃
      {F : A ⥤ B // PreservesFiniteLimits F ∧ PreservesFiniteColimits F} where
  toFun f := ⟨(OrderHom.ofClass f).toFunctor, inferInstance, inferInstance⟩
  invFun F :=
    letI := F.property.1
    letI := F.property.2
    F.val.toBoundedLatticeHom
  left_inv f := toFunctor_toBoundedLatticeHom f
  right_inv F := by
    apply Subtype.ext
    have : PreservesFiniteLimits F.val := F.property.1
    have : PreservesFiniteColimits F.val := F.property.2
    exact F.val.toBoundedLatticeHom_toFunctor

end BoundedLatticeHom
