/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.Category.Soberification
public import SpectralStoneDuality.Topology.Cofinite
public import SpectralStoneDuality.Topology.Finite

/-!
# Boundary examples for soberification

An empty space has no irreducible closed subsets. An indiscrete two-point space has a
noninjective unit, whereas the unit for an infinite cofinite space embeds its points but
misses an irreducible closed subset.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set TopologicalSpace TopologicalSpace.IrreducibleCloseds CategoryTheory

example : IsEmpty (IrreducibleCloseds Empty) := ⟨by
  intro F
  obtain ⟨x, _⟩ := F.isIrreducible.nonempty
  exact x.elim⟩

section IndiscreteBool

local instance : TopologicalSpace Bool := ⊤

example : ¬ Function.Injective (unit Bool) := by
  intro hinj
  have h : unit Bool false = unit Bool true :=
    (unit_eq_iff_inseparable false true).2 (Inseparable.all false true)
  exact Bool.false_ne_true (hinj h)

end IndiscreteBool

section Sierpinski

private theorem prop_eq_true_of (proposition : Prop) (h : proposition) : proposition = True :=
  propext ⟨fun _ => trivial, fun _ => h⟩

private theorem prop_eq_false_of_not (proposition : Prop) (h : ¬ proposition) :
    proposition = False :=
  propext ⟨h, False.elim⟩

private theorem closure_true : closure ({True} : Set Prop) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro proposition
  by_cases hp : proposition
  · rw [prop_eq_true_of proposition hp]
    exact subset_closure (by simp)
  · rw [prop_eq_false_of_not proposition hp]
    exact (specializes_iff_mem_closure).1
      ((specializes_iff_nhds).2 (by rw [nhds_false]; exact le_top))

private instance : T0Space Prop := by
  refine (t0Space_iff_inseparable Prop).2 ?_
  intro proposition other h
  apply propext
  simpa using (inseparable_iff_forall_isOpen.1 h)
    ({True} : Set Prop) isOpen_singleton_true

example : Function.Surjective (unit Prop) := (unitHomeomorph Prop).surjective

private def soberProp : SoberTopCat.{0} :=
  ⟨TopCat.of Prop, ⟨inferInstance, inferInstance⟩⟩

private def propIdentity : TopCat.of Prop ⟶ soberInclusion.obj soberProp :=
  TopCat.ofHom (ContinuousMap.id Prop)

example (U : Opens Prop) (F : IrreducibleCloseds Prop) :
    F ∈ opensOrderIso Prop U ↔ ((F : Set Prop) ∩ (U : Set Prop)).Nonempty := by
  rw [opensOrderIso_apply]
  exact mem_openSet U F

example (V : Opens (IrreducibleCloseds Prop)) (p : Prop) :
    p ∈ (opensOrderIso Prop).symm V ↔ unit Prop p ∈ V := by
  rw [opensOrderIso_symm_apply]
  rfl

example (p : Prop) : ((unitHomeomorph Prop p : IrreducibleCloseds Prop) : Set Prop) =
    closure {p} := by
  rw [unitHomeomorph_apply, coe_unit_apply]

example (F : IrreducibleCloseds Prop) :
    (unitHomeomorph Prop).symm F ∈ (F : Set Prop) := by
  rw [unitHomeomorph_symm_apply]
  exact (F.isIrreducible.isGenericPoint_genericPoint F.isClosed).mem

example (F : IrreducibleCloseds Prop) :
    (soberification.map (𝟙 (TopCat.of Prop))).hom.hom F = F := by
  rw [soberification_map_apply]
  exact map_id F

example (p : Prop) :
    ((soberificationHomEquiv (TopCat.of Prop) soberProp).symm
      propIdentity).hom.hom (unit Prop p) = p := by
  rw [soberificationHomEquiv_symm_apply]
  exact congrArg (fun f : C(Prop, Prop) => f p) (extend_comp_unit (ContinuousMap.id Prop))

example (p : Prop) :
    (soberificationAdjunction.unit.app (TopCat.of Prop)).hom p = unit Prop p := by
  rw [soberificationAdjunction_unit_app]
  rfl

example : ¬ T2Space Prop := by
  intro h
  let : T2Space Prop := h
  have hclosed : closure ({True} : Set Prop) = ({True} : Set Prop) :=
    isClosed_singleton.closure_eq
  have hfalse : (False : Prop) ∈ ({True} : Set Prop) := by
    rw [← hclosed, closure_true]
    trivial
  simp at hfalse

end Sierpinski

private def cofiniteGeneric : IrreducibleCloseds (CofiniteTopology ℕ) :=
  ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩

example : T0Space (CofiniteTopology ℕ) := inferInstance

example : ¬ Function.Surjective (unit (CofiniteTopology ℕ)) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj cofiniteGeneric
  have hclosure : closure ({x} : Set (CofiniteTopology ℕ)) = Set.univ := by
    simpa only [coe_unit_apply, cofiniteGeneric, coe_mk] using congrArg
      (fun F : IrreducibleCloseds (CofiniteTopology ℕ) =>
        (F : Set (CofiniteTopology ℕ))) hx
  have hsingleton : ({x} : Set (CofiniteTopology ℕ)) = Set.univ := by
    simpa only [isClosed_singleton.closure_eq] using hclosure
  have hzero : CofiniteTopology.of 0 = x := by
    apply Set.mem_singleton_iff.mp
    rw [hsingleton]
    trivial
  have hone : CofiniteTopology.of 1 = x := by
    apply Set.mem_singleton_iff.mp
    rw [hsingleton]
    trivial
  exact Nat.zero_ne_one (CofiniteTopology.of.injective (hzero.trans hone.symm))

example : ¬ QuasiSober (CofiniteTopology ℕ) :=
  CofiniteTopology.not_quasiSober ℕ

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

example (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    map g g.continuous (map f f.continuous (unit X x)) = unit Z (g (f x)) := by
  simp only [map_unit]
