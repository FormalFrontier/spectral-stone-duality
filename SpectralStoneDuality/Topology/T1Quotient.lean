/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Setoid.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Separation.Basic

/-!
# The T₁ quotient of a topological space

The setoid `t1Setoid X` is the infimum of all setoids on `X` whose equivalence
classes are closed. The space `T1Quotient X` is its quotient with the ordinary
quotient topology. Closedness is required of the classes, not of the relation's
graph in the product space.

`T1Quotient.unit` is universal among continuous maps from `X` to T₁ spaces.
`T1Quotient.lift` constructs the factored map, and `T1Quotient.map` gives the
induced map of quotients for every continuous map. The source and target may lie
in independent universes. No separation or nonemptiness assumption is imposed
on the source.

For an already T₁ space, `T1Quotient.homeomorph` identifies the space with its
quotient. Under `R0Space X`, `T1Quotient.separationQuotientHomeomorph` compares
this construction with Mathlib's `SeparationQuotient X`. The latter is a T₀
quotient and is not the T₁ quotient for arbitrary `X`.

## References

- Mathlib's setoid, quotient topology, continuous-map descent and separation
  libraries provide the underlying quotient constructions and interfaces.
- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.3(c), study separated quotients of valuative spaces. The
  construction here applies to arbitrary topological spaces; identification with
  a maximal-point presentation is a separate question.
-/

@[expose] public section

noncomputable section

universe u v w

open Set Topology
open scoped Function

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The setoids on `X` for which every equivalence class is closed. -/
def closedClassSetoids (X : Type u) [TopologicalSpace X] : Set (Setoid X) :=
  {r | ∀ x, IsClosed {y | r x y}}

/-- Membership in `closedClassSetoids` means closedness of every equivalence class. -/
@[simp]
theorem mem_closedClassSetoids {r : Setoid X} :
    r ∈ closedClassSetoids X ↔ ∀ x, IsClosed {y | r x y} :=
  Iff.rfl

/-- The infimum of all setoids on `X` with closed equivalence classes. -/
def t1Setoid (X : Type u) [TopologicalSpace X] : Setoid X :=
  sInf (closedClassSetoids X)

/-- Two points are `t1Setoid`-equivalent exactly when every closed-class setoid relates them. -/
theorem t1Setoid_iff {x y : X} :
    t1Setoid X x y ↔ ∀ r ∈ closedClassSetoids X, r x y :=
  Setoid.sInf_iff

/-- Every equivalence class of `t1Setoid X` is closed. -/
theorem isClosed_t1Setoid_class (x : X) : IsClosed {y | t1Setoid X x y} := by
  have h : {y | t1Setoid X x y} = ⋂ r ∈ closedClassSetoids X, {y | r x y} := by
    ext y
    simp only [mem_ofPred_eq, mem_iInter, t1Setoid_iff]
  rw [h]
  exact isClosed_iInter fun r => isClosed_iInter fun hr => (mem_closedClassSetoids.mp hr) x

/-- The quotient by the infimum of all closed-class setoids, with the quotient topology. -/
def T1Quotient (X : Type u) [TopologicalSpace X] : Type u :=
  Quotient (t1Setoid X)

namespace T1Quotient

/-- The ordinary quotient topology on `T1Quotient X`. -/
instance instTopologicalSpace (X : Type u) [TopologicalSpace X] :
    TopologicalSpace (T1Quotient X) :=
  inferInstanceAs (TopologicalSpace (Quotient (t1Setoid X)))

/-- The continuous quotient map from a space to its T₁ quotient. -/
def unit (X : Type u) [TopologicalSpace X] : C(X, T1Quotient X) where
  toFun := Quotient.mk (t1Setoid X)
  continuous_toFun := continuous_quotient_mk'

/-- The unit is the setoid quotient map on points. -/
theorem unit_apply (x : X) : unit X x = Quotient.mk (t1Setoid X) x :=
  rfl

/-- The topology on `T1Quotient X` is the quotient topology of its unit. -/
theorem isQuotientMap_unit : IsQuotientMap (unit X) :=
  isQuotientMap_quotient_mk'

/-- Unit fibres are characterized by all setoids with closed equivalence classes. -/
theorem unit_eq_unit_iff (x y : X) :
    unit X x = unit X y ↔ ∀ r ∈ closedClassSetoids X, r x y :=
  Setoid.quotient_mk_sInf_eq

/-- The quotient of any topological space by `t1Setoid` is T₁. -/
instance instT1Space (X : Type u) [TopologicalSpace X] : T1Space (T1Quotient X) := by
  refine ⟨fun q => ?_⟩
  obtain ⟨x, rfl⟩ := isQuotientMap_unit.surjective q
  apply ((Topology.isQuotientMap_iff_isClosed.mp isQuotientMap_unit).2 {unit X x}).mpr
  have h : unit X ⁻¹' {unit X x} = {y | t1Setoid X x y} := by
    ext y
    change unit X y = unit X x ↔ t1Setoid X x y
    rw [eq_comm]
    exact (unit_eq_unit_iff x y).trans t1Setoid_iff.symm
  rw [h]
  exact isClosed_t1Setoid_class x

/-- Specializing points have the same image in the T₁ quotient. -/
theorem unit_eq_of_specializes {x y : X} (h : x ⤳ y) : unit X x = unit X y :=
  (h.map (unit X).continuous).eq

/-- Continuous maps out of the quotient are determined by their composites with the unit. -/
@[ext]
theorem continuousMap_ext {f g : C(T1Quotient X, Y)}
    (h : ∀ x, f (unit X x) = g (unit X x)) : f = g := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨x, rfl⟩ := isQuotientMap_unit.surjective q
  exact h x

/-- A continuous map into a T₁ space identifies every `t1Setoid`-equivalent pair. -/
theorem eq_of_t1Setoid [T1Space Y] (f : C(X, Y)) {x y : X}
    (h : t1Setoid X x y) : f x = f y := by
  have hker : Setoid.ker f ∈ closedClassSetoids X := by
    rw [mem_closedClassSetoids]
    intro x
    have hs : {y | Setoid.ker f x y} = f ⁻¹' {f x} := by
      ext y
      exact Setoid.ker_def.trans eq_comm
    rw [hs]
    exact (isClosed_singleton : IsClosed ({f x} : Set Y)).preimage f.continuous
  exact Setoid.ker_def.mp (t1Setoid_iff.mp h _ hker)

/-- Factor a continuous map to any T₁ space through the T₁ quotient using `Quotient.lift`. -/
def lift [T1Space Y] (f : C(X, Y)) : C(T1Quotient X, Y) where
  toFun := Quotient.lift f (fun _ _ h => eq_of_t1Setoid f h)
  continuous_toFun :=
    f.continuous.quotient_lift (s := t1Setoid X) (fun _ _ h => eq_of_t1Setoid f h)

/-- Evaluating the factored map on a unit image recovers the original map. -/
@[simp]
theorem lift_unit [T1Space Y] (f : C(X, Y)) (x : X) :
    lift f (unit X x) = f x :=
  rfl

/-- The characteristic factorization equation for `lift`. -/
@[simp]
theorem lift_comp_unit [T1Space Y] (f : C(X, Y)) : (lift f).comp (unit X) = f :=
  ContinuousMap.ext (lift_unit f)

/-- A continuous factor through the unit is uniquely determined. -/
theorem lift_unique [T1Space Y] (f : C(X, Y)) (g : C(T1Quotient X, Y))
    (h : g.comp (unit X) = f) : g = lift f := by
  apply continuousMap_ext
  intro x
  rw [lift_unit]
  exact congrArg (fun k : C(X, Y) => k x) h

/-- Every continuous map to every T₁ target has a unique continuous factor through the unit. -/
theorem existsUnique_lift [T1Space Y] (f : C(X, Y)) :
    ∃! g : C(T1Quotient X, Y), g.comp (unit X) = f :=
  ⟨lift f, lift_comp_unit f, fun g h => lift_unique f g h⟩

/-- The continuous map on T₁ quotients induced by a continuous map of spaces. -/
def map (f : C(X, Y)) : C(T1Quotient X, T1Quotient Y) :=
  lift ((unit Y).comp f)

/-- The induced map commutes with the units on points. -/
@[simp]
theorem map_unit (f : C(X, Y)) (x : X) :
    map f (unit X x) = unit Y (f x) :=
  lift_unit ((unit Y).comp f) x

/-- The naturality square for the continuous unit. -/
theorem map_comp_unit (f : C(X, Y)) :
    (map f).comp (unit X) = (unit Y).comp f :=
  lift_comp_unit ((unit Y).comp f)

/-- The naturality square uniquely determines the induced continuous map. -/
theorem map_unique (f : C(X, Y)) (g : C(T1Quotient X, T1Quotient Y))
    (h : g.comp (unit X) = (unit Y).comp f) : g = map f :=
  lift_unique ((unit Y).comp f) g h

/-- Passing to the T₁ quotient preserves identity maps. -/
@[simp]
theorem map_id : map (ContinuousMap.id X) = ContinuousMap.id (T1Quotient X) := by
  apply continuousMap_ext
  intro x
  exact map_unit (ContinuousMap.id X) x

/-- Passing to the T₁ quotient preserves composition across independent universes. -/
@[simp]
theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) :
    map (g.comp f) = (map g).comp (map f) := by
  apply continuousMap_ext
  intro x
  calc
    map (g.comp f) (unit X x) = unit Z (g (f x)) := map_unit (g.comp f) x
    _ = map g (unit Y (f x)) := (map_unit g (f x)).symm
    _ = map g (map f (unit X x)) := congrArg (map g) (map_unit f x).symm

/-- For a T₁ source, its unit does not identify distinct points. -/
theorem unit_injective [T1Space X] : Function.Injective (unit X) := by
  intro x y h
  exact eq_of_t1Setoid (ContinuousMap.id X)
    (t1Setoid_iff.mpr ((unit_eq_unit_iff x y).mp h))

/-- An already T₁ space is homeomorphic to its T₁ quotient via the unit. -/
def homeomorph (X : Type u) [TopologicalSpace X] [T1Space X] : X ≃ₜ T1Quotient X where
  toEquiv :=
    { toFun := unit X
      invFun := lift (ContinuousMap.id X)
      left_inv := lift_unit (ContinuousMap.id X)
      right_inv := by
        intro q
        obtain ⟨x, rfl⟩ := isQuotientMap_unit.surjective q
        rw [lift_unit, ContinuousMap.id_apply] }
  continuous_toFun := (unit X).continuous
  continuous_invFun := (lift (ContinuousMap.id X)).continuous

/-- The homeomorphism for a T₁ space is the unit on points. -/
@[simp]
theorem homeomorph_apply [T1Space X] (x : X) : homeomorph X x = unit X x :=
  rfl

/-- The inverse homeomorphism sends a unit image back to its representative. -/
@[simp]
theorem homeomorph_symm_apply_unit [T1Space X] (x : X) :
    (homeomorph X).symm (unit X x) = x :=
  lift_unit (ContinuousMap.id X) x

/-- Under R₀, the T₁ quotient identifies exactly the inseparable points. -/
theorem unit_eq_unit_iff_inseparable [R0Space X] (x y : X) :
    unit X x = unit X y ↔ Inseparable x y := by
  let : T1Space (SeparationQuotient X) := SeparationQuotient.t1Space_iff.mpr inferInstance
  let f : C(X, SeparationQuotient X) :=
    ⟨SeparationQuotient.mk, SeparationQuotient.isQuotientMap_mk.continuous⟩
  constructor
  · intro h
    apply SeparationQuotient.mk_eq_mk.mp
    calc
      SeparationQuotient.mk x = lift f (unit X x) := (lift_unit f x).symm
      _ = lift f (unit X y) := congrArg (lift f) h
      _ = SeparationQuotient.mk y := lift_unit f y
  · intro h
    exact unit_eq_of_specializes h.specializes

/-- For an R₀ space, the T₁ quotient agrees homeomorphically with Mathlib's T₀ quotient. -/
def separationQuotientHomeomorph (X : Type u) [TopologicalSpace X] [R0Space X] :
    T1Quotient X ≃ₜ SeparationQuotient X := by
  letI : T1Space (SeparationQuotient X) := SeparationQuotient.t1Space_iff.mpr inferInstance
  let f : C(X, SeparationQuotient X) :=
    ⟨SeparationQuotient.mk, SeparationQuotient.isQuotientMap_mk.continuous⟩
  have hf (x : X) : f x = SeparationQuotient.mk x := rfl
  refine
    { toEquiv :=
        { toFun := lift f
          invFun := SeparationQuotient.lift (unit X)
            (fun _ _ h => unit_eq_of_specializes h.specializes)
          left_inv := ?_
          right_inv := ?_ }
      continuous_toFun := (lift f).continuous
      continuous_invFun := SeparationQuotient.continuous_lift_iff.mpr (unit X).continuous }
  · intro q
    obtain ⟨x, rfl⟩ := isQuotientMap_unit.surjective q
    simpa only [lift_unit, hf] using
      (SeparationQuotient.lift_mk (f := unit X)
        (fun _ _ h => unit_eq_of_specializes h.specializes) x)
  · intro q
    obtain ⟨x, rfl⟩ := SeparationQuotient.isQuotientMap_mk.surjective q
    simpa only [SeparationQuotient.lift_mk, hf] using (lift_unit f x)

/-- The R₀ comparison homeomorphism intertwines the two quotient maps. -/
@[simp]
theorem separationQuotientHomeomorph_unit [R0Space X] (x : X) :
    separationQuotientHomeomorph X (unit X x) = SeparationQuotient.mk x :=
  rfl

/-- The inverse R₀ comparison homeomorphism intertwines the two quotient maps. -/
@[simp]
theorem separationQuotientHomeomorph_symm_mk [R0Space X] (x : X) :
    (separationQuotientHomeomorph X).symm (SeparationQuotient.mk x) = unit X x :=
  SeparationQuotient.lift_mk (f := unit X)
    (fun _ _ h => unit_eq_of_specializes h.specializes) x

end T1Quotient
