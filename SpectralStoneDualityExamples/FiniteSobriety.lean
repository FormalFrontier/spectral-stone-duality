/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.Finite
public import SpectralStoneDuality.Topology.Cofinite
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Finite quasi-sobriety: examples and boundaries

The finite-space result includes empty, discrete, Sierpiński and indiscrete spaces.
An infinite cofinite space shows that finiteness cannot be removed in general.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set TopologicalSpace

namespace SpectralStoneDualityExamples

section Empty

local instance : TopologicalSpace Empty := ⊥

-- This empty-space check uses Mathlib's R₁ instance, independently of the finite-set theorem.
example : QuasiSober Empty := inferInstance

example : QuasiSober Empty := instQuasiSoberOfFinite Empty

example : IsEmpty Empty := inferInstance

end Empty

section Discrete

local instance : TopologicalSpace (Fin 2) := ⊥

example : DiscreteTopology (Fin 2) := inferInstance

example : ∃ x y : Fin 2, x ≠ y := ⟨0, 1, by decide⟩

-- This discrete-space check likewise uses Mathlib's R₁ instance.
example : QuasiSober (Fin 2) := inferInstance

end Discrete

section Sierpinski

example : QuasiSober Prop := inferInstance

-- These separation checks do not use generic-point existence.
private theorem sierpinski_not_t1 : ¬ T1Space Prop := by
  intro h
  have hspec : (True : Prop) ⤳ False :=
    (specializes_iff_nhds).2 (by rw [nhds_false]; exact le_top)
  exact Eq.mp (t1Space_iff_specializes_imp_eq.mp h hspec) True.intro

example : ¬ T1Space Prop := sierpinski_not_t1

example : ¬ T2Space Prop := by
  intro h
  exact sierpinski_not_t1 (@T2Space.t1Space Prop _ h)

end Sierpinski

section Indiscrete

local instance : TopologicalSpace Bool := ⊤

-- The whole two-point space is irreducible, so this exercises the finite-set statement.
example : ∃ x ∈ (Set.univ : Set Bool),
    IsGenericPoint x (closure (Set.univ : Set Bool)) := by
  have hirr : IsIrreducible (Set.univ : Set Bool) :=
    ⟨Set.univ_nonempty, PreirreducibleSpace.isPreirreducible_univ⟩
  exact hirr.exists_isGenericPoint_closure_of_finite (Set.toFinite _)

example : QuasiSober Bool := inferInstance

-- Both generic points and the failure of T₀ are checked independently.
example : ¬ T0Space Bool := by
  intro h
  exact Bool.false_ne_true
    ((t0Space_iff_inseparable Bool).mp h false true (Inseparable.all false true))

example : false ≠ true ∧ IsGenericPoint false (Set.univ : Set Bool) ∧
    IsGenericPoint true (Set.univ : Set Bool) := by
  refine ⟨Bool.false_ne_true, ?_, ?_⟩
  · exact closure_indiscrete (Set.singleton_nonempty false)
  · exact closure_indiscrete (Set.singleton_nonempty true)

end Indiscrete

-- The cofinite counterexample is independent of the finite-space result.
example : ¬ QuasiSober (CofiniteTopology ℕ) :=
  CofiniteTopology.not_quasiSober ℕ

end SpectralStoneDualityExamples
