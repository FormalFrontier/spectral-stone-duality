/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Sober
public import Mathlib.Topology.WithTopology

/-!
# Quasi-sobriety of cofinite spaces

A cofinite space is quasi-sober exactly when its underlying type is finite. Cofinite spaces
are `T₁`, so this also characterizes their sobriety, including the empty space.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace CofiniteTopology

/-- A cofinite space is quasi-sober if and only if its underlying type is finite. -/
theorem quasiSober_iff_finite (X : Type u) :
    QuasiSober (CofiniteTopology X) ↔ Finite X := by
  constructor
  · intro h
    rcases finite_or_infinite X with hfinite | hinfinite
    · exact hfinite
    · let : Infinite X := hinfinite
      let : QuasiSober (CofiniteTopology X) := h
      have hsingleton : ({genericPoint (CofiniteTopology X)} :
          Set (CofiniteTopology X)) = Set.univ := by
        simpa only [isClosed_singleton.closure_eq] using
          (genericPoint_closure (CofiniteTopology X))
      have hfinite_univ : (Set.univ : Set (CofiniteTopology X)).Finite :=
        hsingleton ▸ Set.finite_singleton _
      exact False.elim (Set.infinite_univ.not_finite hfinite_univ)
  · intro hfinite
    let : Finite X := hfinite
    let : DiscreteTopology (CofiniteTopology X) := inferInstance
    infer_instance

/-- An infinite cofinite space is not quasi-sober. -/
theorem not_quasiSober (X : Type u) [Infinite X] :
    ¬ QuasiSober (CofiniteTopology X) := by
  intro h
  have : Finite X := (quasiSober_iff_finite X).mp h
  exact not_finite X

end CofiniteTopology
