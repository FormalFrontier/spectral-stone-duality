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

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, Exercise 0.2.1, for the infinite-cofinite-space obstruction;
  the finite/empty characterization here is stronger than that example.
- Mathlib, `Topology.Sober` and `Topology.Constructions`, for quasi-sobriety
  and the cofinite topology.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace CofiniteTopology

/-- A cofinite space is quasi-sober if and only if its underlying type is finite.
The infinite direction specializes Fujiwara--Kato, *Foundations of Rigid Geometry I*,
Exercise 0.2.1; the converse includes the empty case. -/
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

/-- An infinite cofinite space is not quasi-sober; compare the non-sober
example in Fujiwara--Kato, *Foundations of Rigid Geometry I*, Exercise 0.2.1. -/
theorem not_quasiSober (X : Type u) [Infinite X] :
    ¬ QuasiSober (CofiniteTopology X) := by
  intro h
  have : Finite X := (quasiSober_iff_finite X).mp h
  exact not_finite X

end CofiniteTopology
