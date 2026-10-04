/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.Cofinite

/-!
# Quasi-sobriety of cofinite spaces: boundary cases

The empty and two-point cofinite spaces are sober; an infinite cofinite space is `T₁`
and irreducible but not quasi-sober.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, Exercise 0.2.1, for the infinite cofinite example.
- Mathlib, `Topology.Sober` and `Topology.Constructions`, for the cofinite
  and quasi-sobriety formalization.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open TopologicalSpace

namespace SpectralStoneDualityExamples

example : IsEmpty (CofiniteTopology Empty) :=
  ⟨fun x => isEmptyElim (CofiniteTopology.of.symm x)⟩

example : T1Space (CofiniteTopology Empty) ∧ QuasiSober (CofiniteTopology Empty) :=
  ⟨inferInstance, (CofiniteTopology.quasiSober_iff_finite Empty).mpr inferInstance⟩

example : DiscreteTopology (CofiniteTopology (Fin 2)) := inferInstance

example : ∃ x y : CofiniteTopology (Fin 2), x ≠ y := by
  refine ⟨CofiniteTopology.of (0 : Fin 2), CofiniteTopology.of 1, ?_⟩
  intro h
  exact (by decide : (0 : Fin 2) ≠ 1) (CofiniteTopology.of.injective h)

example : T1Space (CofiniteTopology (Fin 2)) ∧
    QuasiSober (CofiniteTopology (Fin 2)) :=
  ⟨inferInstance, (CofiniteTopology.quasiSober_iff_finite (Fin 2)).mpr inferInstance⟩

example : T1Space (CofiniteTopology ℕ) := inferInstance

example : IrreducibleSpace (CofiniteTopology ℕ) := inferInstance

example : ¬ QuasiSober (CofiniteTopology ℕ) :=
  CofiniteTopology.not_quasiSober ℕ

end SpectralStoneDualityExamples
