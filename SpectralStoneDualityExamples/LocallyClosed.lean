/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.LocallyClosed
public import Mathlib.Topology.Separation.Basic

/-!
# Compact locally closed subspaces: examples and boundaries

The empty space, a proper subset of a finite discrete space, and a finite
indiscrete non-`T₀` space illustrate the conclusions. A finite subset of an
infinite discrete space shows that ambient compactness is unnecessary.

The explicitly named applications of the compact locally closed lemmas use
those results; the finiteness, noninjectivity, and separation checks do not.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set TopologicalSpace Topology

namespace SpectralStoneDualityExamples

section Empty

local instance : TopologicalSpace Empty := ⊥

example : IsRetrocompact (∅ : Set Empty) :=
  isCompact_empty.isRetrocompact_of_isLocallyClosed isClosed_empty.isLocallyClosed

example : PrespectralSpace (∅ : Set Empty) ∧ CompactSpace (∅ : Set Empty) ∧
    QuasiSeparatedSpace (∅ : Set Empty) :=
  isClosed_empty.isLocallyClosed.subtype_prespectral_compact_quasiSeparated isCompact_empty

end Empty

section FiniteDiscrete

local instance : TopologicalSpace (Fin 3) := ⊥

private def twoPoints : Set (Fin 3) := {0, 1}

example : (0 : Fin 3) ∈ twoPoints ∧ (2 : Fin 3) ∉ twoPoints := by
  simp only [twoPoints]
  decide

example : IsRetrocompact twoPoints :=
  (Set.toFinite twoPoints).isCompact.isRetrocompact_of_isLocallyClosed
    (isOpen_discrete twoPoints).isLocallyClosed

example : PrespectralSpace twoPoints ∧ CompactSpace twoPoints ∧
    QuasiSeparatedSpace twoPoints :=
  (isOpen_discrete twoPoints).isLocallyClosed.subtype_prespectral_compact_quasiSeparated
    (Set.toFinite twoPoints).isCompact

end FiniteDiscrete

section NonSeparated

local instance : TopologicalSpace Bool := ⊤
local instance : TopologicalSpace Unit := ⊤

private theorem boolToUnit_inducing : Topology.IsInducing (fun _ : Bool => ()) :=
  ⟨(induced_const).symm⟩

private theorem boolToUnit_spectral : IsSpectralMap (fun _ : Bool => ()) := by
  refine ⟨continuous_const, ?_⟩
  intro U _ _
  exact (Set.toFinite _).isCompact

example : ¬ Function.Injective (fun _ : Bool => ()) := by
  intro hinjective
  exact Bool.false_ne_true (hinjective rfl)

example : ¬ T0Space Bool := by
  intro hT0
  have hInseparable : Inseparable (false : Bool) true :=
    boolToUnit_inducing.inseparable_iff.1 (.of_eq rfl)
  exact Bool.false_ne_true (hT0.t0 hInseparable)

example : QuasiSeparatedSpace Bool :=
  boolToUnit_inducing.quasiSeparatedSpace_of_isSpectralMap boolToUnit_spectral

example : IsRetrocompact (Set.univ : Set Bool) :=
  (Set.toFinite _).isCompact.isRetrocompact_of_isLocallyClosed isClosed_univ.isLocallyClosed

end NonSeparated

section NoncompactAmbient

local instance : TopologicalSpace ℕ := ⊥

private def twoNaturals : Set ℕ := {0, 1}

private theorem twoNaturals_finite : twoNaturals.Finite := by
  simp [twoNaturals]

local instance : PrespectralSpace ℕ :=
  PrespectralSpace.of_isTopologicalBasis (isTopologicalBasis_singletons ℕ) (by
    rintro U ⟨x, rfl⟩
    exact isCompact_singleton)

example : ¬ CompactSpace ℕ := by
  intro hcompact
  exact Set.infinite_univ ((isCompact_univ (X := ℕ)).finite_of_discrete)

example : IsRetrocompact twoNaturals :=
  twoNaturals_finite.isCompact.isRetrocompact_of_isLocallyClosed
    (isOpen_discrete twoNaturals).isLocallyClosed

example : PrespectralSpace twoNaturals ∧ CompactSpace twoNaturals ∧
    QuasiSeparatedSpace twoNaturals :=
  (isOpen_discrete twoNaturals).isLocallyClosed.subtype_prespectral_compact_quasiSeparated
    twoNaturals_finite.isCompact

end NoncompactAmbient

end SpectralStoneDualityExamples
