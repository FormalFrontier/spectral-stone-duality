/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Constructible

/-!
# Tube predicates and finite union duality

A tube-closed subset is the closure of a retrocompact open subset. A tube-open subset
has tube-closed complement. These predicates are the natural generalization to arbitrary
topological spaces of Fujiwara–Kato's Definition 2.3.4 for valuative spaces.
Retrocompactness is relative to the ambient space; no global compactness or separation
assumption is imposed.

## Main definitions and results

* `IsTubeClosed` and `IsTubeOpen` define the two predicates.
* `isTubeClosed_iff` and `IsTubeClosed.closure` give the witness characterization and
  construction of tube-closed sets.
* `isTubeClosed_compl_iff` and `isTubeOpen_compl_iff` express complement duality.
* `IsTubeClosed.isClosed` and `IsTubeOpen.isOpen` relate the predicates to the topology.
* `IsTubeClosed.sUnion` proves stability under finite set-family unions, and
  `IsTubeOpen.sInter` proves the complementary finite-intersection law.
  Empty families are included, with simp lemmas for the empty and universal sets.

The finite-union result and its complementary dual generalize the union-side part of
Fujiwara–Kato's Corollary 2.3.8 to arbitrary topological spaces. The proofs use the existing
finite-union operations for retrocompact sets and topological closure.

## References

* Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*,
  arXiv:1308.4734v5 (2017), Definition 2.3.4 and the union-side part of
  Corollary 2.3.8, printed pages 48–49.
-/

@[expose] public section

universe u

open Set

variable {X : Type u} [TopologicalSpace X] {s U : Set X}

/-- A set is tube closed if it is the closure of a retrocompact open subset.
This naturally generalizes Fujiwara–Kato, Definition 2.3.4, from valuative spaces
to arbitrary topological spaces. -/
def IsTubeClosed (s : Set X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ IsRetrocompact U ∧ closure U = s

/-- A set is tube open if its complement is tube closed.
This naturally generalizes Fujiwara–Kato, Definition 2.3.4, to arbitrary topological spaces. -/
def IsTubeOpen (s : Set X) : Prop :=
  IsTubeClosed sᶜ

/-- The witness characterization of a tube-closed set. This is not a simp rule:
normal simplification retains the predicate rather than introducing an existential. -/
theorem isTubeClosed_iff :
    IsTubeClosed s ↔ ∃ U : Set X, IsOpen U ∧ IsRetrocompact U ∧ closure U = s :=
  Iff.rfl

/-- A retrocompact open subset supplies a tube-closed closure. -/
theorem IsTubeClosed.closure (hUopen : IsOpen U) (hUretrocompact : IsRetrocompact U) :
    IsTubeClosed (closure U) :=
  ⟨U, hUopen, hUretrocompact, rfl⟩

/-- Complementation exchanges tube closed and tube open, removing the complement
from the predicate's argument in simp normal form. -/
@[simp] theorem isTubeClosed_compl_iff : IsTubeClosed sᶜ ↔ IsTubeOpen s :=
  Iff.rfl

/-- Complementation exchanges tube open and tube closed. -/
@[simp] theorem isTubeOpen_compl_iff : IsTubeOpen sᶜ ↔ IsTubeClosed s := by
  simp only [IsTubeOpen, compl_compl]

/-- A tube-closed set is closed in the original topology. -/
theorem IsTubeClosed.isClosed (hs : IsTubeClosed s) : IsClosed s := by
  rcases hs with ⟨U, _, _, rfl⟩
  exact isClosed_closure

/-- A tube-open set is open in the original topology. -/
theorem IsTubeOpen.isOpen (hs : IsTubeOpen s) : IsOpen s := by
  simpa only [compl_compl] using (IsTubeClosed.isClosed hs).isOpen_compl

/-- The empty set is tube closed, with the empty open representative. -/
@[simp] theorem isTubeClosed_empty : IsTubeClosed (∅ : Set X) :=
  ⟨∅, isOpen_empty, IsRetrocompact.empty, closure_empty⟩

/-- The whole space is tube closed, with the whole-space open representative. -/
@[simp] theorem isTubeClosed_univ : IsTubeClosed (univ : Set X) :=
  ⟨univ, isOpen_univ, IsRetrocompact.univ, closure_univ⟩

/-- The empty set is tube open. -/
@[simp] theorem isTubeOpen_empty : IsTubeOpen (∅ : Set X) := by
  simpa only [IsTubeOpen, compl_empty] using (isTubeClosed_univ (X := X))

/-- The whole space is tube open. -/
@[simp] theorem isTubeOpen_univ : IsTubeOpen (univ : Set X) := by
  simpa only [IsTubeOpen, compl_univ] using (isTubeClosed_empty (X := X))

/-- Tube-closed sets are stable under finite set-family unions, including the empty family.
This is the tube-closed union portion of Fujiwara–Kato, Corollary 2.3.8, generalized
from valuative spaces to arbitrary topological spaces. -/
theorem IsTubeClosed.sUnion {F : Set (Set X)} (hF : F.Finite)
    (h : ∀ s ∈ F, IsTubeClosed s) : IsTubeClosed (⋃₀ F) := by
  classical
  revert h
  refine Set.Finite.induction_on F hF ?_ ?_
  · intro _
    simpa only [sUnion_empty] using (isTubeClosed_empty (X := X))
  · intro s F _ _ ih h
    rcases h s (by simp) with ⟨U, hUopen, hUretrocompact, hUclosure⟩
    rcases ih (fun t ht => h t (by simp [ht])) with
      ⟨V, hVopen, hVretrocompact, hVclosure⟩
    refine ⟨U ∪ V, hUopen.union hVopen, hUretrocompact.union hVretrocompact, ?_⟩
    rw [closure_union, hUclosure, hVclosure, sUnion_insert]

/-- Tube-open sets are stable under finite set-family intersections, including the empty
family. This is the complementary dual of `IsTubeClosed.sUnion`, and hence the tube-open
intersection portion of Fujiwara–Kato, Corollary 2.3.8, at arbitrary topological generality. -/
theorem IsTubeOpen.sInter {F : Set (Set X)} (hF : F.Finite)
    (h : ∀ s ∈ F, IsTubeOpen s) : IsTubeOpen (⋂₀ F) := by
  classical
  change IsTubeClosed (⋂₀ F)ᶜ
  have hclosed : IsTubeClosed (⋃₀ (compl '' F)) :=
    IsTubeClosed.sUnion (hF.image compl) (by
      rintro _ ⟨s, hs, rfl⟩
      exact h s hs)
  convert hclosed using 1
  ext x
  simp
