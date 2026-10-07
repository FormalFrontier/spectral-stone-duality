/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Topology.Homeomorph.Defs

/-!
# A generic point with independent closed specializations

`Topology.WithGenericPoint ι` adjoins a generic point to a discrete family
of closed points indexed by `ι`. The index type may be empty and need not be
finite. Its internal order has `generic ≤ closed i` and its opens are lower
sets. This internal order is opposite to the order on `Specialization`:
`Specialization.toEquiv_le_toEquiv` identifies the latter with the convention
that specializations lie *below* their generizations.
An equivalence of index types relabels the independent closed points while
fixing the generic point.

## References

- Mathlib contributors, `Topology.AlexandrovDiscrete` and
  `Topology.Order.UpperLowerSetTopology`, for specialization and lower-set topology.
- Formal Frontier Agents, `ValuationIntegers.FiniteIntersections.Spectrum`, for the
  independently defined generic-point fork and its four point/topology laws.
- Stefan Schröer, *A simple proof for Hochster's Theorem*, §2, for the
  finite-space valuation strategy; antecedent credit to Y. Ershov is indirect
  through Schröer, not a claim to consultation of Ershov's original text.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace Topology

/-- A generic point and an arbitrary family of independent closed points. -/
inductive WithGenericPoint (ι : Type v) : Type v
  | generic : WithGenericPoint ι
  | closed (i : ι) : WithGenericPoint ι

namespace WithGenericPoint

variable {ι : Type v}

instance : PartialOrder (WithGenericPoint ι) where
  le x y := x = .generic ∨ x = y
  le_refl _ := Or.inr rfl
  le_trans _ _ _ hxy hyz := by
    rcases hxy with rfl | rfl
    · exact Or.inl rfl
    · exact hyz
  le_antisymm _ _ hxy hyx := by
    rcases hxy with h | h
    · rcases hyx with h' | h'
      · exact h.trans h'.symm
      · exact h'.symm
    · exact h

/-- The fork has the lower-set topology: an open containing a closed point
must also contain the generic point. -/
instance : TopologicalSpace (WithGenericPoint ι) := Topology.lowerSet _

/-- The only nonempty opens of the fork contain its generic point. -/
theorem isOpen_iff (s : Set (WithGenericPoint ι)) :
    IsOpen s ↔ s = ∅ ∨ WithGenericPoint.generic ∈ s := by
  change IsLowerSet s ↔ _
  constructor
  · intro hs
    by_cases h : s = ∅
    · exact Or.inl h
    · right
      obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
      exact hs (Or.inl rfl) hx
  · rintro (rfl | h) x y hxy hy
    · exact hy
    · rcases hxy with heq | heq
      · simpa [heq] using h
      · simpa [heq] using hy

/-- The generic point specializes to any indexed closed point. -/
theorem generic_specializes (i : ι) :
    (WithGenericPoint.generic : WithGenericPoint ι) ⤳ WithGenericPoint.closed i := by
  apply specializes_iff_forall_open.mpr
  intro s hs hclosed
  exact (isOpen_iff s).mp hs |>.elim (fun h => by simp [h] at hclosed) id

/-- Each indexed point is closed in the independent fork topology. -/
theorem closed_isClosed (i : ι) :
    IsClosed ({WithGenericPoint.closed i} : Set (WithGenericPoint ι)) := by
  rw [← isOpen_compl_iff]
  exact (isOpen_iff _).mpr (Or.inr (by simp))

/-- Indexed closed points specialize to one another only if their indices agree. -/
theorem closed_specializes_closed_iff (i j : ι) :
    (WithGenericPoint.closed i : WithGenericPoint ι) ⤳ WithGenericPoint.closed j ↔
      i = j := by
  constructor
  · intro h
    let s : Set (WithGenericPoint ι) := {WithGenericPoint.generic, WithGenericPoint.closed j}
    have hopen : IsOpen s := (isOpen_iff s).mpr (Or.inr (by simp [s]))
    have hmem := (specializes_iff_forall_open.mp h) s hopen (by simp [s])
    simpa [s] using hmem
  · rintro rfl
    exact specializes_refl _

@[simp]
theorem generic_le (x : WithGenericPoint ι) : WithGenericPoint.generic ≤ x := Or.inl rfl

@[simp]
theorem closed_le_closed_iff (i j : ι) :
    WithGenericPoint.closed i ≤ WithGenericPoint.closed j ↔ i = j := by
  change (WithGenericPoint.closed i = WithGenericPoint.generic ∨
    WithGenericPoint.closed i = WithGenericPoint.closed j) ↔ _
  simp

/-- A map out of a fork is continuous if the image of its generic point
specializes to the image of every indexed point. -/
theorem continuous_of_specializes {Y : Type w} [TopologicalSpace Y]
    (f : WithGenericPoint ι → Y)
    (hf : ∀ i, f .generic ⤳ f (.closed i)) : Continuous f := by
  apply continuous_def.mpr
  intro s hs
  apply (isOpen_iff _).mpr
  by_cases h : f ⁻¹' s = ∅
  · exact Or.inl h
  · right
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
    cases x with
    | generic => exact hx
    | closed i => exact (specializes_iff_forall_open.mp (hf i)) s hs hx

/-- Relabel the closed points of an independent generic-point fork by an
equivalence; the generic point stays fixed. -/
def reindex {κ : Type u} (e : ι ≃ κ) : WithGenericPoint ι ≃ₜ WithGenericPoint κ where
  toEquiv := {
    toFun := fun x => match x with
      | .generic => .generic
      | .closed i => .closed (e i)
    invFun := fun x => match x with
      | .generic => .generic
      | .closed j => .closed (e.symm j)
    left_inv := by
      intro x
      cases x with
      | generic => rfl
      | closed i => simp
    right_inv := by
      intro x
      cases x with
      | generic => rfl
      | closed j => simp
  }
  continuous_toFun := by
    apply continuous_of_specializes
    intro i
    exact generic_specializes (e i)
  continuous_invFun := by
    apply continuous_of_specializes
    intro j
    exact generic_specializes (e.symm j)

@[simp]
theorem reindex_apply_generic {κ : Type u} (e : ι ≃ κ) :
    reindex e .generic = .generic := rfl

@[simp]
theorem reindex_apply_closed {κ : Type u} (e : ι ≃ κ) (i : ι) :
    reindex e (.closed i) = .closed (e i) := rfl

@[simp]
theorem reindex_symm_apply_generic {κ : Type u} (e : ι ≃ κ) :
    (reindex e).symm .generic = .generic := rfl

@[simp]
theorem reindex_symm_apply_closed {κ : Type u} (e : ι ≃ κ) (j : κ) :
    (reindex e).symm (.closed j) = .closed (e.symm j) := rfl

/-- Reindexing by the identity equivalence is the identity homeomorphism. -/
@[simp]
theorem reindex_refl :
    reindex (Equiv.refl ι) = Homeomorph.refl (WithGenericPoint ι) := by
  ext x
  cases x <;> rfl

/-- Successive relabellings agree with relabelling by the composite equivalence. -/
@[simp]
theorem reindex_trans {κ : Type u} {τ : Type w} (e : ι ≃ κ) (f : κ ≃ τ) :
    reindex (e.trans f) = (reindex e).trans (reindex f) := by
  ext x
  cases x <;> rfl

/-- Inverse relabelling agrees with the inverse homeomorphism. -/
@[simp]
theorem reindex_symm {κ : Type u} (e : ι ≃ κ) :
    reindex e.symm = (reindex e).symm := by
  ext x
  cases x <;> rfl

end WithGenericPoint

end Topology
