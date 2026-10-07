/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.GenericPoint
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Removing selected generic points

For selected points `G` of a space `X`, the strict-specialization boundary
has one *discrete, labelled* copy of each incidence `η ⤳ σ` with `η ∈ G`
and `σ ∉ G`. Its two maps identify each incidence with the corresponding
closed point in an independent generic-point fork and with `σ` in the
complement. The resulting square maps into `X`. Its boundary is discrete even
when the complement has a non-discrete subspace topology; different incidences
may map to the same point of the complement.

The pushout statement additionally assumes that `X` is Alexandrov and that
every selected generic has no other generizations. No finiteness, separation,
nonemptiness or injectivity hypothesis is part of the square.

## References

- Mathlib contributors, `Topology.AlexandrovDiscrete`,
  `Topology.Category.TopCat.Basic` and `CategoryTheory.IsPushout`.
- Formal Frontier Agents, `ValuationIntegers.FiniteIntersections.Spectrum`,
  for the independent generic-point fork used in each summand.
- Stefan Schröer, *A simple proof for Hochster's Theorem*, §2, motivates
  finite-space generic-point removal. Y. Ershov's antecedent is credited
  indirectly through Schröer; no original text of Ershov is used here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set

namespace Topology.GenericPointRemoval

variable {X : Type u} [TopologicalSpace X]

/-- The complement of the selected generic points, with its induced topology. -/
abbrev Rest (G : Set X) := {x : X // x ∉ G}

/-- A strict specialization of `η`: a point outside the selected set to
which `η` specializes. -/
abbrev Strict (G : Set X) (η : G) := {σ : Rest G // η.1 ⤳ σ.1}

/-- The labelled incidence boundary, equipped with a discrete topology in
the pushout diagram. -/
abbrev Boundary (G : Set X) := Σ η : G, Strict G η

/-- The topological sum of independent generic-point forks. -/
abbrev Forks (G : Set X) := Σ η : G, WithGenericPoint (Strict G η)

/-- Include each discrete boundary incidence as its fork's closed point. -/
def boundaryFork (G : Set X) :
    TopCat.discrete.obj (Boundary G) ⟶ TopCat.of (Forks G) :=
  TopCat.ofHom (X := TopCat.discrete.obj (Boundary G))
    ⟨fun p => ⟨p.1, .closed p.2⟩, continuous_of_discreteTopology⟩

/-- Forget the generic-point label of a boundary incidence. This map
need not be injective. -/
def boundaryRest (G : Set X) :
    TopCat.discrete.obj (Boundary G) ⟶ TopCat.of (Rest G) :=
  TopCat.ofHom (X := TopCat.discrete.obj (Boundary G))
    ⟨fun p => p.2.1, continuous_of_discreteTopology⟩

/-- Each independent fork maps its generic point and indexed closed points
to their corresponding points of `X`. This map is continuous for any ambient
topology, without an Alexandrov assumption. -/
def forkTotal (G : Set X) : TopCat.of (Forks G) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨(fun p => match p with
      | ⟨η, .generic⟩ => η.1
      | ⟨_, .closed σ⟩ => σ.1.1), by
    apply continuous_sigma
    intro η
    apply WithGenericPoint.continuous_of_specializes
    intro σ
    exact σ.2⟩

/-- Include the complement with its induced subspace topology. -/
def restTotal (G : Set X) : TopCat.of (Rest G) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

variable (G : Set X)

@[simp]
theorem boundaryFork_apply (η : G) (σ : Strict G η) :
    boundaryFork G ⟨η, σ⟩ = ⟨η, .closed σ⟩ := rfl

@[simp]
theorem boundaryRest_apply (η : G) (σ : Strict G η) :
    boundaryRest G ⟨η, σ⟩ = σ.1 := rfl

@[simp]
theorem forkTotal_generic (η : G) :
    forkTotal G ⟨η, .generic⟩ = η.1 := rfl

@[simp]
theorem forkTotal_closed (η : G) (σ : Strict G η) :
    forkTotal G ⟨η, .closed σ⟩ = σ.1.1 := rfl

@[simp]
theorem restTotal_apply (σ : Rest G) : restTotal G σ = σ.1 := rfl

/-- The four maps commute on every labelled incidence. -/
theorem commutes : boundaryFork G ≫ forkTotal G = boundaryRest G ≫ restTotal G := by
  ext p
  rcases p with ⟨η, σ⟩
  rfl

/-- The two maps into `X` jointly cover every point, even when `G` is empty. -/
theorem exists_forkTotal_or_restTotal (x : X) :
    (∃ p : Forks G, forkTotal G p = x) ∨
      (∃ σ : Rest G, restTotal G σ = x) := by
  by_cases hx : x ∈ G
  · left
    exact ⟨⟨⟨x, hx⟩, .generic⟩, rfl⟩
  · right
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Define the underlying gluing function by its values on the selected
generic points and on their complement. -/
noncomputable def extend {W : Type v} (h : Forks G → W) (q : Rest G → W) : X → W := by
  classical
  exact fun x => if hx : x ∈ G then h ⟨⟨x, hx⟩, .generic⟩ else q ⟨x, hx⟩

@[simp]
theorem extend_generic {W : Type v} (h : Forks G → W) (q : Rest G → W)
    (η : G) : extend G h q η.1 = h ⟨η, .generic⟩ := by
  simp [extend, η.2]

@[simp]
theorem extend_rest {W : Type v} (h : Forks G → W) (q : Rest G → W)
    (σ : Rest G) : extend G h q σ.1 = q σ := by
  simp [extend, σ.2]

/-- If the maps agree on each labelled boundary point, the gluing function
restricts to the given map on every fork. -/
theorem extend_fork {W : Type v} (h : Forks G → W) (q : Rest G → W)
    (hcompat : ∀ (η : G) (σ : Strict G η), h ⟨η, .closed σ⟩ = q σ.1)
    (p : Forks G) : extend G h q (forkTotal G p) = h p := by
  rcases p with ⟨η, p⟩
  cases p with
  | generic => exact extend_generic G h q η
  | closed σ =>
    rw [forkTotal_closed, extend_rest]
    exact (hcompat η σ).symm

/-- The selected points have no distinct generizations. This strong form
also rules out indistinguishable generizations in non-`T₀` spaces. -/
def HasOnlyGenerizations (G : Set X) : Prop :=
  ∀ η : G, ∀ x : X, x ⤳ η.1 → x = η.1

variable [AlexandrovDiscrete X]

/-- Open sets are detected on the complement and on all independent forks.
The implication uses the Alexandrov property and the chosen generic-point
condition; the converse follows already from continuity of the four maps. -/
theorem isOpen_iff (hG : HasOnlyGenerizations G) (U : Set X) :
    IsOpen U ↔ IsOpen (restTotal G ⁻¹' U) ∧ IsOpen (forkTotal G ⁻¹' U) := by
  constructor
  · intro hU
    exact ⟨hU.preimage (restTotal G).hom.continuous,
      hU.preimage (forkTotal G).hom.continuous⟩
  · rintro ⟨hrest, hfork⟩
    apply isOpen_iff_forall_specializes.mpr
    intro x y hxy hyU
    by_cases hyG : y ∈ G
    · rw [hG ⟨y, hyG⟩ x hxy]
      exact hyU
    by_cases hxG : x ∈ G
    · let η : G := ⟨x, hxG⟩
      let σ : Strict G η := ⟨⟨y, hyG⟩, hxy⟩
      have hopen : IsOpen ((fun p : WithGenericPoint (Strict G η) =>
          (forkTotal G) ⟨η, p⟩) ⁻¹' U) := (isOpen_sigma_iff.mp hfork) η
      have hclosed : WithGenericPoint.closed σ ∈
          (fun p : WithGenericPoint (Strict G η) => (forkTotal G) ⟨η, p⟩) ⁻¹' U :=
        hyU
      have hgeneric := (specializes_iff_forall_open.mp
        (WithGenericPoint.generic_specializes σ)) _ hopen hclosed
      exact hgeneric
    · have hspec : (⟨x, hxG⟩ : Rest G) ⤳ (⟨y, hyG⟩ : Rest G) :=
        (subtype_specializes_iff _ _).mpr hxy
      have hmem : (⟨y, hyG⟩ : Rest G) ∈ restTotal G ⁻¹' U := hyU
      exact (specializes_iff_forall_open.mp hspec) _ hrest hmem

/-- Equivalently, openness on the complement and the implications along
each labelled strict-specialization incidence detect openness on `X`. -/
theorem isOpen_iff_rest_and_specializes (hG : HasOnlyGenerizations G) (U : Set X) :
    IsOpen U ↔ IsOpen (restTotal G ⁻¹' U) ∧
      ∀ (η : G) (σ : Strict G η), σ.1.1 ∈ U → η.1 ∈ U := by
  constructor
  · intro hU
    refine ⟨(isOpen_iff G hG U).mp hU |>.1, ?_⟩
    intro η σ hσ
    exact (specializes_iff_forall_open.mp σ.2) U hU hσ
  · rintro ⟨hrest, hinc⟩
    apply (isOpen_iff G hG U).mpr
    refine ⟨hrest, isOpen_sigma_iff.mpr ?_⟩
    intro η
    apply (WithGenericPoint.isOpen_iff _).mpr
    by_cases hη : η.1 ∈ U
    · exact Or.inr hη
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      cases p with
      | generic => exact hη hp
      | closed σ => exact hη (hinc η σ hp)

/-- The same criterion detects continuity into a target in an arbitrary
universe, with no separation assumption on the target. -/
theorem continuous_iff (hG : HasOnlyGenerizations G)
    {W : Type v} [TopologicalSpace W] (f : X → W) :
    Continuous f ↔ Continuous (f ∘ forkTotal G) ∧
      Continuous (f ∘ restTotal G) := by
  constructor
  · intro hf
    exact ⟨hf.comp (forkTotal G).hom.continuous,
      hf.comp (restTotal G).hom.continuous⟩
  · rintro ⟨hfork, hrest⟩
    apply continuous_def.mpr
    intro U hU
    apply (isOpen_iff G hG (f ⁻¹' U)).mpr
    constructor
    · exact hU.preimage hrest
    · exact hU.preimage hfork

/-- The explicit gluing function is continuous when both inputs are
continuous and agree on each labelled boundary point. This uses the
open-preimage/continuity criterion above. -/
theorem continuous_extend (hG : HasOnlyGenerizations G)
    {W : Type v} [TopologicalSpace W] (h : Forks G → W) (q : Rest G → W)
    (hh : Continuous h) (hq : Continuous q)
    (hcompat : ∀ (η : G) (σ : Strict G η), h ⟨η, .closed σ⟩ = q σ.1) :
    Continuous (extend G h q) := by
  apply (continuous_iff G hG _).mpr
  constructor
  · have heq : extend G h q ∘ forkTotal G = h :=
      funext (extend_fork G h q hcompat)
    rw [heq]
    exact hh
  · have heq : extend G h q ∘ restTotal G = q :=
      funext (extend_rest G h q)
    rw [heq]
    exact hq

/-- This square is a pushout in `TopCat`, not merely a commuting square of
underlying sets. In particular `boundaryRest` may identify incidences. -/
theorem isPushout (hG : HasOnlyGenerizations G) :
    CategoryTheory.IsPushout (boundaryFork G) (boundaryRest G)
      (forkTotal G) (restTotal G) := by
  have compatible (s : PushoutCocone (boundaryFork G) (boundaryRest G)) :
      ∀ (η : G) (σ : Strict G η), s.inl ⟨η, .closed σ⟩ = s.inr σ.1 := by
    intro η σ
    have h := congrArg
      (fun k : TopCat.discrete.obj (Boundary G) ⟶ s.pt => k ⟨η, σ⟩) s.condition
    change s.inl ⟨η, .closed σ⟩ = s.inr σ.1 at h
    exact h
  let lift (s : PushoutCocone (boundaryFork G) (boundaryRest G)) :
      TopCat.of X ⟶ s.pt :=
    TopCat.ofHom ⟨extend G s.inl s.inr,
      continuous_extend G hG s.inl s.inr s.inl.hom.continuous
        s.inr.hom.continuous (compatible s)⟩
  apply CategoryTheory.IsPushout.of_isColimit' ⟨commutes G⟩
  refine PushoutCocone.IsColimit.mk (commutes G) lift ?_ ?_ ?_
  · intro s
    ext p
    exact extend_fork G s.inl s.inr (compatible s) p
  · intro s
    ext σ
    exact extend_rest G s.inl s.inr σ
  · intro s m hfork hrest
    ext x
    rcases exists_forkTotal_or_restTotal G x with ⟨p, rfl⟩ | ⟨σ, rfl⟩
    · calc
        m (forkTotal G p) = s.inl p :=
          congrArg (fun k : TopCat.of (Forks G) ⟶ s.pt => k p) hfork
        _ = lift s (forkTotal G p) := (extend_fork G s.inl s.inr (compatible s) p).symm
    · calc
        m (restTotal G σ) = s.inr σ :=
          congrArg (fun k : TopCat.of (Rest G) ⟶ s.pt => k σ) hrest
        _ = lift s (restTotal G σ) := (extend_rest G s.inl s.inr σ).symm

/-- The morphism induced by compatible maps out of the forks and complement.
The categorical universal property is supplied by `IsPushout.desc`. -/
noncomputable def desc (hG : HasOnlyGenerizations G) {W : TopCat.{u}}
    (h : TopCat.of (Forks G) ⟶ W) (q : TopCat.of (Rest G) ⟶ W)
    (hcompat : boundaryFork G ≫ h = boundaryRest G ≫ q) : TopCat.of X ⟶ W :=
  (isPushout G hG).desc h q hcompat

@[simp]
theorem forkTotal_desc (hG : HasOnlyGenerizations G) {W : TopCat.{u}}
    (h : TopCat.of (Forks G) ⟶ W) (q : TopCat.of (Rest G) ⟶ W)
    (hcompat : boundaryFork G ≫ h = boundaryRest G ≫ q) :
    forkTotal G ≫ desc G hG h q hcompat = h :=
  (isPushout G hG).inl_desc h q hcompat

@[simp]
theorem restTotal_desc (hG : HasOnlyGenerizations G) {W : TopCat.{u}}
    (h : TopCat.of (Forks G) ⟶ W) (q : TopCat.of (Rest G) ⟶ W)
    (hcompat : boundaryFork G ≫ h = boundaryRest G ≫ q) :
    restTotal G ≫ desc G hG h q hcompat = q :=
  (isPushout G hG).inr_desc h q hcompat

/-- Two continuous extensions agreeing on the forks and complement agree
everywhere; this is the `IsPushout.hom_ext` eliminator. -/
theorem hom_ext (hG : HasOnlyGenerizations G) {W : TopCat.{u}}
    {f g : TopCat.of X ⟶ W}
    (hf : forkTotal G ≫ f = forkTotal G ≫ g)
    (hq : restTotal G ≫ f = restTotal G ≫ g) : f = g :=
  (isPushout G hG).hom_ext hf hq

end Topology.GenericPointRemoval
