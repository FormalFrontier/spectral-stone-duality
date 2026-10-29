/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.T1Quotient
public import Mathlib.Topology.WithTopology
public import Mathlib.Topology.Specialization
public import Mathlib.Order.Max

/-!
# Maximal generizations and the T₁ quotient

Suppose every point of a topological space has a unique maximal generization,
where uniqueness means equality of points, not merely inseparability.
`maximalGenerization h x` selects that point. The hypothesis `h` is an ordinary
explicit argument; no separation, chain, coherence or nonemptiness hypothesis is
imposed on the space. Maximality is expressed by the stock order predicate
`IsMax (Specialization.toEquiv a)` on original points.
`Specialization.isMax_toEquiv_iff` characterizes it using specialization.

`MaximalGenerizationSpace X h` is the set of maximal points with the final
topology of this selection, distinguished from its subspace topology by
Mathlib's `WithTopology` tag. Its constructor `MaximalGenerizationSpace.ofMaximal`
and eliminator `MaximalGenerizationSpace.repr` identify its points with maximal
points of `X`. The eliminator is not asserted to be continuous.

The projection `MaximalGenerizationSpace.unit` is a quotient map with closed
fibres equal to singleton closures in `X`, and its target is T₁.
`MaximalGenerizationSpace.t1QuotientHomeomorph` identifies this presentation
with `T1Quotient X`, preserving the unit. `MaximalGenerizationSpace.lift`
factors maps to every T₁ target, in an independent universe. The induced map
`MaximalGenerizationSpace.map` sends a maximal point `a` to the maximal
generization of `f a`; it is not a restriction of `f` to maximal points.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, Definition 2.3.1 and §2.3(c), motivate the maximal-point
  presentation. Here the explicit unique-maximal-generization hypothesis
  replaces their valuative-space assumptions; no source-valuative structure is
  defined.
- Mathlib supplies the topology tag, coinduced topology, continuous maps and
  quotient-map descent. The comparison reuses the T₁ quotient and its universal
  lift from `SpectralStoneDuality.Topology.T1Quotient`.
-/

@[expose] public section

noncomputable section

universe u v w

open Set Topology

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace Specialization

/-- Maximality in the specialization order means that every generization specializes back.
No separation hypothesis is required. -/
theorem isMax_toEquiv_iff (a : X) :
    IsMax (toEquiv a) ↔ ∀ z : X, z ⤳ a → a ⤳ z := by
  rw [isMax_iff_forall_not_lt]
  constructor
  · intro ha z hz
    by_contra haz
    apply ha (toEquiv z)
    exact lt_iff_le_not_ge.mpr
      ⟨toEquiv_le_toEquiv.mpr hz, fun h => haz (toEquiv_le_toEquiv.mp h)⟩
  · intro ha b hab
    have hz : ofEquiv b ⤳ a := toEquiv_le_toEquiv.mp (by
      simpa only [toEquiv_ofEquiv] using (lt_iff_le_not_ge.mp hab).1)
    have hback : toEquiv (ofEquiv b) ≤ toEquiv a :=
      toEquiv_le_toEquiv.mpr (ha _ hz)
    exact (lt_iff_le_not_ge.mp hab).2 (by
      simpa only [toEquiv_ofEquiv] using hback)

end Specialization

/-- In a T₀ space with comparable generizations, existence of maximal generizations
implies their uniqueness as points. -/
theorem existsUnique_maximalGenerization_of_t0 [T0Space X]
    (hchain : ∀ x a b : X, a ⤳ x → b ⤳ x → a ⤳ b ∨ b ⤳ a)
    (hexists : ∀ x : X, ∃ a : X, a ⤳ x ∧ IsMax (Specialization.toEquiv a)) :
    ∀ x : X, ∃! a : X, a ⤳ x ∧ IsMax (Specialization.toEquiv a) := by
  intro x
  obtain ⟨a, hax, ha⟩ := hexists x
  refine ⟨a, ⟨hax, ha⟩, ?_⟩
  intro b hb
  have hab : a ⤳ b ∧ b ⤳ a := by
    rcases hchain x a b hax hb.1 with hab | hba
    · exact ⟨hab, (Specialization.isMax_toEquiv_iff b).mp hb.2 a hab⟩
    · exact ⟨(Specialization.isMax_toEquiv_iff a).mp ha b hba, hba⟩
  exact Specialization.toEquiv_inj.mp (le_antisymm
    (Specialization.toEquiv_le_toEquiv.mpr hab.1)
    (Specialization.toEquiv_le_toEquiv.mpr hab.2))

/-- Every point of a T₁ space is its unique maximal generization. -/
theorem existsUnique_maximalGenerization_of_t1 [T1Space X] :
    ∀ x : X, ∃! a : X, a ⤳ x ∧ IsMax (Specialization.toEquiv a) := by
  intro x
  refine ⟨x, ⟨specializes_refl x, (Specialization.isMax_toEquiv_iff x).mpr ?_⟩, ?_⟩
  · intro z hz
    rcases hz.eq with rfl
    exact specializes_refl z
  · intro a ha
    exact ha.1.eq

/-- The unique maximal generization of a point, chosen using equality of points. -/
def maximalGenerization
    (h : ∀ x : X, ∃! a, a ⤳ x ∧ IsMax (Specialization.toEquiv a)) (x : X) : X :=
  Classical.choose (h x)

variable (hX : ∀ x : X, ∃! a, a ⤳ x ∧ IsMax (Specialization.toEquiv a))

/-- The selected point generizes the original point and is maximal. -/
theorem maximalGenerization_spec (x : X) :
    maximalGenerization hX x ⤳ x ∧
      IsMax (Specialization.toEquiv (maximalGenerization hX x)) := by
  exact (Classical.choose_spec (hX x)).1

/-- A point is fixed by maximal-generization selection exactly when it is maximal. -/
theorem maximalGenerization_eq_self_iff (a : X) :
    maximalGenerization hX a = a ↔ IsMax (Specialization.toEquiv a) := by
  constructor
  · intro h
    rw [← h]
    exact (maximalGenerization_spec hX a).2
  · intro ha
    exact ((Classical.choose_spec (hX a)).2 a ⟨specializes_refl a, ha⟩).symm

/-- Under point uniqueness, a maximal point has no distinct generization. -/
theorem isMax_specialization_iff_specializes_eq
    (h : ∀ x : X, ∃! a, a ⤳ x ∧ IsMax (Specialization.toEquiv a)) (a : X) :
    IsMax (Specialization.toEquiv a) ↔ ∀ z, z ⤳ a → z = a := by
  constructor
  · intro ha z hza
    have hz : IsMax (Specialization.toEquiv z) :=
      (Specialization.isMax_toEquiv_iff z).mpr fun w hwz =>
        hza.trans ((Specialization.isMax_toEquiv_iff a).mp ha w (hwz.trans hza))
    exact ((Classical.choose_spec (h a)).2 z ⟨hza, hz⟩).trans
      ((Classical.choose_spec (h a)).2 a ⟨specializes_refl a, ha⟩).symm
  · intro ha
    apply (Specialization.isMax_toEquiv_iff a).mpr
    intro z hza
    rw [ha z hza]

/-- Maximal-generization selection is idempotent. -/
@[simp]
theorem maximalGenerization_idem (x : X) :
    maximalGenerization hX (maximalGenerization hX x) = maximalGenerization hX x := by
  exact (maximalGenerization_eq_self_iff hX _).mpr (maximalGenerization_spec hX x).2

/-- A specialization pair has the same maximal generization. -/
theorem maximalGenerization_eq_of_specializes {x y : X} (hxy : x ⤳ y) :
    maximalGenerization hX x = maximalGenerization hX y := by
  exact (Classical.choose_spec (hX y)).2 (maximalGenerization hX x)
    ⟨(maximalGenerization_spec hX x).1.trans hxy, (maximalGenerization_spec hX x).2⟩

/-- The selected maximal generization is greatest among all generizations of the point. -/
theorem maximalGenerization_greatest {x z : X} (hz : z ⤳ x) :
    maximalGenerization hX x ⤳ z := by
  -- Apply unique maximal-generization existence at the intermediate point `z` as well.
  rw [← maximalGenerization_eq_of_specializes hX hz]
  exact (maximalGenerization_spec hX z).1

/-- Selection has value `a` exactly on the specializations of a maximal point `a`. -/
theorem maximalGenerization_eq_iff (x a : X) (ha : IsMax (Specialization.toEquiv a)) :
    maximalGenerization hX x = a ↔ a ⤳ x := by
  constructor
  · intro h
    rw [← h]
    exact (maximalGenerization_spec hX x).1
  · intro hax
    exact ((Classical.choose_spec (hX x)).2 a ⟨hax, ha⟩).symm

/-- Maximal points with the final topology of maximal-generization selection.

The `WithTopology` tag carries the coinduced topology, not the inherited subtype
topology. The hypothesis is an explicit argument of the carrier. -/
abbrev MaximalGenerizationSpace (X : Type u) [tX : TopologicalSpace X]
    (h : ∀ x : X, ∃! a, a ⤳ x ∧ IsMax (Specialization.toEquiv a)) : Type u :=
  WithTopology {a : X // IsMax (Specialization.toEquiv a)}
    (TopologicalSpace.coinduced
      (fun x : X => (⟨maximalGenerization h x, (Classical.choose_spec (h x)).1.2⟩ :
        {a : X // IsMax (Specialization.toEquiv a)})) tX)

namespace MaximalGenerizationSpace

/-- The point of `X` represented by a point of the maximal-generization space.
This set map is not asserted to be continuous. -/
def repr (a : MaximalGenerizationSpace X hX) : X :=
  (WithTopology.ofTopology a).1

/-- Every represented point is maximal in the generization direction. -/
theorem isMax_repr (a : MaximalGenerizationSpace X hX) :
    IsMax (Specialization.toEquiv (repr hX a)) := by
  exact (WithTopology.ofTopology a).2

/-- Regard a maximal point as a point of the final-topology presentation. -/
def ofMaximal (a : X) (ha : IsMax (Specialization.toEquiv a)) : MaximalGenerizationSpace X hX :=
  WithTopology.toTopology _ ⟨a, ha⟩

/-- The constructor represents the given maximal point. -/
@[simp]
theorem repr_ofMaximal (a : X) (ha : IsMax (Specialization.toEquiv a)) :
    repr hX (ofMaximal hX a ha) = a := by
  exact congrArg Subtype.val (WithTopology.ofTopology_toTopology _ ⟨a, ha⟩)

/-- Reconstructing a point from its represented maximal point gives that point. -/
@[simp]
theorem ofMaximal_repr (a : MaximalGenerizationSpace X hX) :
    ofMaximal hX (repr hX a) (isMax_repr hX a) = a := by
  exact WithTopology.toTopology_ofTopology _ a

/-- Points of the maximal-generization space are equal when their representatives are equal. -/
@[ext]
theorem ext {a b : MaximalGenerizationSpace X hX} (hab : repr hX a = repr hX b) :
    a = b := by
  apply (WithTopology.ofTopology_bijective _).injective
  exact Subtype.ext hab

/-- The projection selecting the unique maximal generization, with its final topology. -/
def unit : C(X, MaximalGenerizationSpace X hX) where
  toFun x := WithTopology.toTopology _
    ⟨maximalGenerization hX x, (Classical.choose_spec (hX x)).1.2⟩
  continuous_toFun := by
    apply Topology.IsCoinducing.continuous
    apply Topology.isCoinducing_iff.mpr
    intro s
    exact ((WithTopology.isOpen_iff _).trans isOpen_coinduced).symm

/-- The projection represents the selected maximal generization. -/
@[simp]
theorem repr_unit (x : X) : repr hX (unit hX x) = maximalGenerization hX x := by
  exact repr_ofMaximal hX (maximalGenerization hX x) (maximalGenerization_spec hX x).2

/-- Projection fixes the represented maximal points. -/
@[simp]
theorem unit_repr (a : MaximalGenerizationSpace X hX) : unit hX (repr hX a) = a := by
  apply ext hX
  rw [repr_unit]
  exact (maximalGenerization_eq_self_iff hX _).mpr (isMax_repr hX a)

/-- The projection is a quotient map onto the specified final-topology space. -/
theorem isQuotientMap_unit : IsQuotientMap (unit hX) := by
  apply Topology.isQuotientMap_iff_isClosed.mpr
  refine ⟨fun a => ⟨repr hX a, unit_repr hX a⟩, ?_⟩
  intro s
  exact (WithTopology.isClosed_iff _).trans isClosed_coinduced

/-- A singleton fibre is exactly the closure of its represented maximal point in `X`. -/
theorem preimage_unit_singleton (a : MaximalGenerizationSpace X hX) :
    unit hX ⁻¹' {a} = closure ({repr hX a} : Set X) := by
  ext x
  change unit hX x = a ↔ x ∈ closure ({repr hX a} : Set X)
  calc
    unit hX x = a ↔ repr hX (unit hX x) = repr hX a :=
      ⟨fun h => congrArg (repr hX) h, fun h => ext hX h⟩
    _ ↔ maximalGenerization hX x = repr hX a := by rw [repr_unit]
    _ ↔ repr hX a ⤳ x := maximalGenerization_eq_iff hX x _ (isMax_repr hX a)
    _ ↔ x ∈ closure ({repr hX a} : Set X) := specializes_iff_mem_closure

/-- Unit images agree exactly when their selected maximal generizations agree. -/
theorem unit_eq_unit_iff (x y : X) :
    unit hX x = unit hX y ↔ maximalGenerization hX x = maximalGenerization hX y := by
  constructor
  · intro h
    simpa only [repr_unit] using congrArg (repr hX) h
  · intro h
    apply ext hX
    simpa only [repr_unit] using h

/-- The final-topology space of maximal generizations is T₁.
For the valuative-space formulation, see Fujiwara–Kato, *Foundations of Rigid
Geometry I*, arXiv:1308.4734v5, Chapter 0, Exercise 0.2.10. -/
instance instT1Space : T1Space (MaximalGenerizationSpace X hX) := by
  refine ⟨fun a => ?_⟩
  apply ((Topology.isQuotientMap_iff_isClosed.mp (isQuotientMap_unit hX)).2 {a}).mpr
  rw [preimage_unit_singleton]
  exact isClosed_closure

/-- The unit-preserving homeomorphism from the T₁ quotient to its maximal-point presentation.
Its inverse sends a maximal point to its image under `T1Quotient.unit`. -/
def t1QuotientHomeomorph : T1Quotient X ≃ₜ MaximalGenerizationSpace X hX where
  toEquiv :=
    { toFun := T1Quotient.lift (unit hX)
      invFun := fun a => T1Quotient.unit X (repr hX a)
      left_inv := by
        intro q
        obtain ⟨x, rfl⟩ := T1Quotient.isQuotientMap_unit.surjective q
        exact (congrArg (fun a : MaximalGenerizationSpace X hX =>
          T1Quotient.unit X (repr hX a)) (T1Quotient.lift_unit (unit hX) x)).trans
            ((congrArg (T1Quotient.unit X) (repr_unit hX x)).trans
              (T1Quotient.unit_eq_of_specializes (maximalGenerization_spec hX x).1))
      right_inv := by
        intro a
        exact (T1Quotient.lift_unit (unit hX) (repr hX a)).trans (unit_repr hX a) }
  continuous_toFun := (T1Quotient.lift (unit hX)).continuous
  continuous_invFun := by
    apply (isQuotientMap_unit hX).continuous_iff.mpr
    have hcomp :
        ((fun a : MaximalGenerizationSpace X hX => T1Quotient.unit X (repr hX a)) ∘
          unit hX) = T1Quotient.unit X := by
      funext x
      exact (congrArg (T1Quotient.unit X) (repr_unit hX x)).trans
        (T1Quotient.unit_eq_of_specializes (maximalGenerization_spec hX x).1)
    rw [hcomp]
    exact (T1Quotient.unit X).continuous

/-- The comparison homeomorphism intertwines the two units. -/
@[simp]
theorem t1QuotientHomeomorph_unit (x : X) :
    t1QuotientHomeomorph hX (T1Quotient.unit X x) = unit hX x :=
  T1Quotient.lift_unit (unit hX) x

/-- The inverse comparison takes the T₁ quotient class of the represented maximal point. -/
@[simp]
theorem t1QuotientHomeomorph_symm_apply (a : MaximalGenerizationSpace X hX) :
    (t1QuotientHomeomorph hX).symm a = T1Quotient.unit X (repr hX a) :=
  rfl

/-- The closed-class T₁ relation is equality of the selected maximal generizations. -/
theorem t1Setoid_iff (x y : X) :
    t1Setoid X x y ↔ maximalGenerization hX x = maximalGenerization hX y := by
  calc
    t1Setoid X x y ↔ T1Quotient.unit X x = T1Quotient.unit X y :=
      _root_.t1Setoid_iff.trans (T1Quotient.unit_eq_unit_iff x y).symm
    _ ↔ unit hX x = unit hX y := by
      constructor
      · intro hxy
        simpa only [t1QuotientHomeomorph_unit] using
          congrArg (t1QuotientHomeomorph hX) hxy
      · intro hxy
        apply (t1QuotientHomeomorph hX).injective
        simpa only [t1QuotientHomeomorph_unit] using hxy
    _ ↔ maximalGenerization hX x = maximalGenerization hX y :=
      unit_eq_unit_iff hX x y

/-- The generic T₁ unit identifies exactly points with the same maximal generization. -/
theorem t1Quotient_unit_eq_unit_iff (x y : X) :
    T1Quotient.unit X x = T1Quotient.unit X y ↔
      maximalGenerization hX x = maximalGenerization hX y :=
  (T1Quotient.unit_eq_unit_iff x y).trans
    (_root_.t1Setoid_iff.symm.trans (t1Setoid_iff hX x y))

/-- Factor a continuous map to any T₁ target through the maximal-point presentation.
The formula is evaluation at the represented point; continuity is by quotient descent,
not continuity of `repr`. No inhabitedness assumption on the target is needed. -/
def lift [T1Space Y] (f : C(X, Y)) : C(MaximalGenerizationSpace X hX, Y) where
  toFun a := f (repr hX a)
  continuous_toFun := by
    apply (isQuotientMap_unit hX).continuous_iff.mpr
    have hcomp :
        ((fun a : MaximalGenerizationSpace X hX => f (repr hX a)) ∘ unit hX) = f := by
      funext x
      exact (congrArg f (repr_unit hX x)).trans
        (((maximalGenerization_spec hX x).1.map f.continuous).eq)
    rw [hcomp]
    exact f.continuous

/-- The factored map evaluates the original map at the represented maximal point. -/
theorem lift_apply [T1Space Y] (f : C(X, Y)) (a : MaximalGenerizationSpace X hX) :
    lift hX f a = f (repr hX a) :=
  rfl

/-- Evaluation on a unit image recovers the original map. -/
@[simp]
theorem lift_unit [T1Space Y] (f : C(X, Y)) (x : X) :
    lift hX f (unit hX x) = f x := by
  rw [lift_apply, repr_unit]
  exact ((maximalGenerization_spec hX x).1.map f.continuous).eq

/-- The factorization equation for the continuous lift. -/
@[simp]
theorem lift_comp_unit [T1Space Y] (f : C(X, Y)) : (lift hX f).comp (unit hX) = f :=
  ContinuousMap.ext (lift_unit hX f)

/-- A continuous factor through the unit is uniquely determined by its unit composite. -/
theorem lift_unique [T1Space Y] (f : C(X, Y)) (g : C(MaximalGenerizationSpace X hX, Y))
    (hg : g.comp (unit hX) = f) : g = lift hX f := by
  apply ContinuousMap.ext
  intro a
  obtain ⟨x, rfl⟩ := (isQuotientMap_unit hX).surjective a
  rw [lift_unit]
  exact congrArg (fun k : C(X, Y) => k x) hg

/-- Every supplied continuous map to every T₁ target has a unique continuous factor.
This is the universal property considered in Fujiwara–Kato, *Foundations of
Rigid Geometry I*, arXiv:1308.4734v5, Chapter 0, Proposition 2.3.9, here under
the explicit unique-maximal-generization hypothesis. -/
theorem existsUnique_lift [T1Space Y] (f : C(X, Y)) :
    ∃! g : C(MaximalGenerizationSpace X hX, Y), g.comp (unit hX) = f :=
  ⟨lift hX f, lift_comp_unit hX f, fun g hg => lift_unique hX f g hg⟩

variable (hY : ∀ y : Y, ∃! b, b ⤳ y ∧ IsMax (Specialization.toEquiv b))

/-- The map induced by any continuous map of spaces with unique maximal generizations.
Compare Fujiwara–Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
Chapter 0, Corollary 2.3.10, for the valuative-space formulation. -/
def map (f : C(X, Y)) :
    C(MaximalGenerizationSpace X hX, MaximalGenerizationSpace Y hY) :=
  lift hX ((unit hY).comp f)

/-- An induced map projects the image of the represented maximal point.
The original map need not preserve maximal points. -/
theorem map_apply (f : C(X, Y)) (a : MaximalGenerizationSpace X hX) :
    map hX hY f a = unit hY (f (repr hX a)) :=
  lift_apply hX ((unit hY).comp f) a

/-- The induced map commutes with the units on points. -/
@[simp]
theorem map_unit (f : C(X, Y)) (x : X) :
    map hX hY f (unit hX x) = unit hY (f x) :=
  lift_unit hX ((unit hY).comp f) x

/-- The unit square for the induced continuous map. -/
theorem map_comp_unit (f : C(X, Y)) :
    (map hX hY f).comp (unit hX) = (unit hY).comp f :=
  lift_comp_unit hX ((unit hY).comp f)

/-- The unit square uniquely determines the induced continuous map. -/
theorem map_unique (f : C(X, Y))
    (g : C(MaximalGenerizationSpace X hX, MaximalGenerizationSpace Y hY))
    (hg : g.comp (unit hX) = (unit hY).comp f) : g = map hX hY f :=
  lift_unique hX ((unit hY).comp f) g hg

/-- Passing to maximal generizations preserves the identity map. -/
@[simp]
theorem map_id :
    map hX hX (ContinuousMap.id X) = ContinuousMap.id (MaximalGenerizationSpace X hX) := by
  apply ContinuousMap.ext
  intro a
  obtain ⟨x, rfl⟩ := (isQuotientMap_unit hX).surjective a
  exact map_unit hX hX (ContinuousMap.id X) x

/-- Passing to maximal generizations preserves composition across independent universes. -/
@[simp]
theorem map_comp (hZ : ∀ z : Z, ∃! c, c ⤳ z ∧ IsMax (Specialization.toEquiv c))
    (f : C(X, Y)) (g : C(Y, Z)) :
    map hX hZ (g.comp f) = (map hY hZ g).comp (map hX hY f) := by
  apply ContinuousMap.ext
  intro a
  obtain ⟨x, rfl⟩ := (isQuotientMap_unit hX).surjective a
  calc
    map hX hZ (g.comp f) (unit hX x) = unit hZ (g (f x)) :=
      map_unit hX hZ (g.comp f) x
    _ = map hY hZ g (unit hY (f x)) := (map_unit hY hZ g (f x)).symm
    _ = map hY hZ g (map hX hY f (unit hX x)) :=
      congrArg (map hY hZ g) (map_unit hX hY f x).symm

/-- The comparison with the T₁ quotient is natural for every continuous map. -/
theorem t1QuotientHomeomorph_natural (f : C(X, Y)) (q : T1Quotient X) :
    t1QuotientHomeomorph hY (T1Quotient.map f q) =
      map hX hY f (t1QuotientHomeomorph hX q) := by
  obtain ⟨x, rfl⟩ := T1Quotient.isQuotientMap_unit.surjective q
  simp only [T1Quotient.map_unit, t1QuotientHomeomorph_unit, map_unit]

end MaximalGenerizationSpace
