/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveTopology

/-!
# Universal finite coproducts in thin distributive lattices

Finite joins in a distributive lattice with bottom are universal coproducts in its
order category. A particular finite coproduct is disjoint exactly when distinct
summands have meet bottom; the distinction matters even for Boolean lattices.

The pullback of two order arrows is their meet without requiring a top element;
binary coproduct injections have pullbacks without requiring bottom or top.
The chosen-pullback equality in `Mathlib.CategoryTheory.Limits.Lattice` assumes
top because it obtains pullbacks from all finite limits. Here the pullback
square itself is stated under only `SemilatticeInf`.

The site consumer concerns the extensive topology on the thin category of
elements, not a topology on the category of lattice objects. Nothing here
asserts that all finite coproducts are disjoint or van Kampen.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §1.2(e) and §2.2(b), for order-category conventions and the
  conditional universality of disjoint finite sums. The present results also
  cover arbitrary finite joins and lattices without top.
- M. Artin, A. Grothendieck and J.-L. Verdier (eds.), *Théorie des topos et
  cohomologie étale des schémas* (SGA 4), Tome I, Exposé II, Definition 4.5,
  for the terminology of universally disjoint sums, not for the proofs here.
- Mathlib, `CategoryTheory.Extensive`, `CategoryTheory.Limits.Lattice` and
  `CategoryTheory.Sites.Coherent.ExtensiveTopology`, for the categorical
  pullback, disjointness and covering-sieve interfaces.
-/

@[expose] public section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory

/-- Meets give pullbacks of order arrows in a meet-semilattice, even without top. -/
theorem isPullback_inf {A : Type u} [SemilatticeInf A] {x y z : A}
    (f : x ⟶ z) (g : y ⟶ z) :
    IsPullback (homOfLE inf_le_left) (homOfLE inf_le_right) f g := by
  exact (isPullback_iff_isLimit_binaryFan_of_isThin).2 ⟨Preorder.isLimitBinaryFan x y⟩

/-- With a top element, the meet pullback square agrees with Mathlib's chosen pullback. -/
theorem pullback_eq_inf_of_isPullback {A : Type u} [SemilatticeInf A] [OrderTop A]
    {x y z : A} (f : x ⟶ z) (g : y ⟶ z) : pullback f g = x ⊓ y := by
  exact ((pullback.isLimit f g).conePointUniqueUpToIso (isPullback_inf f g).isLimit).to_eq

/-- Meets give pullbacks of binary coproduct injections in an order category without
bottom or top. -/
instance hasPullbacksOfInclusions_of_lattice (A : Type u) [Lattice A] :
    HasPullbacksOfInclusions A where
  hasPullbackInl f := (isPullback_inf coprod.inl f).hasPullback

/-- Finite coproducts in the order category of a distributive lattice with bottom
are universal; no top element or nontriviality assumption is needed. This
extends the conditional disjoint-sum assertion in Fujiwara--Kato,
*Foundations of Rigid Geometry I*, §2.2(b). -/
instance finitaryPreExtensive_of_distribLattice (A : Type u) [DistribLattice A]
    [OrderBot A] : FinitaryPreExtensive A := by
  refine ⟨?_⟩
  intro X Y c hc F' c' α f _ _ h
  have hc_le : c.pt ≤ X ⊔ Y :=
    (hc.desc (BinaryCofan.mk (homOfLE le_sup_left) (homOfLE le_sup_right))).le
  have hleft : c'.pt ⊓ X ≤ F'.obj ⟨WalkingPair.left⟩ :=
    ((h ⟨WalkingPair.left⟩).lift (homOfLE inf_le_left)
      (homOfLE inf_le_right) (by subsingleton)).le
  have hright : c'.pt ⊓ Y ≤ F'.obj ⟨WalkingPair.right⟩ :=
    ((h ⟨WalkingPair.right⟩).lift (homOfLE inf_le_left)
      (homOfLE inf_le_right) (by subsingleton)).le
  have hc'_le : c'.pt ≤ F'.obj ⟨WalkingPair.left⟩ ⊔
      F'.obj ⟨WalkingPair.right⟩ := by
    calc
      c'.pt ≤ c'.pt ⊓ (X ⊔ Y) := le_inf le_rfl (f.le.trans hc_le)
      _ = (c'.pt ⊓ X) ⊔ (c'.pt ⊓ Y) := inf_sup_left _ _ _
      _ ≤ F'.obj ⟨WalkingPair.left⟩ ⊔ F'.obj ⟨WalkingPair.right⟩ :=
        sup_le_sup hleft hright
  exact ⟨Preorder.isColimitOfIsLUB F' c' ⟨Preorder.coconePt_mem_upperBounds _ c', fun t ht =>
    hc'_le.trans (sup_le (ht ⟨_, rfl⟩) (ht ⟨_, rfl⟩))⟩⟩

namespace Limits

/-- A finite indexed coproduct in a lattice with bottom is disjoint exactly when
different indices have summands whose meet is bottom. Repeated values are allowed. -/
theorem coproductDisjoint_iff_pairwise_inf_eq_bot {A : Type u} [Lattice A] [OrderBot A]
    {ι : Type v} [Finite ι] (X : ι → A) :
    CoproductDisjoint X ↔ ∀ i j : ι, i ≠ j → X i ⊓ X j = ⊥ := by
  constructor
  · intro h i j hij
    have : CoproductDisjoint X := h
    have hinitial : IsInitial (X i ⊓ X j) :=
      IsInitial.ofCoproductDisjointOfIsColimitOfIsLimit hij
        (coproductIsCoproduct X) (isPullback_inf (Sigma.ι X i) (Sigma.ι X j)).isLimit
    exact le_antisymm (hinitial.to ⊥).le bot_le
  · intro h
    refine { nonempty_isInitial_of_ne := ?_, mono_inj := ?_ }
    · intro c hc i j hij s hs
      have hpoint : s.pt = X i ⊓ X j :=
        (hs.conePointUniqueUpToIso (isPullback_inf (c.inj i) (c.inj j)).isLimit).to_eq
      rw [hpoint, h i j hij]
      exact ⟨Preorder.isInitialBot A⟩
    · intro c hc i
      exact ⟨fun _ _ _ => Subsingleton.elim _ _⟩

attribute [local instance] Fintype.ofFinite in
/-- Generalizing the conditional finite-sum observation in Fujiwara--Kato,
*Foundations of Rigid Geometry I*, §2.2(b), a disjoint finite coproduct remains
a disjoint coproduct after base change
along an order arrow. The pulled-back summands are the meets with its domain. -/
theorem coproductDisjoint_baseChange {A : Type u} [DistribLattice A] [OrderBot A]
    {ι : Type v} [Finite ι] (X : ι → A) [CoproductDisjoint X]
    {Y : A} (f : Y ⟶ ∐ X) :
    Nonempty (IsColimit (Cofan.mk Y (fun i => homOfLE (inf_le_left : Y ⊓ X i ≤ Y)))) ∧
      CoproductDisjoint (fun i => Y ⊓ X i) := by
  have hcoprod : ∐ X = Finset.univ.sup X := by
    apply le_antisymm
    · exact ((coproductIsCoproduct X).desc
        (Cofan.mk (Finset.univ.sup X)
          (fun i => homOfLE (Finset.le_sup (Finset.mem_univ i))))).le
    · apply Finset.sup_le
      intro i hi
      exact (Sigma.ι X i).le
  have hjoin : Y = Finset.univ.sup (fun i => Y ⊓ X i) := by
    calc
      Y = Y ⊓ ∐ X := (inf_eq_left.mpr f.le).symm
      _ = Y ⊓ Finset.univ.sup X := by rw [hcoprod]
      _ = Finset.univ.sup (fun i => Y ⊓ X i) := Finset.sup_inf_distrib_left _ _ _
  constructor
  · refine ⟨Preorder.isColimitOfIsLUB (Discrete.functor (fun i => Y ⊓ X i)) _
      ⟨Preorder.coconePt_mem_upperBounds _ _, ?_⟩⟩
    intro z hz
    rw [hjoin]
    apply Finset.sup_le
    intro i hi
    exact hz ⟨⟨i⟩, rfl⟩
  · apply (coproductDisjoint_iff_pairwise_inf_eq_bot _).2
    intro i j hij
    apply eq_bot_iff.mpr
    calc
      (Y ⊓ X i) ⊓ (Y ⊓ X j) ≤ X i ⊓ X j :=
        le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
      _ = ⊥ := (coproductDisjoint_iff_pairwise_inf_eq_bot X).1 inferInstance i j hij

end Limits

/-- The coproduct injections of a finite family generate a covering sieve for
the extensive topology of the underlying order category. -/
theorem mem_extensiveTopology_of_coproduct {A : Type u} [DistribLattice A]
    [OrderBot A] {ι : Type} [Finite ι] (X : ι → A) (S : Sieve (∐ X))
    (hS : ∀ i, S.arrows (Sigma.ι X i)) : S ∈ (extensiveTopology A) (∐ X) := by
  exact (extensiveTopology.mem_sieves_iff_contains_colimit_cofan S).2
    ⟨ι, inferInstance, X, Sigma.ι X, ⟨coproductIsCoproduct X⟩, hS⟩

end CategoryTheory
