/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.CategoryTheory.Lattice.Extensive

/-!
# Boundary examples for thin-lattice coproducts

Integers supply binary coproduct injection pullbacks without bottom or top.
Natural numbers supply a lattice with bottom and no top, as well as generated
covering sieves. Empty and singleton families are disjoint; two distinct
atoms in a four-element Boolean lattice
give a nontrivial disjoint coproduct, while repeating top at distinct indices
does not. Finite distributivity cannot be removed from universality: in the
five-element diamond, distinct atoms `a`, `b`, `c` have `a ⊓ b = ⊥` and
`a ⊔ b = ⊤`, but `c ⊓ a ⊔ c ⊓ b = ⊥ ≠ c`.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.2(b), for the conditional finite-sum observation.
- SGA 4, Tome I, Exposé II, Definition 4.5, for disjoint coproduct terminology;
  Mathlib, `CategoryTheory.Extensive`, for its formalization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

example :
    pullback (coprod.inl : (2 : ℤ) ⟶ (2 : ℤ) ⨿ 4)
      (coprod.inr : (4 : ℤ) ⟶ (2 : ℤ) ⨿ 4) = 2 := by
  have hp := ((pullback.isLimit
      (coprod.inl : (2 : ℤ) ⟶ (2 : ℤ) ⨿ 4)
      (coprod.inr : (4 : ℤ) ⟶ (2 : ℤ) ⨿ 4)).conePointUniqueUpToIso
      (isPullback_inf
        (coprod.inl : (2 : ℤ) ⟶ (2 : ℤ) ⨿ 4)
        (coprod.inr : (4 : ℤ) ⟶ (2 : ℤ) ⨿ 4)).isLimit).to_eq
  exact hp.trans (inf_eq_left.mpr (by omega))

example {ι : Type*} [Finite ι] (X : ι → Nat) :
    IsUniversalColimit (Cofan.mk (∐ X) (Sigma.ι X)) :=
  FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X)

example {ι : Type} [Finite ι] (X : ι → Nat) :
    Sieve.ofArrows X (Sigma.ι X) ∈ extensiveTopology Nat (∐ X) :=
  mem_extensiveTopology_of_coproduct X _ (fun i => Sieve.ofArrows_mk X (Sigma.ι X) i)

example : ¬ ∃ n : Nat, IsTop n := by
  rintro ⟨n, hn⟩
  exact (Nat.not_succ_le_self n) (hn (n + 1))

example : CoproductDisjoint (fun _ : Fin 0 => (0 : Nat)) := by
  apply (coproductDisjoint_iff_pairwise_inf_eq_bot _).2
  intro i
  exact i.elim0

example : CoproductDisjoint (fun _ : Fin 1 => (7 : Nat)) := by
  apply (coproductDisjoint_iff_pairwise_inf_eq_bot _).2
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

example : CoproductDisjoint (fun _ : Fin 2 => (0 : Fin 1)) := by
  apply (coproductDisjoint_iff_pairwise_inf_eq_bot _).2
  intro i j _
  exact Subsingleton.elim _ _

section BooleanAtoms

local instance : CoproductDisjoint (fun i : Fin 2 => ({i} : Set (Fin 2))) := by
  apply (coproductDisjoint_iff_pairwise_inf_eq_bot _).2
  intro i j hij
  simp [hij]

example {Y : Set (Fin 2)}
    (f : Y ⟶ ∐ (fun i : Fin 2 => ({i} : Set (Fin 2)))) :
    CoproductDisjoint (fun i : Fin 2 => Y ⊓ ({i} : Set (Fin 2))) := by
  exact (coproductDisjoint_baseChange _ f).2

end BooleanAtoms

example : ({(0 : Fin 2)} : Set (Fin 2)) ⊔ {1} = ⊤ := by
  apply Set.ext
  exact Fin.forall_fin_two.2 ⟨by simp, by simp⟩

example : ¬ CoproductDisjoint (fun _ : Fin 2 => (⊤ : Bool)) := by
  intro h
  have hmeet := (coproductDisjoint_iff_pairwise_inf_eq_bot _).1 h
    (0 : Fin 2) 1 (by decide)
  simp at hmeet
