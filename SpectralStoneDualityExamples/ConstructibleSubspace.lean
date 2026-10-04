/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.ConstructibleSubspace
public import SpectralStoneDuality.Topology.Finite
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Topology.Order

/-!
# Constructibly closed spectral subspaces: examples

Empty and whole subspaces are included. The two-point upper-set topology has a
proper constructibly closed subset that is not stable under generization.
The hypotheses for these examples are established independently of the
constructibly closed subspace results.
An infinite family of compact-open cylinders has a non-open intersection.

## References

- Fujiwara and Kato, *Foundations of Rigid Geometry I*, Lemma 2.2.15 and
  Corollary 2.2.16, motivate the intersection and generization examples.
- Mathlib's `Topology.Order.UpperLowerSetTopology` supplies the non-Hausdorff
  upper-set space and its specialization lemmas used in the boundary examples.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set TopologicalSpace
open scoped Topology

namespace SpectralStoneDualityExamples

section Boundaries

local instance : TopologicalSpace Empty := ⊥

private theorem empty_constructiblyClosed :
    IsClosed[constructibleTopology Empty] (∅ : Set Empty) :=
  @isClosed_empty Empty (constructibleTopology Empty)

example : QuasiSober (∅ : Set Empty) := by
  exact (spectralSpace_subtype_of_isClosed_constructible
    empty_constructiblyClosed).toQuasiSober

example : SpectralSpace (Set.univ : Set Empty) :=
  spectralSpace_subtype_of_isClosed_constructible
    (@isClosed_univ Empty (constructibleTopology Empty))

end Boundaries

section ProperDiscrete

local instance : TopologicalSpace (Fin 3) := ⊥

private def twoPoints : Set (Fin 3) := {0, 1}

private theorem twoPoints_constructiblyClosed :
    IsClosed[constructibleTopology (Fin 3)] twoPoints :=
  (Set.toFinite _).isCompact.isClosed_constructibleTopology_of_isClosed
    (isClosed_discrete _)

example : (0 : Fin 3) ∈ twoPoints ∧ (2 : Fin 3) ∉ twoPoints := by
  simp [twoPoints]

example : QuasiSober twoPoints := by
  exact (spectralSpace_subtype_of_isClosed_constructible
    twoPoints_constructiblyClosed).toQuasiSober

example : IsCompact ((Subtype.val : twoPoints → Fin 3) ⁻¹' ({0} : Set (Fin 3))) := by
  have hmap : IsSpectralMap (Subtype.val : twoPoints → Fin 3) :=
    isSpectralMap_subtypeVal_of_isClosed_constructible twoPoints_constructiblyClosed
  exact hmap.isCompact_preimage_of_isOpen (isOpen_discrete _) isCompact_singleton

end ProperDiscrete

section UpperSet

private abbrev TwoPointUpper := Topology.WithUpperSet (Fin 2)

private def bottom : TwoPointUpper := Topology.WithUpperSet.toUpperSet 0
private def top : TwoPointUpper := Topology.WithUpperSet.toUpperSet 1

private instance : Finite TwoPointUpper :=
  Finite.of_injective (Topology.WithUpperSet.ofUpperSet : TwoPointUpper → Fin 2)
    Topology.WithUpperSet.ofUpperSet.injective

private instance : T0Space TwoPointUpper :=
  (t0Space_iff_inseparable TwoPointUpper).2 (by
    intro left right h
    obtain ⟨hleft, hright⟩ := inseparable_iff_specializes_and.mp h
    apply Topology.WithUpperSet.ofUpperSet_inj.mp
    apply le_antisymm
    · exact Topology.WithUpperSet.ofUpperSet_le_iff.mpr
        (Topology.IsUpperSet.specializes_iff_le.mp hright)
    · exact Topology.WithUpperSet.ofUpperSet_le_iff.mpr
        (Topology.IsUpperSet.specializes_iff_le.mp hleft))

private theorem closedBottom : IsClosed ({bottom} : Set TwoPointUpper) := by
  have hIic : (Set.Iic bottom : Set TwoPointUpper) = {bottom} := by
    ext point
    simp only [Set.mem_Iic, Set.mem_singleton_iff]
    change (Topology.WithUpperSet.ofUpperSet point : Fin 2) ≤ (0 : Fin 2) ↔
      (Topology.WithUpperSet.ofUpperSet point : Fin 2) = (0 : Fin 2)
    simp
  rw [← hIic]
  exact Topology.IsUpperSet.isClosed_iff_isLower.mpr (isLowerSet_Iic bottom)

private theorem bottom_constructiblyClosed :
    IsClosed[constructibleTopology TwoPointUpper] ({bottom} : Set TwoPointUpper) :=
  (Set.toFinite _).isCompact.isClosed_constructibleTopology_of_isClosed closedBottom

private theorem top_specializes_bottom : top ⤳ bottom :=
  Topology.IsUpperSet.specializes_iff_le.mpr (by
    change (0 : Fin 2) ≤ 1
    decide)

example : ¬ (∀ x ∈ ({bottom} : Set TwoPointUpper),
    ∀ y, y ⤳ x → y ∈ ({bottom} : Set TwoPointUpper)) := by
  intro h
  have heq := Set.mem_singleton_iff.mp (h bottom (by simp) top top_specializes_bottom)
  change (1 : Fin 2) = 0 at heq
  exact (by decide : (1 : Fin 2) ≠ 0) heq

example : ¬ T2Space TwoPointUpper := by
  intro hT2
  have heq := t1Space_iff_specializes_imp_eq.mp hT2.t1Space top_specializes_bottom
  change (1 : Fin 2) = 0 at heq
  exact (by decide : (1 : Fin 2) ≠ 0) heq

example : QuasiSober ({bottom} : Set TwoPointUpper) := by
  exact (spectralSpace_subtype_of_isClosed_constructible
    bottom_constructiblyClosed).toQuasiSober

example : IsCompact
    ((Subtype.val : ({bottom} : Set TwoPointUpper) → TwoPointUpper) ⁻¹'
      (Set.univ : Set TwoPointUpper)) := by
  have hmap := isSpectralMap_subtypeVal_of_isClosed_constructible
    bottom_constructiblyClosed
  exact hmap.isCompact_preimage_of_isOpen isOpen_univ isCompact_univ

example : nhdsKer ({bottom} : Set TwoPointUpper) = Set.univ := by
  rw [Topology.IsUpperSet.nhdsKer_singleton]
  ext point
  change (0 : Fin 2) ≤ Topology.WithUpperSet.ofUpperSet point ↔ True
  simp

example : nhdsKer ({top} : Set TwoPointUpper) = {top} := by
  rw [Topology.IsUpperSet.nhdsKer_singleton]
  ext point
  simp only [Set.mem_Ici, Set.mem_singleton_iff]
  change (1 : Fin 2) ≤ (Topology.WithUpperSet.ofUpperSet point : Fin 2) ↔
    (Topology.WithUpperSet.ofUpperSet point : Fin 2) = (1 : Fin 2)
  exact ⟨fun h ↦ le_antisymm (Fin.le_last _) h, fun h ↦ h ▸ le_rfl⟩

example : CompactSpace (nhdsKer ({bottom} : Set TwoPointUpper)) ∧
    ∃ point : nhdsKer ({bottom} : Set TwoPointUpper),
      IsClosed ({point} : Set (nhdsKer ({bottom} : Set TwoPointUpper))) ∧
      ∀ z, IsClosed ({z} : Set (nhdsKer ({bottom} : Set TwoPointUpper))) →
        z = point := by
  have hcompact : CompactSpace (nhdsKer ({bottom} : Set TwoPointUpper)) :=
    (spectralSpace_nhdsKer_singleton bottom).toCompactSpace
  let original : nhdsKer ({bottom} : Set TwoPointUpper) :=
    ⟨bottom, mem_nhdsKer_singleton.mpr (specializes_refl bottom)⟩
  refine ⟨hcompact, original, isClosed_singleton_nhdsKer bottom, ?_⟩
  intro z hz
  exact Subtype.ext ((isClosed_singleton_nhdsKer_iff bottom z).mp hz)

end UpperSet

section InfiniteIntersection

private instance : PrespectralSpace (ℕ → Bool) :=
  PrespectralSpace.of_isTopologicalBasis
    (isTopologicalBasis_pi (fun _ : ℕ ↦ isTopologicalBasis_singletons Bool)) (by
      rintro U ⟨V, I, hV, rfl⟩
      apply IsClosed.isCompact
      apply isClosed_set_pi
      intro i hi
      obtain ⟨value, hvalue⟩ := hV i hi
      rw [hvalue]
      exact isClosed_singleton)

private instance : SpectralSpace (ℕ → Bool) where
  __ := (inferInstance : T0Space (ℕ → Bool))
  __ := (inferInstance : CompactSpace (ℕ → Bool))
  __ := (inferInstance : QuasiSober (ℕ → Bool))
  __ := (inferInstance : QuasiSeparatedSpace (ℕ → Bool))
  __ := (inferInstance : PrespectralSpace (ℕ → Bool))

private def cylinder (n : ℕ) : Set (ℕ → Bool) :=
  ⋂ i ∈ Finset.range n, (fun f : ℕ → Bool ↦ f i) ⁻¹' {false}

private theorem cylinder_open (n : ℕ) : IsOpen (cylinder n) := by
  unfold cylinder
  exact (Finset.range n).finite_toSet.isOpen_biInter (fun i _ ↦
    (isOpen_discrete _).preimage (continuous_apply i))

private theorem cylinder_compact (n : ℕ) : IsCompact (cylinder n) := by
  apply IsClosed.isCompact
  unfold cylinder
  exact isClosed_biInter (fun i _ ↦ isClosed_singleton.preimage (continuous_apply i))

private theorem cylinder_intersection :
    (⋂ n : ℕ, cylinder n) = ({fun _ : ℕ ↦ false} : Set (ℕ → Bool)) := by
  ext f
  constructor
  · intro hf
    apply mem_singleton_iff.mpr
    funext i
    have hn : f ∈ cylinder (i + 1) := mem_iInter.mp hf (i + 1)
    have hi : f ∈ (fun g : ℕ → Bool ↦ g i) ⁻¹' {false} :=
      mem_iInter₂.mp hn i (Finset.mem_range.mpr (Nat.lt_succ_self i))
    exact hi
  · intro hf
    rw [mem_singleton_iff] at hf
    subst f
    simp [cylinder]

private theorem cylinder_intersection_not_open :
    ¬ IsOpen (⋂ n : ℕ, cylinder n) := by
  rw [cylinder_intersection]
  intro hOpen
  classical
  obtain ⟨I, U, hIU, hI⟩ :=
    isOpen_pi_iff.mp hOpen (fun _ : ℕ ↦ false) (by simp)
  let index : ℕ := I.sup id + 1
  have hindex : index ∉ I := by
    intro hmem
    have hle : index ≤ I.sup id := Finset.le_sup (f := id) hmem
    exact (not_lt_of_ge hle) (Nat.lt_succ_self _)
  let g : ℕ → Bool := fun i ↦ if i = index then true else false
  have hg : g ∈ (I : Set ℕ).pi U := by
    apply Set.mem_pi.mpr
    intro i hi
    have hine : i ≠ index := by
      intro heq
      exact hindex (heq ▸ hi)
    simpa [g, hine] using (hIU i hi).2
  have heq : g = (fun _ : ℕ ↦ false) := mem_singleton_iff.mp (hI hg)
  have h := congrFun heq index
  simp [g] at h

example : ∃ F : Set (Set (ℕ → Bool)),
    (∀ U ∈ F, IsOpen U ∧ IsCompact U) ∧
    ¬ IsOpen (⋂₀ F) ∧ QuasiSober (⋂₀ F) := by
  let F : Set (Set (ℕ → Bool)) := Set.range cylinder
  have hF : ∀ U ∈ F, IsOpen U ∧ IsCompact U := by
    rintro U ⟨n, rfl⟩
    exact ⟨cylinder_open n, cylinder_compact n⟩
  have hnotOpen : ¬ IsOpen (⋂₀ F) := by
    rw [Set.sInter_range]
    exact cylinder_intersection_not_open
  exact ⟨F, hF, hnotOpen,
    (spectralSpace_sInter_of_compactOpen F hF).toQuasiSober⟩

end InfiniteIntersection

end SpectralStoneDualityExamples
