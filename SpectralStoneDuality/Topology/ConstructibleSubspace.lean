/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Subspace
public import SpectralStoneDuality.Topology.LocallyClosed
public import SpectralStoneDuality.Topology.NhdsKer
public import SpectralStoneDuality.Limits
public import Mathlib.Topology.Compactness.NhdsKer

/-!
# Constructibly closed subspaces of spectral spaces

A subset closed in the constructible topology of a spectral space is spectral
with its original subspace topology, and its inclusion is a spectral map.
Consequently, arbitrary intersections with a cofinal family of compact opens
and the generizations of a point have spectral subspace topologies.

The intersection results allow arbitrary families rather than only filters of
opens; the constructibly closed subspace result needs no open presentation.

## References

- Fujiwara and Kato, *Foundations of Rigid Geometry I*, Lemma 2.2.15 and
  Corollary 2.2.16, for compact-open-generated filters and generization subspaces.
  The constructibly closed result here is stronger and its direct compactness
  proof differs from their inverse-limit argument.
- Mathlib's `Topology.Spectral.ConstructibleTopology`, `Topology.Spectral.Prespectral`,
  and `Topology.Sober` supply the constructible compactness, compact-open basis,
  and quasi-sobriety APIs used in the proof.
- Anchor's earlier Formal Frontier Lean work on compact-open neighborhoods of
  `nhdsKer` and cofinal-intersection equality and constructible closedness is
  adapted here. The direct quasi-sobriety proof for constructibly closed
  subspaces is distinct.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set TopologicalSpace
open scoped Topology

universe u

variable {X : Type u} [TopologicalSpace X]

private theorem compactSpace_constructible [SpectralSpace X] :
    @CompactSpace X (constructibleTopology X) := by
  exact @Function.Surjective.compactSpace (WithConstructibleTopology X) X
    inferInstance (constructibleTopology X) _
    (WithTopology.continuous_ofTopology (constructibleTopology X))
    inferInstance (WithTopology.ofTopology_surjective (constructibleTopology X))

private theorem isCompact_of_isClosed_constructible [SpectralSpace X]
    {S : Set X} (hS : IsClosed[constructibleTopology X] S) : IsCompact S := by
  have hScompact : @IsCompact X (constructibleTopology X) S :=
    @IsClosed.isCompact X (constructibleTopology X) S
      (compactSpace_constructible (X := X)) hS
  simpa only [image_id] using
    @IsCompact.image X X (constructibleTopology X) inferInstance S id
      hScompact (SpectralStoneDuality.continuous_constructibleToOriginal X)

/-- The inclusion of a constructibly closed subset of a spectral space is spectral.
This strengthens the open-filter inclusions of Fujiwara–Kato, Lemma 2.2.15. -/
theorem isSpectralMap_subtypeVal_of_isClosed_constructible [SpectralSpace X]
    {S : Set X} (hS : IsClosed[constructibleTopology X] S) :
    IsSpectralMap (Subtype.val : S → X) := by
  apply IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
  intro U hUcompact hUopen
  exact isCompact_of_isClosed_constructible
    (@IsClosed.inter X S U (constructibleTopology X) hS
      (hUcompact.isClosed_constructibleTopology_of_isOpen hUopen))

/-- A constructibly closed subset of a spectral space is spectral with its
original subspace topology. Constructible closedness need not imply closedness
in the original topology. This strengthens the open-filter result of
Fujiwara–Kato, Lemma 2.2.15, via compactness in the constructible topology. -/
theorem spectralSpace_subtype_of_isClosed_constructible [SpectralSpace X]
    {S : Set X} (hS : IsClosed[constructibleTopology X] S) :
    SpectralSpace S := by
  have hmap := isSpectralMap_subtypeVal_of_isClosed_constructible hS
  have hcompact : CompactSpace S :=
    isCompact_iff_compactSpace.mp (isCompact_of_isClosed_constructible hS)
  have hprespectral : PrespectralSpace S :=
    PrespectralSpace.of_isInducing Subtype.val .subtypeVal hmap
  have hquasiSeparated : QuasiSeparatedSpace S :=
    Topology.IsInducing.quasiSeparatedSpace_of_isSpectralMap .subtypeVal hmap
  have hquasiSober : QuasiSober S := by
    refine ⟨?_⟩
    intro C hCirr hCclosed
    let T : Set X := Subtype.val '' C
    have hTirr : IsIrreducible T :=
      hCirr.image Subtype.val continuous_subtype_val.continuousOn
    obtain ⟨D, hDclosed, hT_eq⟩ := hCclosed.image_val
    have hDpatch : IsClosed[constructibleTopology X] D := by
      simpa only [preimage_id] using
        @IsClosed.preimage X X (constructibleTopology X) inferInstance id
          (SpectralStoneDuality.continuous_constructibleToOriginal X) D hDclosed
    have hTpatch : IsClosed[constructibleTopology X] T := by
      change IsClosed[constructibleTopology X] (Subtype.val '' C)
      rw [hT_eq]
      exact @IsClosed.inter X D S (constructibleTopology X) hDpatch hS
    have hTcompact : @IsCompact X (constructibleTopology X) T :=
      @IsClosed.isCompact X (constructibleTopology X) T
        (compactSpace_constructible (X := X)) hTpatch
    let F : Set (Set X) :=
      {U | IsOpen U ∧ IsCompact U ∧ (T ∩ U).Nonempty}
    have hFclosed : ∀ U ∈ F, IsClosed[constructibleTopology X] U := by
      intro U hU
      exact hU.2.1.isClosed_constructibleTopology_of_isOpen hU.1
    have hFfinite : ∀ A ⊆ F, A.Finite → (T ∩ ⋂₀ A).Nonempty := by
      intro A hAF hAfinite
      simpa only [hAfinite.coe_toFinset] using
        (isIrreducible_iff_sInter.mp hTirr) hAfinite.toFinset
          (fun U hU ↦ (hAF (hAfinite.mem_toFinset.mp hU)).1)
          (fun U hU ↦ (hAF (hAfinite.mem_toFinset.mp hU)).2.2)
    have hTinterF : (T ∩ ⋂₀ F).Nonempty :=
      @IsCompact.nonempty_inter_sInter X (constructibleTopology X)
        T hTcompact F hFclosed hFfinite
    obtain ⟨x, hxT, hxF⟩ := hTinterF
    obtain ⟨y, hyC, rfl⟩ := hxT
    refine ⟨y, isGenericPoint_def.mpr ?_⟩
    apply Subset.antisymm
    · exact closure_minimal (singleton_subset_iff.mpr hyC) hCclosed
    · intro z hzC
      apply specializes_iff_mem_closure.mp
      apply (subtype_specializes_iff y z).2
      apply specializes_iff_forall_open.mpr
      intro W hWopen hzW
      obtain ⟨U, ⟨hUopen, hUcompact⟩, hzU, hUW⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hzW hWopen
      have hTU : (T ∩ U).Nonempty := ⟨z, ⟨z, hzC, rfl⟩, hzU⟩
      exact hUW (mem_sInter.mp hxF U ⟨hUopen, hUcompact, hTU⟩)
  exact {
    toT0Space := Topology.IsEmbedding.subtypeVal.t0Space
    toCompactSpace := hcompact
    toQuasiSober := hquasiSober
    toQuasiSeparatedSpace := hquasiSeparated
    toPrespectralSpace := hprespectral
  }

/-- Inclusion of a constructibly closed subset into any containing subspace is
spectral, regardless of whether the containing subset is open or spectral.
This extends the maps to open filter members of Fujiwara–Kato, Lemma 2.2.15. -/
theorem isSpectralMap_inclusion_of_isClosed_constructible [SpectralSpace X]
    {S Y : Set X} (hS : IsClosed[constructibleTopology X] S)
    (hSY : S ⊆ Y) : IsSpectralMap (Set.inclusion hSY : S → Y) := by
  apply SpectralStoneDuality.isSpectralMap_to_subtype_of_comp
  change IsSpectralMap (Subtype.val : S → X)
  exact isSpectralMap_subtypeVal_of_isClosed_constructible hS

/-- A cofinal compact-open subfamily has the same intersection as the original
family. The other members need not be open. -/
theorem sInter_eq_sInter_compactOpenCofinal (F : Set (Set X))
    (hF : ∀ U ∈ F, ∃ V ∈ F, IsOpen V ∧ IsCompact V ∧ V ⊆ U) :
    ⋂₀ F = ⋂₀ {V : Set X | V ∈ F ∧ IsOpen V ∧ IsCompact V} := by
  ext x
  simp only [mem_sInter]
  constructor
  · intro hx V hV
    exact hx V hV.1
  · intro hx U hU
    obtain ⟨V, hVF, hVo, hVc, hVU⟩ := hF U hU
    exact hVU (hx V ⟨hVF, hVo, hVc⟩)

/-- The intersection of a family cofinal in compact opens is constructibly
closed in any topological space. -/
theorem isClosed_constructible_sInter_of_compactOpenCofinal
    (F : Set (Set X))
    (hF : ∀ U ∈ F, ∃ V ∈ F, IsOpen V ∧ IsCompact V ∧ V ⊆ U) :
    IsClosed[constructibleTopology X] (⋂₀ F) := by
  rw [sInter_eq_sInter_compactOpenCofinal F hF]
  exact @isClosed_sInter X (constructibleTopology X) _ (fun V hV ↦
    hV.2.2.isClosed_constructibleTopology_of_isOpen hV.2.1)

/-- A cofinal compact-open subfamily makes an arbitrary intersection spectral,
including the empty and whole intersections. This extends the
compact-open-generated filter case of Fujiwara–Kato, Lemma 2.2.15. -/
theorem spectralSpace_sInter_of_compactOpenCofinal [SpectralSpace X]
    (F : Set (Set X))
    (hF : ∀ U ∈ F, ∃ V ∈ F, IsOpen V ∧ IsCompact V ∧ V ⊆ U) :
    SpectralSpace (⋂₀ F) :=
  spectralSpace_subtype_of_isClosed_constructible
    (isClosed_constructible_sInter_of_compactOpenCofinal F hF)

/-- Any intersection of compact open subsets of a spectral space is spectral. -/
theorem spectralSpace_sInter_of_compactOpen [SpectralSpace X]
    (F : Set (Set X)) (hF : ∀ U ∈ F, IsOpen U ∧ IsCompact U) :
    SpectralSpace (⋂₀ F) :=
  spectralSpace_sInter_of_compactOpenCofinal F (by
    intro U hU
    exact ⟨U, hU, (hF U hU).1, (hF U hU).2, Subset.rfl⟩)

/-- The generizations of a point are the intersection of its compact-open
neighborhoods. In Mathlib, `y ∈ nhdsKer {x}` means `y ⤳ x`. -/
theorem nhdsKer_singleton_eq_sInter_compactOpenNhds [PrespectralSpace X] (x : X) :
    nhdsKer ({x} : Set X) =
      ⋂₀ {U : Set X | IsOpen U ∧ IsCompact U ∧ x ∈ U} := by
  ext y
  constructor
  · intro hy
    apply mem_sInter.mpr
    intro U hU
    exact (mem_nhdsKer.mp hy) U hU.1 (singleton_subset_iff.mpr hU.2.2)
  · intro hy
    apply mem_nhdsKer.mpr
    intro U hUopen hxU
    obtain ⟨V, ⟨hVo, hVc⟩, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open
        (hxU (mem_singleton x)) hUopen
    exact hVU (mem_sInter.mp hy V ⟨hVo, hVc, hxV⟩)

/-- The generizations of a point form a spectral subspace, as in
Fujiwara–Kato, Corollary 2.2.16. -/
theorem spectralSpace_nhdsKer_singleton [SpectralSpace X] (x : X) :
    SpectralSpace (nhdsKer ({x} : Set X)) := by
  rw [nhdsKer_singleton_eq_sInter_compactOpenNhds x]
  exact spectralSpace_sInter_of_compactOpen _ (fun U hU ↦ ⟨hU.1, hU.2.1⟩)

/-- The inclusion of the generizations of a point is a spectral map. -/
theorem isSpectralMap_subtypeVal_nhdsKer_singleton [SpectralSpace X] (x : X) :
    IsSpectralMap (Subtype.val : nhdsKer ({x} : Set X) → X) := by
  rw [nhdsKer_singleton_eq_sInter_compactOpenNhds x]
  apply isSpectralMap_subtypeVal_of_isClosed_constructible
  exact isClosed_constructible_sInter_of_compactOpenCofinal _ (by
    intro U hU
    exact ⟨U, hU, hU.1, hU.2.1, Subset.rfl⟩)
