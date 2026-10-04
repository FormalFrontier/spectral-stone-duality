/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Category

/-!
# Reconstructing a spectral space from its compact opens

A point determines the prime ideal of compact opens avoiding it. Conversely,
a prime ideal cuts out a nonempty irreducible closed set; sobriety provides its
unique generic point. `spaceSpectrumHomeomorph` packages the resulting
homeomorphism, and `spaceUnitIso` expresses its naturality in spectral maps.
This reconstructs spectral spaces, not arbitrary non-sober spaces.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.2(b), Theorem 2.2.8(2). The generic-point construction here
  realizes its quasi-inverse for spectral spaces.
- Mathlib, `Topology.Sober` and `Topology.Spectral.Basic`, for generic points,
  sobriety and compact opens.
-/

public section

set_option warningAsError true

open CategoryTheory Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

open PrimeIdealSpectrum

private def pointAvoidanceIdeal (X : SpectralCat) (x : X) :
    Order.Ideal (TopologicalSpace.CompactOpens X) where
  carrier := {U | x ∉ (U : Set X)}
  nonempty' := ⟨⊥, by
    change x ∉ (∅ : Set X)
    simp⟩
  directed' := by
    intro U hU V hV
    refine ⟨U ⊔ V, ?_, le_sup_left, le_sup_right⟩
    change x ∉ ((U : Set X) ∪ (V : Set X))
    intro hx
    exact hx.elim hU hV
  lower' := by
    intro U V hUV hV hxU
    exact hV (hUV hxU)

private theorem pointAvoidanceIdeal_isPrime (X : SpectralCat) (x : X) :
    (pointAvoidanceIdeal X x).IsPrime := by
  let _ : (pointAvoidanceIdeal X x).IsProper := Order.Ideal.isProper_of_notMem (by
    change ¬ x ∉ ((⊤ : TopologicalSpace.CompactOpens X) : Set X)
    simp)
  apply Order.Ideal.IsPrime.of_mem_or_mem
  intro U V hUV
  change x ∉ ((U ⊓ V : TopologicalSpace.CompactOpens X) : Set X) at hUV
  change x ∉ (U : Set X) ∨ x ∉ (V : Set X)
  simpa only [TopologicalSpace.CompactOpens.coe_inf, Set.mem_inter_iff] using
    Classical.not_and_iff_not_or_not.mp hUV

/-- A point of a spectral space determines the prime ideal of compact opens avoiding it. -/
def spaceToSpectrum (X : SpectralCat) :
    X → PrimeIdealSpectrum (TopologicalSpace.CompactOpens X) :=
  fun x ↦ ⟨pointAvoidanceIdeal X x, pointAvoidanceIdeal_isPrime X x⟩

theorem spaceToSpectrum_preimage_basicOpen (X : SpectralCat)
    (U : TopologicalSpace.CompactOpens X) :
    spaceToSpectrum X ⁻¹' basicOpen (Order.Ideal.principal U) = (U : Set X) := by
  ext x
  simp only [Set.mem_preimage, basicOpen, Set.mem_ofPred_eq, Order.Ideal.principal_le_iff,
    spaceToSpectrum, pointAvoidanceIdeal]
  exact Classical.not_not

theorem continuous_spaceToSpectrum (X : SpectralCat) : Continuous (spaceToSpectrum X) := by
  rw [isTopologicalBasis_basicOpen_principal.continuous_iff]
  rintro _ ⟨U, rfl⟩
  rw [spaceToSpectrum_preimage_basicOpen]
  exact U.isOpen

theorem isSpectralMap_spaceToSpectrum (X : SpectralCat) : IsSpectralMap (spaceToSpectrum X) where
  toContinuous := continuous_spaceToSpectrum X
  isCompact_preimage_of_isOpen := by
    intro s hsOpen hsCompact
    obtain ⟨I, hIs⟩ := isOpen_iff_exists_basicOpen s |>.mp hsOpen
    have hICompact : IsCompact (basicOpen I) := by rwa [hIs]
    obtain ⟨U, rfl⟩ := isCompact_basicOpen_iff I |>.mp hICompact
    rw [← hIs, spaceToSpectrum_preimage_basicOpen]
    exact U.isCompact

theorem spaceToSpectrum_injective (X : SpectralCat) : Function.Injective (spaceToSpectrum X) := by
  intro x y hxy
  apply T0Space.t0
  rw [inseparable_iff_forall_isOpen]
  intro U hU
  constructor
  · intro hxU
    obtain ⟨V, ⟨hVOpen, hVCompact⟩, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxU hU
    let K : TopologicalSpace.CompactOpens X := ⟨⟨V, hVCompact⟩, hVOpen⟩
    have hmem : K ∈ (spaceToSpectrum X x).1 ↔ K ∈ (spaceToSpectrum X y).1 := by rw [hxy]
    change (x ∉ (K : Set X)) ↔ y ∉ (K : Set X) at hmem
    have hyV : y ∈ V := by
      by_contra hy
      exact (hmem.mpr hy) hxV
    exact hVU hyV
  · intro hyU
    obtain ⟨V, ⟨hVOpen, hVCompact⟩, hyV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyU hU
    let K : TopologicalSpace.CompactOpens X := ⟨⟨V, hVCompact⟩, hVOpen⟩
    have hmem : K ∈ (spaceToSpectrum X x).1 ↔ K ∈ (spaceToSpectrum X y).1 := by rw [hxy]
    change (x ∉ (K : Set X)) ↔ y ∉ (K : Set X) at hmem
    have hxV : x ∈ V := by
      by_contra hx
      exact (hmem.mp hx) hyV
    exact hVU hxV

/-- The closed subset cut out by all compact opens in a prime ideal. -/
private def primeClosedSet (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X)) : Set X :=
  ⋂ U : {U : TopologicalSpace.CompactOpens X // U ∈ P.1}, ((U.1 : Set X))ᶜ

private theorem mem_primeClosedSet_iff (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X)) (x : X) :
    x ∈ primeClosedSet X P ↔
      ∀ U : TopologicalSpace.CompactOpens X, U ∈ P.1 → x ∉ (U : Set X) := by
  simp only [primeClosedSet, Set.mem_iInter, Set.mem_compl_iff]
  exact ⟨fun h U hUP ↦ h ⟨U, hUP⟩, fun h U ↦ h U.1 U.2⟩

private theorem isClosed_primeClosedSet (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X)) :
    IsClosed (primeClosedSet X P) := by
  apply isClosed_iInter
  intro U
  exact U.1.isOpen.isClosed_compl

private theorem finsetSup_mem_primeIdeal (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X))
    (s : Finset {U : TopologicalSpace.CompactOpens X // U ∈ P.1}) :
    s.sup (fun U ↦ U.1) ∈ P.1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert U s hU ih =>
      rw [Finset.sup_insert]
      exact P.1.sup_mem U.2 ih

private theorem compactOpen_inter_primeClosedSet_nonempty (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X))
    (K : TopologicalSpace.CompactOpens X) (hKP : K ∉ P.1) :
    ((K : Set X) ∩ primeClosedSet X P).Nonempty := by
  apply K.isCompact.inter_iInter_nonempty
  · intro U
    exact U.1.isOpen.isClosed_compl
  · intro s
    let W : TopologicalSpace.CompactOpens X := s.sup (fun U ↦ U.1)
    have hWP : W ∈ P.1 := finsetSup_mem_primeIdeal X P s
    by_contra hne
    apply hKP
    apply P.1.lower (a := W) (b := K)
    · intro x hxK
      by_contra hxW
      apply hne
      refine ⟨x, hxK, ?_⟩
      simp only [Set.mem_iInter, Set.mem_compl_iff]
      intro U hUs hxU
      exact hxW ((Finset.le_sup (f := fun V ↦ V.1) hUs) hxU)
    · exact hWP

private theorem primeClosedSet_nonempty (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X)) :
    (primeClosedSet X P).Nonempty := by
  have h := compactOpen_inter_primeClosedSet_nonempty X P ⊤ P.2.top_notMem
  simpa using h

private theorem primeClosedSet_isIrreducible (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X)) :
    IsIrreducible (primeClosedSet X P) := by
  refine ⟨primeClosedSet_nonempty X P, ?_⟩
  intro U V hUOpen hVOpen hZU hZV
  obtain ⟨x, hxZ, hxU⟩ := hZU
  obtain ⟨y, hyZ, hyV⟩ := hZV
  obtain ⟨KU, ⟨hKUOpen, hKUCompact⟩, hxKU, hKUU⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxU hUOpen
  obtain ⟨KV, ⟨hKVOpen, hKVCompact⟩, hyKV, hKVV⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyV hVOpen
  let K : TopologicalSpace.CompactOpens X := ⟨⟨KU, hKUCompact⟩, hKUOpen⟩
  let L : TopologicalSpace.CompactOpens X := ⟨⟨KV, hKVCompact⟩, hKVOpen⟩
  have hKP : K ∉ P.1 := by
    intro h
    exact (mem_primeClosedSet_iff X P x |>.mp hxZ K h) hxKU
  have hLP : L ∉ P.1 := by
    intro h
    exact (mem_primeClosedSet_iff X P y |>.mp hyZ L h) hyKV
  have hKLP : K ⊓ L ∉ P.1 := by
    intro h
    exact (P.2.mem_or_mem h).elim hKP hLP
  obtain ⟨z, hzKL, hzZ⟩ := compactOpen_inter_primeClosedSet_nonempty X P (K ⊓ L) hKLP
  change z ∈ (K : Set X) ∩ (L : Set X) at hzKL
  exact ⟨z, hzZ, hKUU hzKL.1, hKVV hzKL.2⟩

/-- The sober generic point associated to a prime ideal of compact opens. -/
noncomputable def spectrumToSpace (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X)) : X :=
  (primeClosedSet_isIrreducible X P).genericPoint

private theorem spectrumToSpace_isGeneric (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X)) :
    IsGenericPoint (spectrumToSpace X P) (primeClosedSet X P) :=
  (primeClosedSet_isIrreducible X P).isGenericPoint_genericPoint
    (isClosed_primeClosedSet X P)

theorem spaceToSpectrum_spectrumToSpace (X : SpectralCat)
    (P : PrimeIdealSpectrum (TopologicalSpace.CompactOpens X)) :
    spaceToSpectrum X (spectrumToSpace X P) = P := by
  apply Subtype.ext
  apply Order.Ideal.ext
  ext U
  change spectrumToSpace X P ∉ (U : Set X) ↔ U ∈ P.1
  constructor
  · intro hxU
    by_contra hUP
    have hZU : (primeClosedSet X P ∩ (U : Set X)).Nonempty := by
      rw [Set.inter_comm]
      exact compactOpen_inter_primeClosedSet_nonempty X P U hUP
    exact hxU ((spectrumToSpace_isGeneric X P).mem_open_set_iff U.isOpen |>.mpr hZU)
  · intro hUP
    exact mem_primeClosedSet_iff X P (spectrumToSpace X P) |>.mp
      (spectrumToSpace_isGeneric X P).mem U hUP

theorem spaceToSpectrum_surjective (X : SpectralCat) :
    Function.Surjective (spaceToSpectrum X) :=
  fun P ↦ ⟨spectrumToSpace X P, spaceToSpectrum_spectrumToSpace X P⟩

/-- The point/prime-ideal equivalence for a spectral space. -/
noncomputable def spaceSpectrumEquiv (X : SpectralCat) :
    X ≃ PrimeIdealSpectrum (TopologicalSpace.CompactOpens X) :=
  Equiv.ofBijective (spaceToSpectrum X)
    ⟨spaceToSpectrum_injective X, spaceToSpectrum_surjective X⟩

theorem spaceToSpectrum_image_compactOpen (X : SpectralCat)
    (U : TopologicalSpace.CompactOpens X) :
    spaceToSpectrum X '' (U : Set X) = basicOpen (Order.Ideal.principal U) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hxU, rfl⟩
    change x ∈ spaceToSpectrum X ⁻¹' basicOpen (Order.Ideal.principal U)
    rwa [spaceToSpectrum_preimage_basicOpen]
  · intro P hP
    obtain ⟨x, rfl⟩ := spaceToSpectrum_surjective X P
    refine ⟨x, ?_, rfl⟩
    change x ∈ spaceToSpectrum X ⁻¹' basicOpen (Order.Ideal.principal U) at hP
    rwa [spaceToSpectrum_preimage_basicOpen] at hP

theorem isOpenMap_spaceToSpectrum (X : SpectralCat) : IsOpenMap (spaceToSpectrum X) := by
  rw [PrespectralSpace.isTopologicalBasis.isOpenMap_iff]
  intro U hU
  let K : TopologicalSpace.CompactOpens X := ⟨⟨U, hU.2⟩, hU.1⟩
  change IsOpen (spaceToSpectrum X '' (K : Set X))
  rw [spaceToSpectrum_image_compactOpen]
  exact isOpen_basicOpen _

/-- A spectral space is homeomorphic to the prime spectrum of its compact-open lattice;
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Theorem 2.2.8(2). -/
noncomputable def spaceSpectrumHomeomorph (X : SpectralCat) :
    X ≃ₜ PrimeIdealSpectrum (TopologicalSpace.CompactOpens X) :=
  (spaceSpectrumEquiv X).toHomeomorphOfContinuousOpen
    (continuous_spaceToSpectrum X) (isOpenMap_spaceToSpectrum X)

/-- A homeomorphism of spectral spaces gives an isomorphism in `SpectralCat`. -/
def SpectralCat.isoMk {X Y : SpectralCat} (e : X ≃ₜ Y) : X ≅ Y where
  hom := ⟨⟨e, e.isProperMap.isSpectralMap⟩⟩
  inv := ⟨⟨e.symm, e.symm.isProperMap.isSpectralMap⟩⟩
  hom_inv_id := by
    apply SpectralCat.ext
    intro x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply SpectralCat.ext
    intro y
    exact e.apply_symm_apply y

/-- The spectral-space-side component of Stone duality. -/
noncomputable def spaceUnitComponent (X : SpectralCat) :
    X ≅ (compactOpenFunctor ⋙ spectrumFunctor).obj X :=
  SpectralCat.isoMk (spaceSpectrumHomeomorph X)

/-- Naturality of the space-side reconstruction `X ≅ Spec(QCOuv X)`;
Fujiwara--Kato, *Foundations of Rigid Geometry I*, Theorem 2.2.8(2). -/
noncomputable def spaceUnitIso :
    𝟭 SpectralCat ≅ compactOpenFunctor ⋙ spectrumFunctor :=
  NatIso.ofComponents spaceUnitComponent fun {X Y} f ↦ by
    apply SpectralCat.ext
    intro x
    apply Subtype.ext
    apply Order.Ideal.ext
    ext U
    rfl

end SpectralStoneDuality
