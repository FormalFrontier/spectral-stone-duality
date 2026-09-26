/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
public import Mathlib.Topology.Category.TopCat.Limits.Konig
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.ConstructibleTopology

public section

set_option warningAsError true

/-!
# Cofiltered limits of spectral spaces

This file proves that small cofiltered limits of spectral spaces along spectral
maps are spectral. The proof compares the ordinary topological limit with the
compact Hausdorff limit formed from the constructible topologies. It also exposes
compactness and spectrality of the limit projections and a compact-open cylinder
basis for the limit.
-/

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v

noncomputable section

namespace SpectralStoneDuality

/-- The constructible topology of a T0 prespectral space is Hausdorff. -/
theorem t2Space_constructible (X : Type u) [TopologicalSpace X]
    [T0Space X] [PrespectralSpace X] :
    T2Space (WithConstructibleTopology X) := by
  rw [t2Space_iff]
  intro x y hxy
  have hxy' : WithTopology.ofTopology x ≠ WithTopology.ofTopology y := by
    intro h
    exact hxy (WithTopology.ofTopology_injective _ h)
  obtain ⟨U, hUopen, hUxy⟩ := exists_isOpen_xor_mem hxy'
  rcases hUxy with hUxy | hUyx
  · obtain ⟨V, ⟨hVopen, hVcompact⟩, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hUxy.1 hUopen
    let V' : Set (WithConstructibleTopology X) := WithTopology.ofTopology ⁻¹' V
    refine ⟨V', V'ᶜ, ?_, ?_, ?_, ?_, disjoint_compl_right⟩
    · rw [WithConstructibleTopology.isOpen_iff]
      convert hVcompact.isOpen_constructibleTopology_of_isOpen hVopen using 1
      ext z
      simp only [V', mem_preimage]
    · exact (show IsClosed V' from by
        rw [WithConstructibleTopology.isClosed_iff]
        convert hVcompact.isClosed_constructibleTopology_of_isOpen hVopen using 1
        ext z
        simp only [V', mem_preimage]).isOpen_compl
    · exact hxV
    · exact fun hyV ↦ hUxy.2 (hVU hyV)
  · obtain ⟨V, ⟨hVopen, hVcompact⟩, hyV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hUyx.1 hUopen
    let V' : Set (WithConstructibleTopology X) := WithTopology.ofTopology ⁻¹' V
    refine ⟨V'ᶜ, V', ?_, ?_, ?_, ?_, disjoint_compl_left⟩
    · exact (show IsClosed V' from by
        rw [WithConstructibleTopology.isClosed_iff]
        convert hVcompact.isClosed_constructibleTopology_of_isOpen hVopen using 1
        ext z
        simp only [V', mem_preimage]).isOpen_compl
    · rw [WithConstructibleTopology.isOpen_iff]
      convert hVcompact.isOpen_constructibleTopology_of_isOpen hVopen using 1
      ext z
      simp only [V', mem_preimage]
    · exact fun hxV ↦ hUyx.2 (hVU hxV)
    · exact hyV

/-- A spectral map is continuous for the constructible topologies. -/
theorem IsSpectralMap.continuous_constructible {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsSpectralMap f) :
    @Continuous X Y (constructibleTopology X) (constructibleTopology Y) f := by
  rw [continuous_generateFrom_iff]
  intro s hs
  apply isOpen_generateFrom_of_mem
  rcases hs with hs | hs
  · exact Or.inl ⟨hs.1.preimage hf.continuous,
      hf.isCompact_preimage_of_isOpen hs.1 hs.2⟩
  · refine Or.inr ⟨hs.1.preimage hf.continuous, ?_⟩
    rw [← preimage_compl]
    exact hf.isCompact_preimage_of_isOpen hs.1.isOpen_compl hs.2

/-- The constructible topology is finer than the original topology on a
prespectral space. -/
theorem continuous_constructibleToOriginal (X : Type u) [TopologicalSpace X]
    [PrespectralSpace X] :
    @Continuous X X (constructibleTopology X) inferInstance id := by
  rw [continuous_def]
  intro s hs
  change IsOpen[constructibleTopology X] s
  refine (@isOpen_iff_forall_mem_open X (constructibleTopology X) s).mpr fun x hx ↦ ?_
  obtain ⟨U, ⟨hUopen, hUcompact⟩, hxU, hUs⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hx hs
  exact ⟨U, hUs, hUcompact.isOpen_constructibleTopology_of_isOpen hUopen, hxU⟩

/-- Replace every object and map of a spectral diagram by its constructible topology. -/
def constructibleDiagram {J : Type v} [SmallCategory J]
    (F : J ⥤ TopCat.{max v u})
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    J ⥤ TopCat.{max v u} where
  obj j := TopCat.of (WithConstructibleTopology (F.obj j))
  map {i j} f := TopCat.ofHom
    { toFun := fun x ↦ WithTopology.toTopology _
        (F.map f (WithTopology.ofTopology x))
      continuous_toFun := by
        have hfrom := WithTopology.continuous_ofTopology
          (constructibleTopology (F.obj i))
        have hmiddle : @Continuous (F.obj i) (F.obj j)
            (constructibleTopology (F.obj i)) (constructibleTopology (F.obj j)) (F.map f) :=
          SpectralStoneDuality.IsSpectralMap.continuous_constructible (hmap f)
        have hto := WithTopology.continuous_toTopology
          (constructibleTopology (F.obj j))
        exact @Continuous.comp
          (WithConstructibleTopology (F.obj i)) (F.obj j)
          (WithConstructibleTopology (F.obj j)) inferInstance
          (constructibleTopology (F.obj j)) inferInstance _ _ hto
          (@Continuous.comp
            (WithConstructibleTopology (F.obj i)) (F.obj i) (F.obj j) inferInstance
            (constructibleTopology (F.obj i)) (constructibleTopology (F.obj j))
            _ _ hmiddle hfrom) }
  map_id j := by
    ext x
    change F.map (𝟙 j) (WithTopology.ofTopology x) = WithTopology.ofTopology x
    rw [F.map_id]
    rfl
  map_comp f g := by
    ext x
    change F.map (f ≫ g) (WithTopology.ofTopology x) =
      F.map g (F.map f (WithTopology.ofTopology x))
    rw [F.map_comp]
    rfl

/-- The constructible version of a spectral diagram has a compact Hausdorff
limit. This is the compactness input for the original-topology limit. -/
theorem compactSpace_constructibleLimit {J : Type v} [SmallCategory J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    CompactSpace (TopCat.limitCone (constructibleDiagram F hmap)).pt := by
  let G := constructibleDiagram F hmap
  let _ (j : J) : SpectralSpace (F.obj j) := hX j
  let _ (j : J) : CompactSpace (G.obj j) :=
    compactSpace_withConstructibleTopology
  let _ (j : J) : T2Space (G.obj j) := by
    change T2Space (WithConstructibleTopology (F.obj j))
    exact t2Space_constructible (F.obj j)
  change CompactSpace
    { x : ∀ j : J, G.obj j |
      ∀ {i j : J} (f : i ⟶ j), G.map f (x i) = x j }
  rw [← isCompact_iff_compactSpace]
  apply IsClosed.isCompact
  have hset :
      { x : ∀ j : J, G.obj j |
        ∀ {i j : J} (f : i ⟶ j), G.map f (x i) = x j } =
        ⋂ (i : J) (j : J) (f : i ⟶ j), { x | G.map f (x i) = x j } := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro f
  apply isClosed_eq
  · exact ((G.map f).hom.continuous).comp (continuous_apply i)
  · exact continuous_apply j

/-- Forget the constructible topologies on a compatible section. -/
def fromConstructibleLimit {J : Type v} [SmallCategory J]
    (F : J ⥤ TopCat.{max v u})
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    (TopCat.limitCone (constructibleDiagram F hmap)).pt →
      (TopCat.limitCone F).pt := fun x =>
  ⟨fun j ↦ WithTopology.ofTopology (x.1 j), by
    intro i j f
    exact congrArg WithTopology.ofTopology (x.2 f)⟩

theorem continuous_fromConstructibleLimit {J : Type v} [SmallCategory J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, PrespectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    Continuous (fromConstructibleLimit F hmap) := by
  let _ (j : J) : PrespectralSpace (F.obj j) := hX j
  apply Continuous.subtype_mk
  · apply continuous_pi
    intro j
    have hforget : Continuous
        (fun x : WithConstructibleTopology (F.obj j) ↦ WithTopology.ofTopology x) :=
      @Continuous.comp
        (WithConstructibleTopology (F.obj j)) (F.obj j) (F.obj j)
        inferInstance (constructibleTopology (F.obj j)) inferInstance _ _
        (continuous_constructibleToOriginal (F.obj j))
        (WithTopology.continuous_ofTopology (constructibleTopology (F.obj j)))
    exact hforget.comp
      ((TopCat.limitCone (constructibleDiagram F hmap)).π.app j).hom.continuous

theorem surjective_fromConstructibleLimit {J : Type v} [SmallCategory J]
    (F : J ⥤ TopCat.{max v u})
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    Function.Surjective (fromConstructibleLimit F hmap) := by
  intro x
  let y : (TopCat.limitCone (constructibleDiagram F hmap)).pt :=
    ⟨fun j ↦ WithTopology.toTopology (constructibleTopology (F.obj j)) (x.1 j), by
      intro i j f
      exact congrArg (WithTopology.toTopology (constructibleTopology (F.obj j))) (x.2 f)⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  funext j
  rfl

/-- The original-topology limit is compact, as a continuous image of the
compact Hausdorff constructible-topology limit. -/
theorem compactSpace_limit_of_spectral {J : Type v} [SmallCategory J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    CompactSpace (TopCat.limitCone F).pt := by
  let _ : CompactSpace (TopCat.limitCone (constructibleDiagram F hmap)).pt :=
    compactSpace_constructibleLimit F hX hmap
  let _ (j : J) : SpectralSpace (F.obj j) := hX j
  exact (surjective_fromConstructibleLimit F hmap).compactSpace
    (continuous_fromConstructibleLimit F (fun _ ↦ inferInstance) hmap)

/-- The inverse image of a compact open under a limit projection is compact.
The constructible version of the cylinder is closed in a compact Hausdorff
limit, and forgetting constructible topologies maps it onto the original
cylinder. -/
theorem isCompact_preimage_limitProjection {J : Type v} [SmallCategory J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f))
    (j : J) {U : Set (F.obj j)} (hUopen : IsOpen U) (hUcompact : IsCompact U) :
    IsCompact ((TopCat.limitCone F).π.app j ⁻¹' U) := by
  let G := constructibleDiagram F hmap
  let _ (i : J) : SpectralSpace (F.obj i) := hX i
  let _ : CompactSpace (TopCat.limitCone G).pt :=
    compactSpace_constructibleLimit F hX hmap
  let U' : Set (G.obj j) := WithTopology.ofTopology ⁻¹' U
  have hU'closed : IsClosed U' := by
    change IsClosed (WithTopology.ofTopology ⁻¹' U)
    rw [WithConstructibleTopology.isClosed_iff]
    convert hUcompact.isClosed_constructibleTopology_of_isOpen hUopen using 1
    ext x
    simp only [Set.mem_preimage]
  have hCclosed : IsClosed ((TopCat.limitCone G).π.app j ⁻¹' U') :=
    hU'closed.preimage ((TopCat.limitCone G).π.app j).hom.continuous
  have hC : IsCompact ((TopCat.limitCone G).π.app j ⁻¹' U') := by
    exact @IsClosed.isCompact (TopCat.limitCone G).pt _
      ((TopCat.limitCone G).π.app j ⁻¹' U')
      (compactSpace_constructibleLimit F hX hmap) hCclosed
  have hsurj := surjective_fromConstructibleLimit F hmap
  have himage :
      fromConstructibleLimit F hmap '' ((TopCat.limitCone G).π.app j ⁻¹' U') =
        (TopCat.limitCone F).π.app j ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change WithTopology.ofTopology (y.1 j) ∈ U at hy ⊢
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := hsurj x
      refine ⟨y, ?_, rfl⟩
      change WithTopology.ofTopology (y.1 j) ∈ U at hx ⊢
      exact hx
  rw [← himage]
  exact hC.image
    (continuous_fromConstructibleLimit F (fun _ ↦ inferInstance) hmap)

/-- Intersections of two compact-open limit cylinders are compact. -/
theorem isCompact_inter_preimage_limitProjections {J : Type v} [SmallCategory J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f))
    (i j : J) {U : Set (F.obj i)} {V : Set (F.obj j)}
    (hUopen : IsOpen U) (hUcompact : IsCompact U)
    (hVopen : IsOpen V) (hVcompact : IsCompact V) :
    IsCompact
      (((TopCat.limitCone F).π.app i ⁻¹' U) ∩
        ((TopCat.limitCone F).π.app j ⁻¹' V)) := by
  let G := constructibleDiagram F hmap
  let _ (k : J) : SpectralSpace (F.obj k) := hX k
  let _ : CompactSpace (TopCat.limitCone G).pt :=
    compactSpace_constructibleLimit F hX hmap
  let U' : Set (G.obj i) := WithTopology.ofTopology ⁻¹' U
  let V' : Set (G.obj j) := WithTopology.ofTopology ⁻¹' V
  have hU'closed : IsClosed U' := by
    change IsClosed (WithTopology.ofTopology ⁻¹' U)
    rw [WithConstructibleTopology.isClosed_iff]
    convert hUcompact.isClosed_constructibleTopology_of_isOpen hUopen using 1
    ext x
    simp only [Set.mem_preimage]
  have hV'closed : IsClosed V' := by
    change IsClosed (WithTopology.ofTopology ⁻¹' V)
    rw [WithConstructibleTopology.isClosed_iff]
    convert hVcompact.isClosed_constructibleTopology_of_isOpen hVopen using 1
    ext x
    simp only [Set.mem_preimage]
  let C := ((TopCat.limitCone G).π.app i ⁻¹' U') ∩
    ((TopCat.limitCone G).π.app j ⁻¹' V')
  have hCclosed : IsClosed C :=
    (hU'closed.preimage ((TopCat.limitCone G).π.app i).hom.continuous).inter
      (hV'closed.preimage ((TopCat.limitCone G).π.app j).hom.continuous)
  have hC : IsCompact C := by
    exact @IsClosed.isCompact (TopCat.limitCone G).pt _ C
      (compactSpace_constructibleLimit F hX hmap) hCclosed
  have hsurj := surjective_fromConstructibleLimit F hmap
  have himage :
      fromConstructibleLimit F hmap '' C =
        (((TopCat.limitCone F).π.app i ⁻¹' U) ∩
          ((TopCat.limitCone F).π.app j ⁻¹' V)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyU, hyV⟩, rfl⟩
      constructor
      · change WithTopology.ofTopology (y.1 i) ∈ U at hyU ⊢
        exact hyU
      · change WithTopology.ofTopology (y.1 j) ∈ V at hyV ⊢
        exact hyV
    · rintro ⟨hxU, hxV⟩
      obtain ⟨y, rfl⟩ := hsurj x
      refine ⟨y, ⟨?_, ?_⟩, rfl⟩
      · change WithTopology.ofTopology (y.1 i) ∈ U at hxU ⊢
        exact hxU
      · change WithTopology.ofTopology (y.1 j) ∈ V at hxV ⊢
        exact hxV
  rw [← himage]
  exact hC.image
    (continuous_fromConstructibleLimit F (fun _ ↦ inferInstance) hmap)

/-- Every canonical projection from the limit of a spectral diagram is a
spectral map. -/
theorem isSpectralMap_limitProjection {J : Type v} [SmallCategory J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f))
    (j : J) : IsSpectralMap ((TopCat.limitCone F).π.app j) where
  toContinuous := ((TopCat.limitCone F).π.app j).hom.continuous
  isCompact_preimage_of_isOpen {s} hUopen hUcompact :=
    isCompact_preimage_limitProjection F hX hmap j (U := s) hUopen hUcompact

/-- In a cofiltered limit, compact-open cylinders form a topological basis. -/
theorem isTopologicalBasis_compactOpenCylinders {J : Type v} [SmallCategory J]
    [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    IsTopologicalBasis
      {U : Set (TopCat.limitCone F).pt |
        ∃ (j : J) (V : Set (F.obj j)),
          (IsOpen V ∧ IsCompact V) ∧ U = (TopCat.limitCone F).π.app j ⁻¹' V} := by
  let _ (j : J) : SpectralSpace (F.obj j) := hX j
  apply TopCat.isTopologicalBasis_cofiltered_limit F (TopCat.limitCone F)
    (TopCat.limitConeIsLimit F)
    (fun j ↦ {V : Set (F.obj j) | IsOpen V ∧ IsCompact V})
  · intro j
    exact PrespectralSpace.isTopologicalBasis
  · intro j
    exact ⟨isOpen_univ, isCompact_univ⟩
  · intro j U V hU hV
    exact ⟨hU.1.inter hV.1, hU.2.inter_of_isOpen hV.2 hU.1 hV.1⟩
  · intro i j f V hV
    exact ⟨hV.1.preimage (hmap f).continuous,
      (hmap f).isCompact_preimage_of_isOpen hV.1 hV.2⟩

/-- The original-topology cofiltered limit has a basis of compact opens. -/
theorem prespectralSpace_limit_of_spectral {J : Type v} [SmallCategory J]
    [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    PrespectralSpace (TopCat.limitCone F).pt := by
  apply PrespectralSpace.of_isTopologicalBasis
    (isTopologicalBasis_compactOpenCylinders F hX hmap)
  intro U hU
  obtain ⟨j, V, hV, rfl⟩ := hU
  exact isCompact_preimage_limitProjection F hX hmap j hV.1 hV.2

/-- The original-topology cofiltered limit is quasi-separated. -/
theorem quasiSeparatedSpace_limit_of_spectral {J : Type v} [SmallCategory J]
    [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    QuasiSeparatedSpace (TopCat.limitCone F).pt := by
  let B :=
    {U : Set (TopCat.limitCone F).pt |
      ∃ (j : J) (V : Set (F.obj j)),
        (IsOpen V ∧ IsCompact V) ∧ U = (TopCat.limitCone F).π.app j ⁻¹' V}
  let b : B → Set (TopCat.limitCone F).pt := fun U ↦ U.1
  have hb : IsTopologicalBasis (Set.range b) := by
    convert isTopologicalBasis_compactOpenCylinders F hX hmap using 1
    ext U
    constructor
    · rintro ⟨V, rfl⟩
      exact V.2
    · intro hU
      exact ⟨⟨U, hU⟩, rfl⟩
  apply QuasiSeparatedSpace.of_isTopologicalBasis hb
  intro U V
  obtain ⟨i, Ui, hUi, hUeq⟩ := U.2
  obtain ⟨j, Vj, hVj, hVeq⟩ := V.2
  change IsCompact (U.1 ∩ V.1)
  rw [hUeq, hVeq]
  exact isCompact_inter_preimage_limitProjections F hX hmap i j
    hUi.1 hUi.2 hVj.1 hVj.2

/-- Limits of T0 spaces are T0 for the chosen concrete TopCat limit. -/
theorem t0Space_limit_of_spectral {J : Type v} [SmallCategory J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j)) :
    T0Space (TopCat.limitCone F).pt := by
  let _ (j : J) : SpectralSpace (F.obj j) := hX j
  rw [t0Space_iff_exists_isOpen_xor_mem]
  intro x y hxy
  obtain ⟨j, hj⟩ : ∃ j, x.1 j ≠ y.1 j := by
    by_contra h
    push Not at h
    exact hxy (Subtype.ext (funext h))
  obtain ⟨U, hUopen, hUxy⟩ := exists_isOpen_xor_mem hj
  exact ⟨(TopCat.limitCone F).π.app j ⁻¹' U,
    hUopen.preimage ((TopCat.limitCone F).π.app j).hom.continuous, hUxy⟩

/-- A cofiltered limit of spectral spaces is quasi-sober. The generic point of
an irreducible closed subset is assembled from the generic points of the
closures of its images in the factors. -/
theorem quasiSober_limit_of_spectral {J : Type v} [SmallCategory J]
    [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    QuasiSober (TopCat.limitCone F).pt where
  sober := by
    let _ (j : J) : SpectralSpace (F.obj j) := hX j
    intro S hS hSclosed
    let p (j : J) : (TopCat.limitCone F).pt → F.obj j :=
      (TopCat.limitCone F).π.app j
    let Sj (j : J) : Set (F.obj j) := closure (p j '' S)
    have hSj_irred (j : J) : IsIrreducible (Sj j) :=
      (hS.image (p j) ((TopCat.limitCone F).π.app j).hom.continuous.continuousOn).closure
    have hSj_closed (j : J) : IsClosed (Sj j) := isClosed_closure
    let xj (j : J) : F.obj j := (hSj_irred j).genericPoint
    have hxj_generic (j : J) : IsGenericPoint (xj j) (Sj j) :=
      (hSj_irred j).isGenericPoint_genericPoint (hSj_closed j)
    have hmap_image {i j : J} (f : i ⟶ j) :
        F.map f '' (p i '' S) = p j '' S := by
      ext y
      constructor
      · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, hs, (s.2 f).symm⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s.1 i, ⟨s, hs, rfl⟩, s.2 f⟩
    have hmap_closure {i j : J} (f : i ⟶ j) :
        closure (F.map f '' Sj i) = Sj j := by
      dsimp only [Sj]
      rw [closure_image_closure (hmap f).continuous]
      exact congrArg closure (hmap_image f)
    have hxj_compat {i j : J} (f : i ⟶ j) : F.map f (xj i) = xj j := by
      have hi := (hxj_generic i).image (hmap f).continuous
      rw [hmap_closure f] at hi
      exact hi.eq (hxj_generic j)
    let x : (TopCat.limitCone F).pt := ⟨xj, fun {_ _} f ↦ hxj_compat f⟩
    have hbasis := isTopologicalBasis_compactOpenCylinders F hX hmap
    have hx_open (U : Set (TopCat.limitCone F).pt) (hUopen : IsOpen U) :
        x ∈ U ↔ (S ∩ U).Nonempty := by
      constructor
      · intro hxU
        obtain ⟨W, ⟨j, V, hV, rfl⟩, hxW, hWU⟩ :=
          hbasis.exists_subset_of_mem_open hxU hUopen
        have hxjV : xj j ∈ V := by
          change x.1 j ∈ V at hxW
          simpa only [x] using hxW
        obtain ⟨y, hySj, hyV⟩ :=
          (hxj_generic j).mem_open_set_iff hV.1 |>.mp hxjV
        have hinter : (V ∩ (p j '' S)).Nonempty :=
          mem_closure_iff_nhds.mp hySj V (hV.1.mem_nhds hyV)
        obtain ⟨_, hzV, s, hsS, rfl⟩ := hinter
        exact ⟨s, hsS, hWU hzV⟩
      · rintro ⟨s, hsS, hsU⟩
        obtain ⟨W, ⟨j, V, hV, rfl⟩, hsW, hWU⟩ :=
          hbasis.exists_subset_of_mem_open hsU hUopen
        have hSjV : (Sj j ∩ V).Nonempty :=
          ⟨s.1 j, subset_closure ⟨s, hsS, rfl⟩, hsW⟩
        have hxjV : xj j ∈ V :=
          (hxj_generic j).mem_open_set_iff hV.1 |>.mpr hSjV
        apply hWU
        change x.1 j ∈ V
        simpa only [x] using hxjV
    refine ⟨x, isGenericPoint_iff_specializes.mpr fun y ↦ ?_⟩
    constructor
    · intro hxy
      by_contra hyS
      have hySc : y ∈ Sᶜ := hyS
      have hxSc := hxy.mem_open hSclosed.isOpen_compl hySc
      have hnon := (hx_open Sᶜ hSclosed.isOpen_compl).mp hxSc
      obtain ⟨z, hzS, hzSc⟩ := hnon
      exact hzSc hzS
    · intro hyS
      rw [specializes_iff_forall_open]
      intro U hUopen hyU
      exact (hx_open U hUopen).mpr ⟨y, hyS, hyU⟩

/-- A small cofiltered limit of spectral spaces along spectral maps is spectral. -/
theorem spectralSpace_limit_of_spectral {J : Type v} [SmallCategory J]
    [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f)) :
    SpectralSpace (TopCat.limitCone F).pt where
  toT0Space := t0Space_limit_of_spectral F hX
  toCompactSpace := compactSpace_limit_of_spectral F hX hmap
  toQuasiSober := quasiSober_limit_of_spectral F hX hmap
  toQuasiSeparatedSpace := quasiSeparatedSpace_limit_of_spectral F hX hmap
  toPrespectralSpace := prespectralSpace_limit_of_spectral F hX hmap

/-- A small cofiltered limit of nonempty spectral spaces along spectral maps is nonempty. -/
theorem nonempty_limit_of_spectral {J : Type v} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f))
    (hne : ∀ j, Nonempty (F.obj j)) :
    Nonempty (TopCat.limitCone F).pt := by
  let G := constructibleDiagram F hmap
  let _ (j : J) : SpectralSpace (F.obj j) := hX j
  let _ (j : J) : Nonempty (G.obj j) := by
    change Nonempty (WithConstructibleTopology (F.obj j))
    exact Nonempty.map (WithTopology.toTopology _) (hne j)
  let _ (j : J) : CompactSpace (G.obj j) :=
    compactSpace_withConstructibleTopology
  let _ (j : J) : T2Space (G.obj j) := by
    change T2Space (WithConstructibleTopology (F.obj j))
    exact t2Space_constructible (F.obj j)
  have hG : Nonempty (TopCat.limitCone G).pt :=
    TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system G
  obtain ⟨x⟩ := hG
  refine ⟨⟨fun j ↦ WithTopology.ofTopology (x.1 j), ?_⟩⟩
  intro i j f
  have hx := x.2 f
  dsimp [G, constructibleDiagram] at hx
  exact congrArg WithTopology.ofTopology hx

end SpectralStoneDuality
