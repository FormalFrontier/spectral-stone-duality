/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Limits
public import SpectralStoneDuality.CompactOpenBasis
public import Mathlib.Topology.Compactness.Bases
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

public section

set_option warningAsError true

/-!
# Maps of cofiltered limits of spectral spaces

For natural transformations of small cofiltered diagrams of spectral spaces,
spectrality, surjectivity, and closedness pass to the induced map of arbitrary
limiting cones. The induced map is Mathlib's `IsLimit.map`; its projection
equation is `IsLimit.map_π`.

For a cofiltered-or-empty diagram with a specified object, surjective or closed
spectral transition maps give the corresponding property of the projection
from any limiting cone to that object.

## References

- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Chapter 0, §2.2(c), Theorem 2.2.13(1)–(3) and Corollary 2.2.14. These
  statements generalize directed systems to small cofiltered categories and
  use supplied limiting cones; the projection conclusions do not require
  nonempty stages. The spectral-map proof uses a finite compact-open cylinder
  cover, while the surjective and closed proofs use constructible closed
  fibers instead of the source's spectral-subspace/fiber lemmas.
- Mathlib, `CategoryTheory.Limits.ConcreteCategory.Basic` and
  `CategoryTheory.Filtered.Final`, for induced cone maps and cofinality;
  `Topology.Spectral.ConstructibleTopology`, for the constructible approach.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace SpectralStoneDuality

variable {J : Type v} [SmallCategory J] [IsCofiltered J]
    {F G : J ⥤ TopCat.{max v u}} (f : F ⟶ G)
    (C : Cone F) (D : Cone G)

omit [IsCofiltered J] in
private theorem isCompact_preimage_coneProjection
    (hC : IsLimit C) (hF : ∀ j, SpectralSpace (F.obj j))
    (hFmap : ∀ {i j : J} (g : i ⟶ j), IsSpectralMap (F.map g))
    (j : J) {U : Set (F.obj j)} (hUopen : IsOpen U) (hUcompact : IsCompact U) :
    IsCompact (C.π.app j ⁻¹' U) := by
  let e := (TopCat.limitConeIsLimit F).conePointUniqueUpToIso hC
  let homeo := TopCat.homeoOfIso e
  have hprojection :
      (fun x : (TopCat.limitCone F).pt ↦ C.π.app j (homeo x)) =
        (fun x ↦ (TopCat.limitCone F).π.app j x) := by
    funext x
    exact congrArg (fun q ↦ q x)
      (IsLimit.conePointUniqueUpToIso_hom_comp (TopCat.limitConeIsLimit F) hC j)
  have hcanonical := isCompact_preimage_limitProjection F hF hFmap j hUopen hUcompact
  have hpreimage : homeo ⁻¹' (C.π.app j ⁻¹' U) =
      (TopCat.limitCone F).π.app j ⁻¹' U := by
    ext x
    exact Iff.of_eq (congrArg (fun g ↦ g x ∈ U) hprojection)
  rw [← Set.image_preimage_eq (C.π.app j ⁻¹' U) homeo.surjective,
    hpreimage]
  exact hcanonical.image homeo.continuous

private theorem exists_compatible_constructible_closed
    (hF : ∀ j, SpectralSpace (F.obj j))
    (hFmap : ∀ {i j : J} (g : i ⟶ j), IsSpectralMap (F.map g))
    (Z : ∀ j, Set ((constructibleDiagram F hFmap).obj j))
    (hZclosed : ∀ j, IsClosed (Z j))
    (hZnonempty : ∀ j, (Z j).Nonempty)
    (hZmap : ∀ {i j : J} (g : i ⟶ j),
      Set.MapsTo ((constructibleDiagram F hFmap).map g) (Z i) (Z j)) :
    ∃ z : (TopCat.limitCone (constructibleDiagram F hFmap)).pt,
      ∀ j, z.1 j ∈ Z j := by
  let K := constructibleDiagram F hFmap
  let H : J ⥤ TopCat.{max v u} := {
    obj j := TopCat.of (Z j)
    map {i j} g := TopCat.ofHom
      ⟨(hZmap g).restrict (K.map g) _ _, (K.map g).hom.continuous.restrict (hZmap g)⟩
    map_id j := by
      apply TopCat.ext
      intro z
      apply Subtype.ext
      simp
    map_comp {i j k} g h := by
      apply TopCat.ext
      intro z
      apply Subtype.ext
      change K.map (g ≫ h) z.1 = K.map h (K.map g z.1)
      simp }
  let _ (j : J) : SpectralSpace (F.obj j) := hF j
  let _ (j : J) : CompactSpace (K.obj j) := compactSpace_withConstructibleTopology
  let _ (j : J) : T2Space (K.obj j) := t2Space_constructible (F.obj j)
  let _ (j : J) : CompactSpace (H.obj j) :=
    isCompact_iff_compactSpace.mp (hZclosed j).isCompact
  let _ (j : J) : T2Space (H.obj j) := inferInstance
  let _ (j : J) : Nonempty (H.obj j) := by
    obtain ⟨z, hz⟩ := hZnonempty j
    exact ⟨⟨z, hz⟩⟩
  obtain ⟨z⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system H
  exact ⟨⟨fun j ↦ (z.1 j).1, fun {_ _} g ↦ congrArg Subtype.val (z.2 g)⟩,
    fun j ↦ (z.1 j).2⟩

private theorem continuous_constructible_spectral {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {g : X → Y}
    (hg : IsSpectralMap g) :
    Continuous (fun z : WithConstructibleTopology X ↦
      WithTopology.toTopology (constructibleTopology Y) (g (WithTopology.ofTopology z))) := by
  exact @Continuous.comp _ _ _ _ (constructibleTopology Y) _ _ _
    (WithTopology.continuous_toTopology (constructibleTopology Y))
    (@Continuous.comp _ _ _ _ (constructibleTopology X) (constructibleTopology Y) _ _
      (SpectralStoneDuality.IsSpectralMap.continuous_constructible hg)
      (WithTopology.continuous_ofTopology (constructibleTopology X)))

private theorem isClosed_constructible_fiber {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [SpectralSpace Y]
    {g : X → Y} (hg : IsSpectralMap g) (y : Y) :
    IsClosed {z : WithConstructibleTopology X | g (WithTopology.ofTopology z) = y} := by
  let _ : T2Space (WithConstructibleTopology Y) := t2Space_constructible Y
  have hclosed : IsClosed ((fun z : WithConstructibleTopology X ↦
    WithTopology.toTopology (constructibleTopology Y) (g (WithTopology.ofTopology z))) ⁻¹'
      {WithTopology.toTopology (constructibleTopology Y) y}) :=
    isClosed_singleton.preimage (continuous_constructible_spectral hg)
  convert hclosed using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
    WithTopology.toTopology_inj]

private theorem closure_eq_iInter_coneProjections (hC : IsLimit C)
    (hF : ∀ j, SpectralSpace (F.obj j))
    (hFmap : ∀ {i j : J} (g : i ⟶ j), IsSpectralMap (F.map g))
    (A : Set C.pt) :
    closure A = ⋂ j, C.π.app j ⁻¹' closure (C.π.app j '' A) := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro x hx
      rw [Set.mem_iInter]
      intro j
      exact subset_closure ⟨x, hx, rfl⟩
    · exact isClosed_iInter fun j ↦
        isClosed_closure.preimage (C.π.app j).hom.continuous
  · intro x hx
    rw [mem_closure_iff_nhds]
    intro U hxU
    have hb := compactOpenCylinders_isBasis F C hC hF hFmap
    change IsTopologicalBasis
      (((↑) : Opens C.pt → Set C.pt) '' Set.range (compactOpenCylinder F C)) at hb
    have hb' : IsTopologicalBasis
        (Set.range (fun k : compactOpenCylinderIndex F ↦
          ((compactOpenCylinder F C k : Opens C.pt) : Set C.pt))) := by
      simpa only [← Set.range_comp'] using hb
    obtain ⟨W, ⟨k, rfl⟩, hxW, hWU⟩ := hb'.mem_nhds_iff.mp hxU
    rw [Set.mem_iInter] at hx
    have hxj : C.π.app k.1 x ∈ closure (C.π.app k.1 '' A) := hx k.1
    have hinter : ((k.2.1 : Set (F.obj k.1)) ∩ (C.π.app k.1 '' A)).Nonempty :=
      mem_closure_iff_nhds.mp hxj _
        ((k.2.1 : Opens (F.obj k.1)).isOpen.mem_nhds hxW)
    obtain ⟨_, hzV, z, hzA, rfl⟩ := hinter
    exact ⟨z, hWU hzV, hzA⟩

/-- The map induced by an objectwise spectral natural transformation of
cofiltered spectral diagrams is spectral. This generalizes Fujiwara--Kato,
*Foundations of Rigid Geometry I*, Theorem 2.2.13(1), to supplied cones. -/
theorem isSpectralMap_isLimit_map
    (hC : IsLimit C) (hD : IsLimit D)
    (hF : ∀ j, SpectralSpace (F.obj j))
    (hG : ∀ j, SpectralSpace (G.obj j))
    (hFmap : ∀ {i j : J} (g : i ⟶ j), IsSpectralMap (F.map g))
    (hGmap : ∀ {i j : J} (g : i ⟶ j), IsSpectralMap (G.map g))
    (hf : ∀ j, IsSpectralMap (f.app j)) :
    IsSpectralMap (hD.map C f) := by
  refine ⟨(hD.map C f).hom.continuous, ?_⟩
  intro U hUopen hUcompact
  have hb := compactOpenCylinders_isBasis G D hD hG hGmap
  have hb' : IsTopologicalBasis
      (Set.range (fun k : compactOpenCylinderIndex G ↦
        ((compactOpenCylinder G D k : Opens D.pt) : Set D.pt))) := by
    change IsTopologicalBasis
      (((↑) : Opens D.pt → Set D.pt) '' Set.range (compactOpenCylinder G D)) at hb
    simpa only [← Set.range_comp'] using hb
  obtain ⟨s, hs, hU⟩ :=
    eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _ hb' U hUcompact hUopen
  rw [hU]
  simp only [Set.preimage_iUnion]
  exact hs.isCompact_biUnion fun k _ ↦ by
    have hfun :
        (fun x : C.pt ↦ D.π.app k.1 (hD.map C f x)) =
          (fun x ↦ f.app k.1 (C.π.app k.1 x)) := by
      funext x
      exact congrArg (fun q ↦ q x) (IsLimit.map_π C hD f k.1)
    change IsCompact
      ((fun x : C.pt ↦ D.π.app k.1 (hD.map C f x)) ⁻¹'
        (k.2.1 : Set (G.obj k.1)))
    rw [hfun]
    change IsCompact (C.π.app k.1 ⁻¹' (f.app k.1 ⁻¹' (k.2.1 : Set (G.obj k.1))))
    exact isCompact_preimage_coneProjection C hC hF hFmap k.1
      ((k.2.1 : Opens (G.obj k.1)).isOpen.preimage (hf k.1).continuous)
      ((hf k.1).isCompact_preimage_of_isOpen
        (k.2.1 : Opens (G.obj k.1)).isOpen k.2.2)

/-- An objectwise surjective spectral natural transformation induces a
surjection of cofiltered limits. No spectrality is required of the target
diagram's transition maps. This strengthens the corresponding directed-system
statement in Fujiwara--Kato, *Foundations of Rigid Geometry I*, Theorem 2.2.13(2). -/
theorem surjective_isLimit_map
    (hC : IsLimit C) (hD : IsLimit D)
    (hF : ∀ j, SpectralSpace (F.obj j))
    (hG : ∀ j, SpectralSpace (G.obj j))
    (hFmap : ∀ {i j : J} (g : i ⟶ j), IsSpectralMap (F.map g))
    (hf : ∀ j, IsSpectralMap (f.app j))
    (hsurj : ∀ j, Function.Surjective (f.app j)) :
    Function.Surjective (hD.map C f) := by
  intro y
  let K := constructibleDiagram F hFmap
  let Z (j : J) : Set (K.obj j) :=
    {z | f.app j (WithTopology.ofTopology z) = D.π.app j y}
  have hZclosed (j : J) : IsClosed (Z j) := by
    let _ : SpectralSpace (G.obj j) := hG j
    change IsClosed {z : WithConstructibleTopology (F.obj j) |
      f.app j (WithTopology.ofTopology z) = D.π.app j y}
    exact isClosed_constructible_fiber (hf j) (D.π.app j y)
  have hZnonempty (j : J) : (Z j).Nonempty := by
    obtain ⟨z, hz⟩ := hsurj j (D.π.app j y)
    exact ⟨WithTopology.toTopology (constructibleTopology (F.obj j)) z, hz⟩
  have hZmap {i j : J} (g : i ⟶ j) : Set.MapsTo (K.map g) (Z i) (Z j) := by
    intro z hz
    change f.app j (WithTopology.ofTopology (K.map g z)) = D.π.app j y
    have hnatural : f.app j (F.map g (WithTopology.ofTopology z)) =
        G.map g (f.app i (WithTopology.ofTopology z)) :=
      congrArg (fun q ↦ q (WithTopology.ofTopology z)) (f.naturality g)
    have hcone : G.map g (D.π.app i y) = D.π.app j y := by
      simpa only [TopCat.coe_comp, Function.comp_apply] using
        congrArg (fun q ↦ q y) (D.w g)
    simp only [K, constructibleDiagram_map_apply, WithTopology.ofTopology_toTopology]
    exact hnatural.trans ((congrArg (G.map g) hz).trans hcone)
  obtain ⟨z, hz⟩ := exists_compatible_constructible_closed hF hFmap
    Z hZclosed hZnonempty hZmap
  let x₀ : (TopCat.limitCone F).pt := fromConstructibleLimit F hFmap z
  let x : C.pt := hC.lift (TopCat.limitCone F) x₀
  have hxcoord (j : J) : C.π.app j x = WithTopology.ofTopology (z.1 j) := by
    have hfac := congrArg (fun q ↦ q x₀) (hC.fac (TopCat.limitCone F) j)
    change C.π.app j x = x₀.1 j at hfac
    exact hfac.trans (fromConstructibleLimit_apply F hFmap z j)
  refine ⟨x, Concrete.isLimit_ext G hD _ _ (fun j ↦ ?_)⟩
  have hfac := congrArg (fun q ↦ q x) (IsLimit.map_π C hD f j)
  exact hfac.trans ((congrArg (f.app j) (hxcoord j)).trans (hz j))

/-- An objectwise closed spectral natural transformation induces a closed
map of cofiltered limits. No spectrality is required of the target diagram's
transition maps. This strengthens the corresponding directed-system statement
in Fujiwara--Kato, *Foundations of Rigid Geometry I*, Theorem 2.2.13(3). -/
theorem isClosedMap_isLimit_map
    (hC : IsLimit C) (hD : IsLimit D)
    (hF : ∀ j, SpectralSpace (F.obj j))
    (hG : ∀ j, SpectralSpace (G.obj j))
    (hFmap : ∀ {i j : J} (g : i ⟶ j), IsSpectralMap (F.map g))
    (hf : ∀ j, IsSpectralMap (f.app j))
    (hclosed : ∀ j, IsClosedMap (f.app j)) :
    IsClosedMap (hD.map C f) := by
  intro A hAclosed
  let K := constructibleDiagram F hFmap
  let p (j : J) : C.pt → F.obj j := C.π.app j
  let q (j : J) : D.pt → G.obj j := D.π.app j
  let Cj (j : J) : Set (F.obj j) := closure (p j '' A)
  let Dj (j : J) : Set (G.obj j) := f.app j '' Cj j
  have hCjclosed (j : J) : IsClosed (Cj j) := isClosed_closure
  have hDjclosed (j : J) : IsClosed (Dj j) :=
    hclosed j (Cj j) (hCjclosed j)
  have hprojImage {i j : J} (g : i ⟶ j) :
      F.map g '' (p i '' A) = p j '' A := by
    have hcone (x : C.pt) : F.map g (p i x) = p j x := by
      simpa only [TopCat.coe_comp, Function.comp_apply] using
        congrArg (fun q ↦ q x) (C.w g)
    ext z
    constructor
    · rintro ⟨_, ⟨x, hxA, rfl⟩, rfl⟩
      exact ⟨x, hxA, (hcone x).symm⟩
    · rintro ⟨x, hxA, rfl⟩
      exact ⟨p i x, ⟨x, hxA, rfl⟩, hcone x⟩
  have hCmaps {i j : J} (g : i ⟶ j) : Set.MapsTo (F.map g) (Cj i) (Cj j) := by
    intro x hx
    have himage : F.map g x ∈ F.map g '' closure (p i '' A) := ⟨x, hx, rfl⟩
    have hclosure := image_closure_subset_closure_image (F.map g).hom.continuous himage
    simpa only [Cj, hprojImage g] using hclosure
  have himage : (hD.map C f) '' A = ⋂ j, q j ⁻¹' Dj j := by
    ext y
    constructor
    · rintro ⟨x, hxA, rfl⟩
      rw [Set.mem_iInter]
      intro j
      change q j (hD.map C f x) ∈ Dj j
      have hfac := congrArg (fun r ↦ r x) (IsLimit.map_π C hD f j)
      exact ⟨p j x, subset_closure ⟨x, hxA, rfl⟩, hfac.symm⟩
    · intro hy
      rw [Set.mem_iInter] at hy
      let Z (j : J) : Set (K.obj j) :=
        {z | WithTopology.ofTopology z ∈ Cj j ∧
          f.app j (WithTopology.ofTopology z) = q j y}
      have hZclosed (j : J) : IsClosed (Z j) := by
        let _ : SpectralSpace (F.obj j) := hF j
        let _ : SpectralSpace (G.obj j) := hG j
        have hforget : Continuous
            (fun z : WithConstructibleTopology (F.obj j) ↦ WithTopology.ofTopology z) :=
          @Continuous.comp _ _ _ _ (constructibleTopology (F.obj j)) _ _ _
            (continuous_constructibleToOriginal (F.obj j))
            (WithTopology.continuous_ofTopology (constructibleTopology (F.obj j)))
        have hfiber : IsClosed
            {z : WithConstructibleTopology (F.obj j) |
              f.app j (WithTopology.ofTopology z) = q j y} :=
          isClosed_constructible_fiber (hf j) (q j y)
        exact (hCjclosed j |>.preimage hforget).inter hfiber
      have hZnonempty (j : J) : (Z j).Nonempty := by
        obtain ⟨x, hxCj, hxy⟩ := hy j
        exact ⟨WithTopology.toTopology (constructibleTopology (F.obj j)) x,
          hxCj, hxy⟩
      have hZmap {i j : J} (g : i ⟶ j) : Set.MapsTo (K.map g) (Z i) (Z j) := by
        intro z hz
        have hcone : G.map g (q i y) = q j y := by
          simpa only [TopCat.coe_comp, Function.comp_apply] using
            congrArg (fun r ↦ r y) (D.w g)
        have hnatural : f.app j (F.map g (WithTopology.ofTopology z)) =
            G.map g (f.app i (WithTopology.ofTopology z)) :=
          congrArg (fun r ↦ r (WithTopology.ofTopology z)) (f.naturality g)
        change WithTopology.ofTopology (K.map g z) ∈ Cj j ∧
          f.app j (WithTopology.ofTopology (K.map g z)) = q j y
        simp only [K, constructibleDiagram_map_apply, WithTopology.ofTopology_toTopology]
        exact ⟨hCmaps g hz.1, hnatural.trans ((congrArg (G.map g) hz.2).trans hcone)⟩
      obtain ⟨z, hz⟩ := exists_compatible_constructible_closed hF hFmap
        Z hZclosed hZnonempty hZmap
      let x₀ : (TopCat.limitCone F).pt := fromConstructibleLimit F hFmap z
      let x : C.pt := hC.lift (TopCat.limitCone F) x₀
      have hxcoord (j : J) : p j x = WithTopology.ofTopology (z.1 j) := by
        have hfac := congrArg (fun r ↦ r x₀) (hC.fac (TopCat.limitCone F) j)
        change p j x = x₀.1 j at hfac
        exact hfac.trans (fromConstructibleLimit_apply F hFmap z j)
      have hxClosure : x ∈ closure A := by
        rw [closure_eq_iInter_coneProjections C hC hF hFmap A, Set.mem_iInter]
        intro j
        change p j x ∈ Cj j
        rw [hxcoord j]
        exact (hz j).1
      have hxA : x ∈ A := by simpa only [hAclosed.closure_eq] using hxClosure
      refine ⟨x, hxA, Concrete.isLimit_ext G hD _ _ (fun j ↦ ?_)⟩
      have hfac := congrArg (fun r ↦ r x) (IsLimit.map_π C hD f j)
      exact hfac.trans ((congrArg (f.app j) (hxcoord j)).trans (hz j).2)
  rw [himage]
  exact isClosed_iInter fun j ↦ (hDjclosed j).preimage (D.π.app j).hom.continuous

end SpectralStoneDuality

namespace SpectralStoneDuality

variable {J : Type v} [SmallCategory J] [IsCofilteredOrEmpty J]
    (F : J ⥤ TopCat.{max v u}) (C : Cone F)

private def tailToStage (j : J) :
    Over.forget j ⋙ F ⟶ (Functor.const (Over j)).obj (F.obj j) where
  app X := F.map X.hom
  naturality _ _ g := by
    dsimp
    rw [← F.map_comp, g.w]
    simp

set_option backward.isDefEq.respectTransparency.types false in
omit [IsCofilteredOrEmpty J] in
private theorem tailMap_eq_projection (j : J) [IsConnected (Over j)] :
    (isLimitConstCone (Over j) (F.obj j)).map
      (C.whisker (Over.forget j)) (tailToStage F j) = C.π.app j := by
  let identityStage : Over j := Over.mk (𝟙 j)
  have hcomponent : (tailToStage F j).app identityStage = 𝟙 (F.obj j) := by
    change F.map (𝟙 j) = 𝟙 (F.obj j)
    exact F.map_id j
  have hsource : (C.whisker (Over.forget j)).π.app identityStage = C.π.app j := rfl
  have hfac := IsLimit.map_π (C.whisker (Over.forget j))
    (isLimitConstCone (Over j) (F.obj j)) (tailToStage F j) identityStage
  have hnormalized : (isLimitConstCone (Over j) (F.obj j)).map
      (C.whisker (Over.forget j)) (tailToStage F j) ≫ 𝟙 (F.obj j) =
        C.π.app j ≫ 𝟙 (F.obj j) := by
    simpa only [constCone, Functor.const_obj_obj, NatTrans.id_app,
      hsource, hcomponent] using hfac
  exact (Category.comp_id _).symm.trans (hnormalized.trans (Category.comp_id _))

/-- Generalizing Fujiwara--Kato, *Foundations of Rigid Geometry I*, Corollary 2.2.14,
a projection from a limiting cone of spectral spaces is surjective when
all transition maps are spectral and surjective. -/
theorem surjective_isLimit_projection
    (hC : IsLimit C) (hF : ∀ i, SpectralSpace (F.obj i))
    (hFmap : ∀ {i k : J} (g : i ⟶ k), IsSpectralMap (F.map g))
    (hsurj : ∀ {i k : J} (g : i ⟶ k), Function.Surjective (F.map g))
    (j : J) : Function.Surjective (C.π.app j) := by
  let _ : IsConnected (Over j) := IsCofiltered.isConnected _
  have hTail : IsLimit (C.whisker (Over.forget j)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) C).symm hC
  rw [← tailMap_eq_projection F C j]
  exact surjective_isLimit_map (tailToStage F j) (C.whisker (Over.forget j))
    (constCone (Over j) (F.obj j)) hTail (isLimitConstCone (Over j) (F.obj j))
    (fun X ↦ hF X.left) (fun _ ↦ hF j) (fun g ↦ hFmap g.left)
    (fun X ↦ hFmap X.hom) (fun X ↦ hsurj X.hom)

/-- Generalizing Fujiwara--Kato, *Foundations of Rigid Geometry I*, Corollary 2.2.14,
a projection from a limiting cone of spectral spaces is closed when
all transition maps are spectral and closed. Surjectivity is not assumed. -/
theorem isClosedMap_isLimit_projection
    (hC : IsLimit C) (hF : ∀ i, SpectralSpace (F.obj i))
    (hFmap : ∀ {i k : J} (g : i ⟶ k), IsSpectralMap (F.map g))
    (hclosed : ∀ {i k : J} (g : i ⟶ k), IsClosedMap (F.map g))
    (j : J) : IsClosedMap (C.π.app j) := by
  let _ : IsConnected (Over j) := IsCofiltered.isConnected _
  have hTail : IsLimit (C.whisker (Over.forget j)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) C).symm hC
  rw [← tailMap_eq_projection F C j]
  exact isClosedMap_isLimit_map (tailToStage F j) (C.whisker (Over.forget j))
    (constCone (Over j) (F.obj j)) hTail (isLimitConstCone (Over j) (F.obj j))
    (fun X ↦ hF X.left) (fun _ ↦ hF j) (fun g ↦ hFmap g.left)
    (fun X ↦ hFmap X.hom) (fun X ↦ hclosed X.hom)

end SpectralStoneDuality
