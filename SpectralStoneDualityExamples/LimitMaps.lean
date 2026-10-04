/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.LimitMaps
public import SpectralStoneDuality.Topology.Finite
public import Mathlib.Topology.Order.LowerUpperTopology

@[expose] public section

set_option warningAsError true

/-!
# Finite examples of maps of cofiltered spectral limits

Two-stage cofiltered diagrams give a spectral surjection from a finite discrete
product onto a two-point space, a noninjective collapse of the Sierpiński space,
and a closed nonsurjective inclusion of its closed point. The induced maps are
also checked independently through their projections before applying the
general limit-map theorems.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set

namespace SpectralStoneDualityExamples.LimitMaps

/-- The constant two-stage diagram on the Sierpiński space. -/
private abbrev sierpinski : Fin 2 ⥤ TopCat :=
  (Functor.const (Fin 2)).obj (TopCat.of Prop)

/-- The constant two-stage diagram on a singleton. -/
private abbrev singleton : Fin 2 ⥤ TopCat :=
  (Functor.const (Fin 2)).obj (TopCat.of PUnit)

/-- The constant two-stage diagram on the empty space. -/
private abbrev empty : Fin 2 ⥤ TopCat :=
  (Functor.const (Fin 2)).obj (TopCat.of Empty)

/-- A constant diagram on a finite discrete product. -/
private abbrev square : Fin 2 ⥤ TopCat :=
  (Functor.const (Fin 2)).obj (TopCat.of (Fin 2 × Fin 2))

/-- A constant diagram on a discrete two-point space. -/
private abbrev pair : Fin 2 ⥤ TopCat :=
  (Functor.const (Fin 2)).obj (TopCat.of (Fin 2))

/-- The projection of the finite discrete product onto its first factor. -/
private abbrev first : TopCat.of (Fin 2 × Fin 2) ⟶ TopCat.of (Fin 2) :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- Collapse the Sierpiński space to a singleton. -/
private abbrev collapse : TopCat.of Prop ⟶ TopCat.of PUnit :=
  TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩

/-- Include the closed point in the Sierpiński space. -/
private abbrev closedPoint : TopCat.of PUnit ⟶ TopCat.of Prop :=
  TopCat.ofHom ⟨fun _ ↦ False, continuous_const⟩

/-- The unique map from the empty space to Sierpiński space. -/
private abbrev emptyMap : TopCat.of Empty ⟶ TopCat.of Prop :=
  TopCat.ofHom ⟨Empty.elim, continuous_of_discreteTopology⟩

private theorem spectral_of_finite {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Finite X] {map : X → Y} (hmap : Continuous map) :
    IsSpectralMap map :=
  ⟨hmap, fun _ _ _ ↦ (Set.toFinite _).isCompact⟩

private theorem isClosed_false : IsClosed ({False} : Set Prop) := by
  have heq : ({False} : Set Prop) = ({True} : Set Prop)ᶜ := by
    ext value
    by_cases hvalue : value <;> simp [hvalue]
  rw [heq]
  exact isOpen_singleton_true.isClosed_compl

private theorem closedPoint_isClosedMap : IsClosedMap closedPoint := by
  intro subset _
  by_cases hsubset : subset.Nonempty
  · change IsClosed ((fun _ : PUnit ↦ False) '' subset)
    simpa only [hsubset.image_const] using isClosed_false
  · simp [Set.not_nonempty_iff_eq_empty.mp hsubset]

private theorem emptyMap_isClosedMap : IsClosedMap emptyMap := by
  intro subset _
  have : subset = ∅ := Set.eq_empty_of_subset_empty (fun x _ ↦ x.elim)
  simp [this]

/-- The compatible two-stage family of collapse maps. -/
private abbrev collapseNat : sierpinski ⟶ singleton :=
  (Functor.const (Fin 2)).map collapse

/-- The compatible two-stage family of closed-point maps. -/
private abbrev closedPointNat : singleton ⟶ sierpinski :=
  (Functor.const (Fin 2)).map closedPoint

/-- The compatible two-stage family of maps from the empty space. -/
private abbrev emptyNat : empty ⟶ sierpinski :=
  (Functor.const (Fin 2)).map emptyMap

/-- The compatible family of first-factor projections. -/
private abbrev firstNat : square ⟶ pair :=
  (Functor.const (Fin 2)).map first

private theorem index_cofiltered : IsCofiltered (Fin 2) := inferInstance

example : IsCofiltered (Fin 2) := index_cofiltered

private theorem stages_spectral : ∀ j, SpectralSpace (sierpinski.obj j) := by
  intro _
  change SpectralSpace Prop
  exact inferInstance

private theorem singleton_stages_spectral : ∀ j, SpectralSpace (singleton.obj j) := by
  intro _
  change SpectralSpace PUnit
  exact inferInstance

private theorem empty_stages_spectral : ∀ j, SpectralSpace (empty.obj j) := by
  intro _
  change SpectralSpace Empty
  exact inferInstance

private theorem square_stages_spectral : ∀ index, SpectralSpace (square.obj index) := by
  intro _
  change SpectralSpace (Fin 2 × Fin 2)
  exact inferInstance

private theorem pair_stages_spectral : ∀ index, SpectralSpace (pair.obj index) := by
  intro _
  change SpectralSpace (Fin 2)
  exact inferInstance

private theorem sierpinski_maps_spectral :
    ∀ {i j : Fin 2} (arrow : i ⟶ j), IsSpectralMap (sierpinski.map arrow) := by
  intro _ _ _
  exact isSpectralMap_id

private theorem singleton_maps_spectral :
    ∀ {i j : Fin 2} (arrow : i ⟶ j), IsSpectralMap (singleton.map arrow) := by
  intro _ _ _
  exact isSpectralMap_id

private theorem empty_maps_spectral :
    ∀ {i j : Fin 2} (arrow : i ⟶ j), IsSpectralMap (empty.map arrow) := by
  intro _ _ _
  exact isSpectralMap_id

private theorem square_maps_spectral :
    ∀ {source target : Fin 2} (arrow : source ⟶ target),
      IsSpectralMap (square.map arrow) := by
  intro _ _ _
  exact isSpectralMap_id

private theorem pair_maps_spectral :
    ∀ {source target : Fin 2} (arrow : source ⟶ target),
      IsSpectralMap (pair.map arrow) := by
  intro _ _ _
  exact isSpectralMap_id

private theorem first_spectral : ∀ index, IsSpectralMap (firstNat.app index) := by
  intro _
  change IsSpectralMap (Prod.fst : Fin 2 × Fin 2 → Fin 2)
  exact spectral_of_finite continuous_fst

private theorem first_surjective : ∀ index, Function.Surjective (firstNat.app index) := by
  intro _
  change Function.Surjective (Prod.fst : Fin 2 × Fin 2 → Fin 2)
  intro value
  exact ⟨(value, 0), rfl⟩

private theorem collapse_spectral : ∀ j, IsSpectralMap (collapseNat.app j) := by
  intro _
  change IsSpectralMap (fun (_ : Prop) ↦ PUnit.unit)
  exact spectral_of_finite continuous_const

private theorem closedPoint_spectral : ∀ j, IsSpectralMap (closedPointNat.app j) := by
  intro _
  change IsSpectralMap (fun (_ : PUnit) ↦ False)
  exact spectral_of_finite continuous_const

private theorem empty_spectral : ∀ j, IsSpectralMap (emptyNat.app j) := by
  intro _
  change IsSpectralMap (Empty.elim : Empty → Prop)
  exact spectral_of_finite continuous_of_discreteTopology

private theorem collapse_surjective : ∀ j, Function.Surjective (collapseNat.app j) := by
  intro _
  change Function.Surjective (fun (_ : Prop) ↦ PUnit.unit)
  intro _
  exact ⟨True, Subsingleton.elim _ _⟩

private theorem closedPoint_not_surjective :
    ¬ Function.Surjective (closedPointNat.app (0 : Fin 2)) := by
  intro h
  obtain ⟨_, contradiction⟩ := h True
  exact Eq.mpr contradiction True.intro

/-- The constant compatible point in the Sierpiński limit. -/
private abbrev propPoint (value : Prop) :
    (TopCat.limitCone ((Functor.const (Fin 2)).obj (TopCat.of Prop))).pt :=
  ⟨fun _ ↦ value, by intro _ _ _; rfl⟩

private theorem propPoint_true_ne_false : propPoint True ≠ propPoint False := by
  intro h
  have hstage := congrArg (fun x ↦ x.1 (0 : Fin 2)) h
  exact Eq.mp hstage True.intro

/-- A compatible constant point in the discrete two-point limit. -/
private abbrev pairPoint (value : Fin 2) :
    (TopCat.limitCone ((Functor.const (Fin 2)).obj (TopCat.of (Fin 2)))).pt :=
  ⟨fun _ ↦ value, by intro _ _ _; rfl⟩

/-- A compatible constant point in the discrete product limit. -/
private abbrev squarePoint (value : Fin 2) :
    (TopCat.limitCone ((Functor.const (Fin 2)).obj (TopCat.of (Fin 2 × Fin 2)))).pt :=
  ⟨fun _ ↦ (value, 0), by intro _ _ _; rfl⟩

private theorem pairPoint_zero_ne_one : pairPoint 0 ≠ pairPoint 1 := by
  intro heq
  have hstage := congrArg (fun point ↦ point.1 (0 : Fin 2)) heq
  exact Fin.zero_ne_one hstage

example : IsSpectralMap
    ((TopCat.limitConeIsLimit pair).map (TopCat.limitCone square) firstNat) := by
  have hprojection_injective :
      Function.Injective (fun point : (TopCat.limitCone square).pt ↦
        point.1 (0 : Fin 2)) := by
    intro point other heq
    apply Subtype.ext
    funext index
    calc
      point.1 index = point.1 0 :=
        (point.2 (homOfLE (by simp : (0 : Fin 2) ≤ index))).symm
      _ = other.1 0 := heq
      _ = other.1 index :=
        other.2 (homOfLE (by simp : (0 : Fin 2) ≤ index))
  have hfinite : Finite (TopCat.limitCone square).pt := by
    have hstage : Finite (square.obj (0 : Fin 2)) := by
      change Finite (Fin 2 × Fin 2)
      infer_instance
    exact @Finite.of_injective _ _ hstage _ hprojection_injective
  exact @spectral_of_finite _ _ _ _ hfinite _
    ((TopCat.limitConeIsLimit pair).map (TopCat.limitCone square) firstNat).hom.continuous

example : Function.Surjective
    ((TopCat.limitConeIsLimit pair).map (TopCat.limitCone square) firstNat) := by
  intro target
  let value : Fin 2 := target.1 (0 : Fin 2)
  have hconstant : ∀ index : Fin 2, target.1 index = value := by
    intro index
    exact (target.2 (homOfLE (by simp : (0 : Fin 2) ≤ index))).symm
  refine ⟨squarePoint value, ?_⟩
  apply Subtype.ext
  funext index
  have hprojection := congrArg (fun map ↦ map (squarePoint value))
    (IsLimit.map_π (TopCat.limitCone square)
      (TopCat.limitConeIsLimit pair) firstNat index)
  exact hprojection.trans (hconstant index).symm

example (arrow : (0 : Fin 2) ⟶ (1 : Fin 2)) (point : Fin 2 × Fin 2) :
    first (square.map arrow point) = pair.map arrow (first point) := by
  rfl

example : pairPoint 0 ≠ pairPoint 1 := pairPoint_zero_ne_one

example : ¬ Function.Injective
    ((TopCat.limitConeIsLimit singleton).map (TopCat.limitCone sierpinski)
      collapseNat) := by
  intro hinjective
  have hpoints :
      (TopCat.limitConeIsLimit singleton).map (TopCat.limitCone sierpinski)
          collapseNat (propPoint True) =
        (TopCat.limitConeIsLimit singleton).map (TopCat.limitCone sierpinski)
          collapseNat (propPoint False) := by
    apply Subtype.ext
    funext j
    exact Subsingleton.elim (α := PUnit) _ _
  exact propPoint_true_ne_false (hinjective hpoints)

/-- The Sierpiński space is not Hausdorff. -/
theorem sierpinski_not_t2 : ¬ T2Space Prop := by
  intro hhausdorff
  have hspecializes : (True : Prop) ⤳ False :=
    (specializes_iff_nhds).2 (by rw [nhds_false]; exact le_top)
  have heq : (True : Prop) = False :=
    t1Space_iff_specializes_imp_eq.mp (@T2Space.t1Space Prop _ hhausdorff)
      hspecializes
  exact Eq.mp heq True.intro

example (x : (TopCat.limitCone sierpinski).pt) (j : Fin 2) :
    ((TopCat.limitConeIsLimit singleton).map (TopCat.limitCone sierpinski)
        collapseNat x).1 j = collapse (x.1 j) := by
  exact congrArg (fun map ↦ map x)
    (IsLimit.map_π (TopCat.limitCone sierpinski)
      (TopCat.limitConeIsLimit singleton) collapseNat j)

example : ¬ Function.Surjective
    ((TopCat.limitConeIsLimit sierpinski).map (TopCat.limitCone singleton)
      closedPointNat) := by
  intro h
  obtain ⟨x, hx⟩ := h (propPoint True)
  have hstage := congrArg (fun y ↦ y.1 (0 : Fin 2)) hx
  have hprojection := congrArg (fun map ↦ map x)
    (IsLimit.map_π (TopCat.limitCone singleton)
      (TopCat.limitConeIsLimit sierpinski) closedPointNat (0 : Fin 2))
  exact Eq.mpr (hprojection.symm.trans hstage) True.intro

private theorem closedPointNat_map_eq (point : (TopCat.limitCone singleton).pt) :
    (TopCat.limitConeIsLimit sierpinski).map (TopCat.limitCone singleton)
      closedPointNat point = propPoint False := by
  apply Subtype.ext
  funext index
  have hprojection := congrArg (fun map ↦ map point)
    (IsLimit.map_π (TopCat.limitCone singleton)
      (TopCat.limitConeIsLimit sierpinski) closedPointNat index)
  exact hprojection.trans (by rfl)

private theorem propPoint_false_isClosed :
    IsClosed ({propPoint False} : Set (TopCat.limitCone sierpinski).pt) := by
  have hclosed : IsClosed (⋂ index : Fin 2,
      (fun point : (TopCat.limitCone sierpinski).pt ↦ point.1 index) ⁻¹'
        ({False} : Set Prop)) := by
    apply isClosed_iInter
    intro index
    exact isClosed_false.preimage
      ((TopCat.limitCone sierpinski).π.app index).hom.continuous
  have heq : (⋂ index : Fin 2,
      (fun point : (TopCat.limitCone sierpinski).pt ↦ point.1 index) ⁻¹'
        ({False} : Set Prop)) = {propPoint False} := by
    ext point
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hpoint
      apply Subtype.ext
      funext index
      exact hpoint index
    · intro hpoint
      subst point
      intro index
      rfl
  rwa [heq] at hclosed

example : IsClosedMap
    ((TopCat.limitConeIsLimit sierpinski).map (TopCat.limitCone singleton)
      closedPointNat) := by
  intro subset _
  have hconstant :
      (((TopCat.limitConeIsLimit sierpinski).map
        (TopCat.limitCone singleton) closedPointNat) :
          (TopCat.limitCone singleton).pt → (TopCat.limitCone sierpinski).pt) =
        fun _ ↦ propPoint False := by
    funext point
    exact closedPointNat_map_eq point
  rw [hconstant]
  by_cases hsubset : subset.Nonempty
  · simpa only [hsubset.image_const] using propPoint_false_isClosed
  · simp [Set.not_nonempty_iff_eq_empty.mp hsubset]

example (arrow : (0 : Fin 2) ⟶ (1 : Fin 2)) (point : Prop) :
    collapse (sierpinski.map arrow point) =
      singleton.map arrow (collapse point) := by
  rfl

example : Nonempty ((0 : Fin 2) ⟶ (1 : Fin 2)) :=
  ⟨homOfLE (by decide)⟩

example : IsClosedMap closedPoint := closedPoint_isClosedMap

example : ∀ j, IsClosedMap (closedPointNat.app j) := by
  intro _
  exact closedPoint_isClosedMap

example : SpectralSpace Empty := inferInstance

example : ¬ Function.Surjective emptyMap := by
  intro h
  obtain ⟨x, _⟩ := h True
  exact x.elim

example : IsClosedMap emptyMap := emptyMap_isClosedMap

example : ¬ Function.Surjective
    ((TopCat.limitConeIsLimit sierpinski).map (TopCat.limitCone empty) emptyNat) := by
  intro hsurj
  obtain ⟨point, _⟩ := hsurj (propPoint True)
  exact (point.1 (0 : Fin 2)).elim

example : IsSpectralMap
    ((TopCat.limitConeIsLimit pair).map (TopCat.limitCone square) firstNat) :=
  SpectralStoneDuality.isSpectralMap_isLimit_map firstNat
    (TopCat.limitCone square) (TopCat.limitCone pair)
    (TopCat.limitConeIsLimit square) (TopCat.limitConeIsLimit pair)
    square_stages_spectral pair_stages_spectral
    square_maps_spectral pair_maps_spectral first_spectral

example : Function.Surjective
    ((TopCat.limitConeIsLimit pair).map (TopCat.limitCone square) firstNat) :=
  SpectralStoneDuality.surjective_isLimit_map firstNat
    (TopCat.limitCone square) (TopCat.limitCone pair)
    (TopCat.limitConeIsLimit square) (TopCat.limitConeIsLimit pair)
    square_stages_spectral pair_stages_spectral
    square_maps_spectral first_spectral first_surjective

example : IsClosedMap
    ((TopCat.limitConeIsLimit sierpinski).map (TopCat.limitCone singleton)
      closedPointNat) :=
  SpectralStoneDuality.isClosedMap_isLimit_map closedPointNat
    (TopCat.limitCone singleton) (TopCat.limitCone sierpinski)
    (TopCat.limitConeIsLimit singleton) (TopCat.limitConeIsLimit sierpinski)
    singleton_stages_spectral stages_spectral
    singleton_maps_spectral closedPoint_spectral
    (fun _ ↦ closedPoint_isClosedMap)

end SpectralStoneDualityExamples.LimitMaps
