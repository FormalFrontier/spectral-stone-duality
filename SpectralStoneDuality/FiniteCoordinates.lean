/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Topology.Finite
public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.Order.LowerUpperTopology
public import Mathlib.Topology.Specialization

/-!
# Finite compact-open coordinates

A finite collection of compact opens determines the realized membership patterns in a product
of Sierpiński spaces. These stages carry the subspace topology, not the quotient topology of
the evaluation map. Compatible patterns form a subspace of the product of all finite stages.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality.FiniteCoordinates

variable {X : Type u} [TopologicalSpace X]

/-- The finite index type of a family of compact opens. -/
abbrev Coordinates (F : Finset (CompactOpens X)) : Type u :=
  {U : CompactOpens X // U ∈ F}

/-- The compact-open membership pattern of a point. -/
def membership (F : Finset (CompactOpens X)) (x : X) : Coordinates F → Prop :=
  fun U => x ∈ (U.1 : Set X)

/-- The realized membership patterns with the subspace topology from the Sierpiński product. -/
def Stage (F : Finset (CompactOpens X)) : Type u :=
  {v : Coordinates F → Prop // ∃ x : X, membership F x = v}

instance instTopologicalSpaceStage (F : Finset (CompactOpens X)) :
    TopologicalSpace (Stage F) :=
  inferInstanceAs (TopologicalSpace
    {v : Coordinates F → Prop // ∃ x : X, membership F x = v})

/-- Send a point to its realized finite membership pattern. -/
def point (F : Finset (CompactOpens X)) (x : X) : Stage F :=
  ⟨membership F x, x, rfl⟩

/-- Two stage points are equal if all of their coordinates agree. -/
@[ext] theorem Stage.ext {F : Finset (CompactOpens X)} {v w : Stage F}
    (h : ∀ U : Coordinates F, (v.1 U ↔ w.1 U)) : v = w := by
  apply Subtype.ext
  funext U
  exact propext (h U)

/-- Membership in a finite compact-open coordinate of a stage. -/
def coordinateOpen (F : Finset (CompactOpens X)) (U : Coordinates F) : Opens (Stage F) :=
  ⟨{v | v.1 U}, continuous_Prop.mp
    ((continuous_apply U).comp continuous_subtype_val)⟩

@[simp] theorem mem_coordinateOpen (F : Finset (CompactOpens X))
    (U : Coordinates F) (v : Stage F) : v ∈ coordinateOpen F U ↔ v.1 U :=
  Iff.rfl

@[simp] theorem point_coordinate (F : Finset (CompactOpens X))
    (U : Coordinates F) (x : X) : (point F x).1 U ↔ x ∈ (U.1 : Set X) :=
  Iff.rfl

@[simp] theorem point_preimage_coordinateOpen (F : Finset (CompactOpens X))
    (U : Coordinates F) : point F ⁻¹' (coordinateOpen F U : Set (Stage F)) =
      (U.1 : Set X) := by
  ext x
  change (point F x).1 U ↔ x ∈ (U.1 : Set X)
  exact point_coordinate F U x

/-- Finite coordinate evaluation is continuous even without separation or compactness. -/
theorem continuous_point (F : Finset (CompactOpens X)) : Continuous (point F (X := X)) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun U => continuous_Prop.mpr U.1.isOpen

/-- Every stage point is realized, even when the stage is empty. -/
theorem surjective_point (F : Finset (CompactOpens X)) :
    Function.Surjective (point F (X := X)) := by
  intro v
  obtain ⟨x, hx⟩ := v.2
  exact ⟨x, Subtype.ext hx⟩

instance instFiniteStage (F : Finset (CompactOpens X)) : Finite (Stage F) :=
  inferInstanceAs (Finite {v : Coordinates F → Prop // ∃ x : X, membership F x = v})

instance instT0Stage (F : Finset (CompactOpens X)) : T0Space (Stage F) :=
  inferInstanceAs (T0Space
    {v : Coordinates F → Prop // ∃ x : X, membership F x = v})

instance instSpectralStage (F : Finset (CompactOpens X)) : SpectralSpace (Stage F) :=
  inferInstance

private theorem specializes_Prop_iff (p q : Prop) : p ⤳ q ↔ (q → p) := by
  by_cases hq : q
  · have hq_eq : q = True := propext ⟨fun _ => True.intro, fun _ => hq⟩
    subst q
    constructor
    · intro h
      have hp : p ∈ ({True} : Set Prop) :=
        h.mem_open isOpen_singleton_true (by simp)
      intro _
      simpa using hp
    · intro hp
      have hp_eq : p = True := propext ⟨fun _ => True.intro, fun _ => hp True.intro⟩
      subst p
      exact specializes_rfl
  · have hq_eq : q = False := propext ⟨hq.elim, False.elim⟩
    subst q
    constructor
    · intro _ hf
      exact hf.elim
    · intro _
      exact specializes_iff_nhds.mpr (by rw [nhds_false]; exact le_top)

/-- Specialization reverses inclusion of the positive coordinate patterns. -/
theorem specializes_iff (F : Finset (CompactOpens X)) (v w : Stage F) :
    v ⤳ w ↔ ∀ U : Coordinates F, w.1 U → v.1 U := by
  have h : v ⤳ w ↔ (v.1 : Coordinates F → Prop) ⤳ w.1 :=
    subtype_specializes_iff v w
  rw [h, specializes_pi]
  simp only [specializes_Prop_iff]

/-- Forget coordinates along an inclusion of finite families. -/
def restrict {F G : Finset (CompactOpens X)} (hFG : F ⊆ G) : Stage G → Stage F :=
  fun v => ⟨fun U => v.1 ⟨U.1, hFG U.2⟩, by
    obtain ⟨x, hx⟩ := v.2
    refine ⟨x, ?_⟩
    funext U
    exact congrFun hx ⟨U.1, hFG U.2⟩⟩

@[simp] theorem restrict_coordinate {F G : Finset (CompactOpens X)} (hFG : F ⊆ G)
    (v : Stage G) (U : Coordinates F) :
    (restrict hFG v).1 U ↔ v.1 ⟨U.1, hFG U.2⟩ := Iff.rfl

/-- Pulling a coordinate open back along a refinement recovers that coordinate open. -/
@[simp] theorem restrict_preimage_coordinateOpen {F G : Finset (CompactOpens X)}
    (hFG : F ⊆ G) (U : Coordinates F) :
    restrict (X := X) hFG ⁻¹' (coordinateOpen F U : Set (Stage F)) =
      (coordinateOpen G ⟨U.1, hFG U.2⟩ : Set (Stage G)) := by
  ext v
  change (restrict hFG v).1 U ↔ v.1 ⟨U.1, hFG U.2⟩
  exact restrict_coordinate hFG v U

/-- Forgetting coordinates is continuous. -/
theorem continuous_restrict {F G : Finset (CompactOpens X)} (hFG : F ⊆ G) :
    Continuous (restrict (X := X) hFG) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun U => ?_
  exact (continuous_apply (⟨U.1, hFG U.2⟩ : Coordinates G)).comp
    (continuous_subtype_val : Continuous (fun v : Stage G => v.1))

/-- A realized coarse pattern extends to a realized finer pattern. -/
theorem surjective_restrict {F G : Finset (CompactOpens X)} (hFG : F ⊆ G) :
    Function.Surjective (restrict (X := X) hFG) := by
  intro v
  obtain ⟨x, rfl⟩ := surjective_point F v
  refine ⟨point G x, ?_⟩
  apply Stage.ext
  intro U
  rfl

@[simp] theorem restrict_point {F G : Finset (CompactOpens X)}
    (hFG : F ⊆ G) (x : X) : restrict hFG (point G x) = point F x := by
  apply Stage.ext
  intro U
  rfl

@[simp] theorem restrict_id (F : Finset (CompactOpens X)) :
    restrict (X := X) (subset_rfl : F ⊆ F) = id := by
  funext v
  apply Stage.ext
  intro U
  rfl

theorem restrict_comp {F G H : Finset (CompactOpens X)}
    (hFG : F ⊆ G) (hGH : G ⊆ H) :
    restrict (X := X) (hFG.trans hGH) = restrict hFG ∘ restrict hGH := by
  funext v
  apply Stage.ext
  intro U
  rfl

/-- Compatible choices of a realized pattern at every finite coordinate stage. -/
def Family (X : Type u) [TopologicalSpace X] : Type u :=
  {z : ∀ F : Finset (CompactOpens X), Stage F //
    ∀ (F G : Finset (CompactOpens X)) (hFG : F ⊆ G),
      restrict (X := X) hFG (z G) = z F}

instance instTopologicalSpaceFamily : TopologicalSpace (Family X) :=
  inferInstanceAs (TopologicalSpace
    {z : ∀ F : Finset (CompactOpens X), Stage F //
      ∀ (F G : Finset (CompactOpens X)) (hFG : F ⊆ G),
        restrict (X := X) hFG (z G) = z F})

@[simp] theorem Family.restrict_apply (z : Family X) (F G : Finset (CompactOpens X))
    (hFG : F ⊆ G) : restrict hFG (z.1 G) = z.1 F :=
  z.2 F G hFG

/-- Compatible families are equal when all of their stage points agree. -/
@[ext] theorem Family.ext {z w : Family X}
    (h : ∀ F : Finset (CompactOpens X), z.1 F = w.1 F) : z = w := by
  apply Subtype.ext
  funext F
  exact h F

/-- Compatible families are equal if all their finite coordinate values agree. -/
theorem Family.ext_coordinate {z w : Family X}
    (h : ∀ (F : Finset (CompactOpens X)) (U : Coordinates F),
      (z.1 F).1 U ↔ (w.1 F).1 U) : z = w := by
  apply Family.ext
  intro F
  exact Stage.ext (h F)

/-- The positive-coordinate cylinder at a finite stage of compatible families. -/
def cylinder (F : Finset (CompactOpens X)) (U : Coordinates F) : Opens (Family X) :=
  ⟨{z | z.1 F ∈ coordinateOpen F U}, (coordinateOpen F U).isOpen.preimage
    ((continuous_apply F).comp continuous_subtype_val)⟩

@[simp] theorem mem_cylinder (F : Finset (CompactOpens X))
    (U : Coordinates F) (z : Family X) : z ∈ cylinder F U ↔ (z.1 F).1 U :=
  Iff.rfl

/-- The compatible family of finite coordinate evaluations of a point. -/
def toFamily (x : X) : Family X :=
  ⟨fun F => point F x, fun _ _ hFG => restrict_point hFG x⟩

@[simp] theorem toFamily_apply (x : X) (F : Finset (CompactOpens X)) :
    (toFamily x).1 F = point F x := rfl

/-- A cylinder pulls back under point evaluation to its compact-open coordinate. -/
@[simp] theorem toFamily_preimage_cylinder (F : Finset (CompactOpens X))
    (U : Coordinates F) : toFamily (X := X) ⁻¹' (cylinder F U : Set (Family X)) =
      (U.1 : Set X) := by
  ext x
  rfl

/-- A singleton-stage cylinder evaluates to its original compact open. -/
@[simp] theorem toFamily_preimage_singleton_cylinder (U : CompactOpens X) :
    toFamily (X := X) ⁻¹'
      (cylinder ({U} : Finset (CompactOpens X))
        ⟨U, Finset.mem_singleton_self U⟩ : Set (Family X)) = (U : Set X) :=
  toFamily_preimage_cylinder _ _

/-- The value of a compatible family at one compact open. -/
def coordinateValue (z : Family X) (U : CompactOpens X) : Prop :=
  (z.1 {U}).1 ⟨U, Finset.mem_singleton_self U⟩

@[simp] theorem coordinateValue_toFamily (x : X) (U : CompactOpens X) :
    coordinateValue (toFamily x) U ↔ x ∈ (U : Set X) :=
  Iff.rfl

/-- A coordinate has the same value at every finite stage containing it. -/
theorem stage_coordinate_iff_coordinateValue (z : Family X)
    (F : Finset (CompactOpens X)) (U : Coordinates F) :
    (z.1 F).1 U ↔ coordinateValue z U.1 := by
  have hUF : ({U.1} : Finset (CompactOpens X)) ⊆ F :=
    Finset.singleton_subset_iff.mpr U.2
  have h := congrArg
    (fun v : Stage ({U.1} : Finset (CompactOpens X)) =>
      v.1 ⟨U.1, Finset.mem_singleton_self U.1⟩)
    (z.2 {U.1} F hUF)
  exact Iff.of_eq h

/-- The point-to-family map is continuous without separation hypotheses. -/
theorem continuous_toFamily : Continuous (toFamily (X := X)) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun F => continuous_point F

/-- The topology on `X` is induced from the topology on compatible families by `toFamily`. -/
theorem inducing_toFamily [PrespectralSpace X] : IsInducing (toFamily (X := X)) := by
  refine ⟨le_antisymm continuous_toFamily.le_induced ?_⟩
  rw [TopologicalSpace.le_def]
  intro s hs
  refine PrespectralSpace.isTopologicalBasis.isOpen_induction
    (P := fun t => IsOpen[TopologicalSpace.induced (toFamily (X := X)) inferInstance] t)
    ?_ ?_ hs
  · intro U hU
    let K : CompactOpens X := ⟨⟨U, hU.2⟩, hU.1⟩
    change IsOpen[TopologicalSpace.induced (toFamily (X := X)) inferInstance] (K : Set X)
    rw [← toFamily_preimage_singleton_cylinder K]
    exact isOpen_induced (cylinder ({K} : Finset (CompactOpens X))
      ⟨K, Finset.mem_singleton_self K⟩).isOpen
  · intro S hS
    exact @isOpen_sUnion X (TopologicalSpace.induced (toFamily (X := X)) inferInstance) S hS

/-- Under T₀ and a compact-open basis, compatible coordinates separate points. -/
theorem injective_toFamily [PrespectralSpace X] [T0Space X] :
    Function.Injective (toFamily (X := X)) := by
  exact inducing_toFamily.injective

private theorem coordinateValue_iff_mem_of_realizes (z : Family X)
    (F : Finset (CompactOpens X)) (x : X) (hx : membership F x = (z.1 F).1)
    (U : Coordinates F) : coordinateValue z U.1 ↔ x ∈ (U.1 : Set X) :=
  (stage_coordinate_iff_coordinateValue z F U).symm.trans
    (Iff.of_eq (congrFun hx U)).symm

/-- Finite-stage realization makes singleton coordinates preserve intersections. -/
theorem coordinateValue_inf [QuasiSeparatedSpace X] (z : Family X)
    (K L : CompactOpens X) :
    coordinateValue z (K ⊓ L) ↔ coordinateValue z K ∧ coordinateValue z L := by
  classical
  let F : Finset (CompactOpens X) := {K, L, K ⊓ L}
  obtain ⟨x, hx⟩ := (z.1 F).2
  have hval (U : CompactOpens X) (hUF : U ∈ F) :
      coordinateValue z U ↔ x ∈ (U : Set X) :=
    coordinateValue_iff_mem_of_realizes z F x hx ⟨U, hUF⟩
  rw [hval (K ⊓ L) (by simp [F]), hval K (by simp [F]), hval L (by simp [F])]
  rfl

/-- Every compatible family assigns true to the whole compact open. -/
theorem coordinateValue_top [CompactSpace X] (z : Family X) :
    coordinateValue z (⊤ : CompactOpens X) := by
  obtain ⟨x, hx⟩ := (z.1 ({⊤} : Finset (CompactOpens X))).2
  exact (coordinateValue_iff_mem_of_realizes z {⊤} x hx
    ⟨⊤, Finset.mem_singleton_self _⟩).mpr (by simp)

private theorem exists_realizing_avoiding (z : Family X) (K : CompactOpens X)
    (hK : coordinateValue z K)
    (s : Finset {U : CompactOpens X // ¬ coordinateValue z U}) :
    ∃ x : X, x ∈ (K : Set X) ∧ ∀ U ∈ s, x ∉ (U.1 : Set X) := by
  classical
  let F : Finset (CompactOpens X) := insert K (s.image Subtype.val)
  obtain ⟨x, hx⟩ := (z.1 F).2
  have hval (U : CompactOpens X) (hUF : U ∈ F) :
      coordinateValue z U ↔ x ∈ (U : Set X) :=
    coordinateValue_iff_mem_of_realizes z F x hx ⟨U, hUF⟩
  refine ⟨x, (hval K (Finset.mem_insert_self K _)).mp hK, ?_⟩
  intro U hUs hxU
  exact U.2 ((hval U.1 (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem Subtype.val hUs))).mpr hxU)

/-- Under `CompactSpace`, `QuasiSeparatedSpace`, `PrespectralSpace` (a compact-open basis)
and `QuasiSober`, every compatible family is realized without a `T0Space` assumption. -/
theorem surjective_toFamily [CompactSpace X] [QuasiSeparatedSpace X]
    [PrespectralSpace X] [QuasiSober X] :
    Function.Surjective (toFamily (X := X)) := by
  intro z
  let C : Set X := ⋂ U : {U : CompactOpens X // ¬ coordinateValue z U},
    ((U.1 : Set X))ᶜ
  have hC (x : X) : x ∈ C ↔
      ∀ U : CompactOpens X, ¬ coordinateValue z U → x ∉ (U : Set X) := by
    simp only [C, Set.mem_iInter, Set.mem_compl_iff]
    exact ⟨fun h U hU => h ⟨U, hU⟩, fun h U => h U.1 U.2⟩
  have hmeet (K : CompactOpens X) (hK : coordinateValue z K) :
      ((K : Set X) ∩ C).Nonempty := by
    refine K.isCompact.inter_iInter_nonempty
      (fun U : {U : CompactOpens X // ¬ coordinateValue z U} => ((U.1 : Set X))ᶜ)
      (fun U => U.1.isOpen.isClosed_compl) (fun s => ?_)
    obtain ⟨x, hxK, hxAvoid⟩ := exists_realizing_avoiding z K hK s
    refine ⟨x, hxK, ?_⟩
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    exact hxAvoid
  have hCnonempty : C.Nonempty := by
    obtain ⟨x, _, hxC⟩ := hmeet ⊤ (coordinateValue_top z)
    exact ⟨x, hxC⟩
  have hclosed : IsClosed C := isClosed_iInter fun U => U.1.isOpen.isClosed_compl
  have hvalue (K : CompactOpens X) :
      coordinateValue z K ↔ (C ∩ (K : Set X)).Nonempty := by
    constructor
    · intro hK
      simpa only [Set.inter_comm] using hmeet K hK
    · rintro ⟨x, hxC, hxK⟩
      by_contra hnK
      exact (hC x).mp hxC K hnK hxK
  have hirreducible : IsIrreducible C := by
    refine ⟨hCnonempty, ?_⟩
    intro U V hUOpen hVOpen hCU hCV
    obtain ⟨x, hxC, hxU⟩ := hCU
    obtain ⟨y, hyC, hyV⟩ := hCV
    obtain ⟨KU, ⟨hKUOpen, hKUCompact⟩, hxKU, hKUU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxU hUOpen
    obtain ⟨KV, ⟨hKVOpen, hKVCompact⟩, hyKV, hKVV⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyV hVOpen
    let K : CompactOpens X := ⟨⟨KU, hKUCompact⟩, hKUOpen⟩
    let L : CompactOpens X := ⟨⟨KV, hKVCompact⟩, hKVOpen⟩
    have hK : coordinateValue z K := (hvalue K).mpr ⟨x, hxC, hxKU⟩
    have hL : coordinateValue z L := (hvalue L).mpr ⟨y, hyC, hyKV⟩
    obtain ⟨w, hwKL, hwC⟩ :=
      hmeet (K ⊓ L) ((coordinateValue_inf z K L).mpr ⟨hK, hL⟩)
    change w ∈ (K : Set X) ∩ (L : Set X) at hwKL
    exact ⟨w, hwC, hKUU hwKL.1, hKVV hwKL.2⟩
  refine ⟨hirreducible.genericPoint, ?_⟩
  apply Family.ext_coordinate
  intro F U
  change hirreducible.genericPoint ∈ (U.1 : Set X) ↔ (z.1 F).1 U
  exact ((hirreducible.isGenericPoint_genericPoint hclosed).mem_open_set_iff
    U.1.isOpen).trans ((hvalue U.1).symm.trans
      (stage_coordinate_iff_coordinateValue z F U).symm)

/-- A spectral space is homeomorphic to its compatible finite compact-open patterns. -/
noncomputable def spaceHomeomorph (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] : X ≃ₜ Family X := by
  exact (Equiv.ofBijective (toFamily (X := X))
    ⟨injective_toFamily, surjective_toFamily⟩).toHomeomorphOfIsInducing
      inducing_toFamily

@[simp] theorem spaceHomeomorph_apply (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] (x : X) : spaceHomeomorph X x = toFamily x := by
  rfl

end SpectralStoneDuality.FiniteCoordinates
