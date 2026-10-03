/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Sober

/-!
# Soberification of a topological space

The points of the soberification are Mathlib's nonempty irreducible closed subsets.
An open subset consists of those points meeting a given open subset of the original space.
The unit sends a point to the closure of its singleton.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

universe u v w

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The topology whose open sets consist exactly of the irreducible closed subsets meeting an
open set of the original space. -/
instance instTopologicalSpace (X : Type u) [TopologicalSpace X] :
    TopologicalSpace (IrreducibleCloseds X) where
  IsOpen S := ∃ U : Opens X,
    S = {F : IrreducibleCloseds X | ((F : Set X) ∩ (U : Set X)).Nonempty}
  isOpen_univ := by
    refine ⟨⊤, ?_⟩
    ext F
    simpa only [Opens.coe_top, Set.inter_univ, Set.mem_univ, Set.mem_ofPred_eq, true_iff]
      using F.isIrreducible.nonempty
  isOpen_inter := by
    rintro A B ⟨U, rfl⟩ ⟨V, rfl⟩
    refine ⟨U ⊓ V, ?_⟩
    ext F
    change (((F : Set X) ∩ (U : Set X)).Nonempty ∧
      ((F : Set X) ∩ (V : Set X)).Nonempty) ↔
        ((F : Set X) ∩ ((U ⊓ V : Opens X) : Set X)).Nonempty
    constructor
    · rintro ⟨hU, hV⟩
      exact F.isIrreducible.isPreirreducible _ _ U.isOpen V.isOpen hU hV
    · rintro ⟨x, hxF, hxUV⟩
      exact ⟨⟨x, hxF, hxUV.1⟩, ⟨x, hxF, hxUV.2⟩⟩
  isOpen_sUnion := by
    intro S hS
    choose U hU using (fun s : S => hS s.1 s.2)
    refine ⟨sSup (Set.range U), ?_⟩
    ext F
    change (∃ s ∈ S, F ∈ s) ↔
      ((F : Set X) ∩ (sSup (Set.range U) : Opens X)).Nonempty
    constructor
    · rintro ⟨s, hs, hFs⟩
      obtain ⟨x, hxF, hxU⟩ := (Set.ext_iff.mp (hU ⟨s, hs⟩) F).mp hFs
      exact ⟨x, hxF, Opens.mem_sSup.mpr ⟨U ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩, hxU⟩⟩
    · rintro ⟨x, hxF, hxU⟩
      obtain ⟨_, ⟨s, rfl⟩, hxUs⟩ := Opens.mem_sSup.mp hxU
      exact ⟨s.1, s.2, (Set.ext_iff.mp (hU s) F).mpr ⟨x, hxF, hxUs⟩⟩

/-- The open set of irreducible closed subsets meeting `U`. -/
def openSet (U : Opens X) : Opens (IrreducibleCloseds X) :=
  ⟨{F : IrreducibleCloseds X | ((F : Set X) ∩ (U : Set X)).Nonempty}, ⟨U, rfl⟩⟩

@[simp]
theorem mem_openSet (U : Opens X) (F : IrreducibleCloseds X) :
    F ∈ openSet U ↔ ((F : Set X) ∩ (U : Set X)).Nonempty :=
  Iff.rfl

/-- Every open of the soberification is the set of irreducible closeds meeting an open of `X`. -/
theorem isOpen_iff (S : Set (IrreducibleCloseds X)) :
    IsOpen S ↔ ∃ U : Opens X, S = (openSet U : Set _) := by
  constructor
  · rintro ⟨U, h⟩
    exact ⟨U, h⟩
  · rintro ⟨U, h⟩
    exact ⟨U, h⟩

@[simp]
theorem openSet_bot : openSet (⊥ : Opens X) = ⊥ := by
  ext F
  simp [mem_openSet]

@[simp]
theorem openSet_top : openSet (⊤ : Opens X) = ⊤ := by
  ext F
  simpa [mem_openSet] using F.isIrreducible.nonempty

@[simp]
theorem openSet_inf (U V : Opens X) :
    openSet (U ⊓ V) = openSet U ⊓ openSet V := by
  ext F
  constructor
  · rintro ⟨x, hxF, hxUV⟩
    exact ⟨⟨x, hxF, hxUV.1⟩, ⟨x, hxF, hxUV.2⟩⟩
  · rintro ⟨hU, hV⟩
    exact F.isIrreducible.isPreirreducible _ _ U.isOpen V.isOpen hU hV

theorem openSet_sSup (S : Set (Opens X)) :
    openSet (sSup S) = sSup (openSet '' S) := by
  ext F
  constructor
  · rintro ⟨x, hxF, hxU⟩
    obtain ⟨U, hUS, hxU'⟩ := Opens.mem_sSup.mp hxU
    exact Opens.mem_sSup.mpr ⟨openSet U, ⟨U, hUS, rfl⟩, ⟨x, hxF, hxU'⟩⟩
  · intro hF
    obtain ⟨_, ⟨U, hUS, rfl⟩, ⟨x, hxF, hxU⟩⟩ := Opens.mem_sSup.mp hF
    exact ⟨x, hxF, Opens.mem_sSup.mpr ⟨U, hUS, hxU⟩⟩

/-- The irreducible closed subsets contained in a set. -/
def closedSet (Z : Set X) : Set (IrreducibleCloseds X) :=
  {F | (F : Set X) ⊆ Z}

@[simp]
theorem mem_closedSet (Z : Set X) (F : IrreducibleCloseds X) :
    F ∈ closedSet Z ↔ (F : Set X) ⊆ Z :=
  Iff.rfl

/-- The complement of the irreducible closed subsets contained in a closed set is the open set
of those meeting its complement. -/
theorem compl_closedSet {Z : Set X} (hZ : IsClosed Z) :
    (closedSet Z)ᶜ = (openSet ⟨Zᶜ, hZ.isOpen_compl⟩ : Set _) := by
  ext F
  constructor
  · intro h
    obtain ⟨x, hxF, hxZ⟩ := Set.not_subset_iff_exists_mem_notMem.mp h
    exact ⟨x, hxF, hxZ⟩
  · rintro ⟨x, hxF, hxZ⟩ h
    exact hxZ (h hxF)

theorem isClosed_closedSet {Z : Set X} (hZ : IsClosed Z) :
    IsClosed (closedSet Z) := by
  apply isOpen_compl_iff.mp
  rw [compl_closedSet hZ]
  exact (openSet ⟨Zᶜ, hZ.isOpen_compl⟩).isOpen

/-- Every closed subset of the soberification arises from a closed subset of `X`. -/
theorem isClosed_iff (D : Set (IrreducibleCloseds X)) :
    IsClosed D ↔ ∃ Z : Set X, IsClosed Z ∧ D = closedSet Z := by
  constructor
  · intro hD
    obtain ⟨U, hU⟩ := (isOpen_iff Dᶜ).mp hD.isOpen_compl
    refine ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl, ?_⟩
    apply compl_injective
    rw [hU, compl_closedSet U.isOpen.isClosed_compl]
    ext F
    change ((F : Set X) ∩ (U : Set X)).Nonempty ↔
      ((F : Set X) ∩ (((U : Set X)ᶜ)ᶜ)).Nonempty
    simp only [compl_compl]
  · rintro ⟨Z, hZ, rfl⟩
    exact isClosed_closedSet hZ

theorem closedSet_nonempty_iff {Z : Set X} (hZ : IsClosed Z) :
    (closedSet Z).Nonempty ↔ Z.Nonempty := by
  constructor
  · rintro ⟨F, hF⟩
    exact F.isIrreducible.nonempty.mono hF
  · rintro ⟨x, hx⟩
    refine ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩, ?_⟩
    exact hZ.closure_subset_iff.mpr (singleton_subset_iff.mpr hx)

theorem closedSet_meets_openSet_iff {Z : Set X} (hZ : IsClosed Z) (U : Opens X) :
    (closedSet Z ∩ (openSet U : Set _)).Nonempty ↔
      (Z ∩ (U : Set X)).Nonempty := by
  constructor
  · rintro ⟨F, hFZ, ⟨x, hxF, hxU⟩⟩
    exact ⟨x, hFZ hxF, hxU⟩
  · rintro ⟨x, hxZ, hxU⟩
    refine ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩,
      hZ.closure_subset_iff.mpr (singleton_subset_iff.mpr hxZ), ?_⟩
    exact ⟨x, subset_closure (by simp), hxU⟩

theorem irreducible_closedSet_iff {Z : Set X} (hZ : IsClosed Z) :
    IsIrreducible (closedSet Z) ↔ IsIrreducible Z := by
  constructor
  · intro h
    refine ⟨(closedSet_nonempty_iff hZ).mp h.nonempty, ?_⟩
    intro U V hU hV hZU hZV
    let u : Opens X := ⟨U, hU⟩
    let v : Opens X := ⟨V, hV⟩
    have hDu := (closedSet_meets_openSet_iff hZ u).mpr hZU
    have hDv := (closedSet_meets_openSet_iff hZ v).mpr hZV
    have hDuv := h.isPreirreducible _ _ (openSet u).isOpen (openSet v).isOpen hDu hDv
    have hDuv' : (closedSet Z ∩ (openSet (u ⊓ v) : Set _)).Nonempty := by
      simpa only [openSet_inf, Opens.coe_inf] using hDuv
    exact (closedSet_meets_openSet_iff hZ (u ⊓ v)).mp hDuv'
  · intro h
    refine ⟨(closedSet_nonempty_iff hZ).mpr h.nonempty, ?_⟩
    intro A B hA hB hDA hDB
    obtain ⟨U, hAU⟩ := (isOpen_iff A).mp hA
    obtain ⟨V, hBV⟩ := (isOpen_iff B).mp hB
    rw [hAU] at hDA ⊢
    rw [hBV] at hDB ⊢
    have hZU := (closedSet_meets_openSet_iff hZ U).mp hDA
    have hZV := (closedSet_meets_openSet_iff hZ V).mp hDB
    have hZUV := h.isPreirreducible _ _ U.isOpen V.isOpen hZU hZV
    have hDuv := (closedSet_meets_openSet_iff hZ (U ⊓ V)).mpr hZUV
    simpa only [openSet_inf, Opens.coe_inf] using hDuv

theorem closure_singleton_eq_closedSet (F : IrreducibleCloseds X) :
    closure ({F} : Set (IrreducibleCloseds X)) = closedSet (F : Set X) := by
  apply subset_antisymm
  · apply closure_minimal
    · intro G hG
      change (G : Set X) ⊆ F
      rw [Set.mem_singleton_iff.mp hG]
    · exact isClosed_closedSet F.isClosed
  · intro G hGF
    apply mem_closure_iff.mpr
    intro V hV hGV
    obtain ⟨U, hVU⟩ := (isOpen_iff V).mp hV
    have hGU : G ∈ (openSet U : Set (IrreducibleCloseds X)) := by
      rw [hVU] at hGV
      exact hGV
    obtain ⟨x, hxG, hxU⟩ := hGU
    have hFU : F ∈ (openSet U : Set (IrreducibleCloseds X)) := ⟨x, hGF hxG, hxU⟩
    have hFV : F ∈ V := by rwa [hVU]
    exact ⟨F, hFV, rfl⟩

/-- The unit of soberification takes `x` to the closure of its singleton. -/
def unit (X : Type u) [TopologicalSpace X] : C(X, IrreducibleCloseds X) :=
  ⟨fun x => ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩,
    by
      rw [continuous_def]
      intro S hS
      obtain ⟨U, hU⟩ := (isOpen_iff S).mp hS
      rw [hU]
      convert U.isOpen using 1
      ext x
      change ((closure {x} : Set X) ∩ (U : Set X)).Nonempty ↔ x ∈ U
      exact (isGenericPoint_closure.mem_open_set_iff U.isOpen).symm⟩

@[simp]
theorem coe_unit_apply (x : X) :
    ((unit X x : IrreducibleCloseds X) : Set X) = closure {x} :=
  rfl

@[simp]
theorem unit_preimage_openSet (U : Opens X) :
    (unit X) ⁻¹' (openSet U : Set _) = (U : Set X) := by
  ext x
  change ((closure {x} : Set X) ∩ (U : Set X)).Nonempty ↔ x ∈ U
  exact (isGenericPoint_closure.mem_open_set_iff U.isOpen).symm

theorem unit_preimage_closedSet {Z : Set X} (hZ : IsClosed Z) :
    (unit X) ⁻¹' closedSet Z = Z := by
  ext x
  change closure {x} ⊆ Z ↔ x ∈ Z
  exact (isGenericPoint_closure.mem_closed_set_iff hZ).symm

/-- Opens of `X` and of its soberification correspond via the unit. -/
def opensOrderIso (X : Type u) [TopologicalSpace X] :
    Opens X ≃o Opens (IrreducibleCloseds X) where
  toFun := openSet
  invFun U := ⟨(unit X) ⁻¹' (U : Set _), U.isOpen.preimage (unit X).continuous⟩
  left_inv := by
    intro U
    exact Opens.ext (unit_preimage_openSet U)
  right_inv := by
    intro U
    obtain ⟨V, hV⟩ := (isOpen_iff (U : Set (IrreducibleCloseds X))).mp U.isOpen
    have hUV : U = openSet V := SetLike.coe_injective hV
    subst U
    have hInv : (⟨(unit X) ⁻¹' (openSet V : Set _),
        (openSet V).isOpen.preimage (unit X).continuous⟩ : Opens X) = V :=
      Opens.ext (unit_preimage_openSet V)
    exact congrArg openSet hInv
  map_rel_iff' := by
    intro U V
    constructor
    · intro h
      change (U : Set X) ⊆ V
      simpa only [unit_preimage_openSet] using
        (Set.preimage_mono (f := unit X) (show (openSet U : Set _) ⊆ openSet V from h))
    · intro h F hF
      obtain ⟨x, hxF, hxU⟩ := hF
      exact ⟨x, hxF, h hxU⟩

@[simp]
theorem opensOrderIso_apply (U : Opens X) : opensOrderIso X U = openSet U :=
  rfl

@[simp]
theorem opensOrderIso_symm_apply (U : Opens (IrreducibleCloseds X)) :
    (opensOrderIso X).symm U =
      ⟨(unit X) ⁻¹' (U : Set _), U.isOpen.preimage (unit X).continuous⟩ :=
  rfl

/-- Soberification is `T₀`, whether or not `X` is separated. -/
instance instT0Space (X : Type u) [TopologicalSpace X] :
    T0Space (IrreducibleCloseds X) := by
  apply (t0Space_iff_inseparable _).mpr
  intro F G hFG
  have h : closedSet (F : Set X) = closedSet (G : Set X) := by
    simpa only [closure_singleton_eq_closedSet] using
      (inseparable_iff_closure_eq.mp hFG)
  apply IrreducibleCloseds.ext
  apply subset_antisymm
  · exact (mem_closedSet (G : Set X) F).mp
      ((Set.ext_iff.mp h F).mp ((mem_closedSet (F : Set X) F).mpr Set.Subset.rfl))
  · exact (mem_closedSet (F : Set X) G).mp
      ((Set.ext_iff.mp h G).mpr ((mem_closedSet (G : Set X) G).mpr Set.Subset.rfl))

/-- Every irreducible closed subset of the soberification has a generic point. -/
instance instQuasiSober (X : Type u) [TopologicalSpace X] :
    QuasiSober (IrreducibleCloseds X) := by
  constructor
  intro D hD hDclosed
  obtain ⟨Z, hZ, hDZ⟩ := (isClosed_iff D).mp hDclosed
  have hZirr : IsIrreducible Z := (irreducible_closedSet_iff hZ).mp (hDZ ▸ hD)
  let F : IrreducibleCloseds X := ⟨Z, hZirr, hZ⟩
  refine ⟨F, ?_⟩
  change closure {F} = D
  rw [closure_singleton_eq_closedSet]
  exact hDZ.symm

theorem unit_isInducing (X : Type u) [TopologicalSpace X] :
    Topology.IsInducing (unit X) := by
  constructor
  apply TopologicalSpace.ext_iff.mpr
  intro S
  rw [isOpen_induced_iff]
  constructor
  · intro hS
    exact ⟨openSet ⟨S, hS⟩, (openSet ⟨S, hS⟩).isOpen,
      unit_preimage_openSet ⟨S, hS⟩⟩
  · rintro ⟨V, hV, rfl⟩
    exact hV.preimage (unit X).continuous

theorem unit_eq_iff_inseparable (x x' : X) :
    unit X x = unit X x' ↔ Inseparable x x' := by
  constructor
  · intro h
    exact inseparable_iff_closure_eq.mpr
      (congrArg (fun F : IrreducibleCloseds X => (F : Set X)) h)
  · intro h
    apply IrreducibleCloseds.ext
    exact inseparable_iff_closure_eq.mp h

theorem unit_injective_iff_t0 (X : Type u) [TopologicalSpace X] :
    Function.Injective (unit X) ↔ T0Space X := by
  rw [t0Space_iff_inseparable]
  constructor
  · intro hinj x y hxy
    exact hinj ((unit_eq_iff_inseparable x y).mpr hxy)
  · intro h x y hxy
    exact h x y ((unit_eq_iff_inseparable x y).mp hxy)

theorem unit_isEmbedding_iff_t0 (X : Type u) [TopologicalSpace X] :
    Topology.IsEmbedding (unit X) ↔ T0Space X := by
  rw [Topology.isEmbedding_iff, unit_injective_iff_t0]
  simp only [unit_isInducing, true_and]

theorem closure_range_unit (X : Type u) [TopologicalSpace X] :
    closure (Set.range (unit X)) = Set.univ := by
  apply dense_iff_closure_eq.mp
  apply dense_iff_inter_open.mpr
  intro S hS hSne
  obtain ⟨U, hU⟩ := (isOpen_iff S).mp hS
  have hSne' : (openSet U : Set (IrreducibleCloseds X)).Nonempty := by
    simpa only [hU] using hSne
  obtain ⟨F, hFU⟩ := hSne'
  obtain ⟨x, hxF, hxU⟩ := hFU
  refine ⟨unit X x, ?_, ⟨x, rfl⟩⟩
  rw [hU]
  exact (Set.ext_iff.mp (unit_preimage_openSet U) x).mpr hxU

/-- Maps into a `T₀` space are determined by their values on the unit. -/
theorem continuous_ext_of_comp_unit [T0Space Y]
    {g h : C(IrreducibleCloseds X, Y)}
    (heq : g.comp (unit X) = h.comp (unit X)) : g = h := by
  ext F
  apply Inseparable.eq
  apply inseparable_iff_forall_isOpen.mpr
  intro S hS
  have hpre : (unit X) ⁻¹' (g ⁻¹' S) = (unit X) ⁻¹' (h ⁻¹' S) := by
    ext x
    change g (unit X x) ∈ S ↔ h (unit X x) ∈ S
    have hx := congrArg (fun k : C(X, Y) => k x) heq
    exact hx ▸ Iff.rfl
  obtain ⟨U, hU⟩ := (isOpen_iff (g ⁻¹' S)).mp (hS.preimage g.continuous)
  obtain ⟨V, hV⟩ := (isOpen_iff (h ⁻¹' S)).mp (hS.preimage h.continuous)
  have hUV : U = V := by
    apply SetLike.coe_injective
    calc
      (U : Set X) = (unit X) ⁻¹' (openSet U : Set _) := (unit_preimage_openSet U).symm
      _ = (unit X) ⁻¹' (g ⁻¹' S) := by rw [hU]
      _ = (unit X) ⁻¹' (h ⁻¹' S) := hpre
      _ = (unit X) ⁻¹' (openSet V : Set _) := by rw [hV]
      _ = (V : Set X) := unit_preimage_openSet V
  have hEq : g ⁻¹' S = h ⁻¹' S := by
    calc
      g ⁻¹' S = (openSet U : Set _) := hU
      _ = (openSet V : Set _) := congrArg
        (fun W : Opens X => (openSet W : Set (IrreducibleCloseds X))) hUV
      _ = h ⁻¹' S := hV.symm
  exact Set.ext_iff.mp hEq F

@[simp]
theorem map_mem_openSet_iff (f : C(X, Y)) (F : IrreducibleCloseds X) (V : Opens Y) :
    map f f.continuous F ∈ openSet V ↔
      F ∈ openSet ⟨f ⁻¹' (V : Set Y), V.isOpen.preimage f.continuous⟩ := by
  change (closure (f '' (F : Set X)) ∩ (V : Set Y)).Nonempty ↔
    ((F : Set X) ∩ f ⁻¹' (V : Set Y)).Nonempty
  exact (closure_inter_open_nonempty_iff V.isOpen).trans image_inter_nonempty_iff

theorem continuous_map (f : C(X, Y)) :
    Continuous (map f f.continuous) := by
  rw [continuous_def]
  intro S hS
  obtain ⟨V, hV⟩ := (isOpen_iff S).mp hS
  rw [hV]
  convert (openSet ⟨f ⁻¹' (V : Set Y), V.isOpen.preimage f.continuous⟩).isOpen using 1
  ext F
  exact map_mem_openSet_iff f F V

@[simp]
theorem map_id (F : IrreducibleCloseds X) :
    map id continuous_id F = F := by
  apply IrreducibleCloseds.ext
  simpa only [coe_map, image_id] using F.isClosed.closure_eq

@[simp]
theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) (F : IrreducibleCloseds X) :
    map (g ∘ f) (g.continuous.comp f.continuous) F =
      map g g.continuous (map f f.continuous F) := by
  apply IrreducibleCloseds.ext
  change closure ((g ∘ f) '' (F : Set X)) =
    closure (g '' closure (f '' (F : Set X)))
  rw [Set.image_comp, closure_image_closure g.continuous]

@[simp]
theorem map_unit (f : C(X, Y)) (x : X) :
    map f f.continuous (unit X x) = unit Y (f x) := by
  apply IrreducibleCloseds.ext
  change closure (f '' closure ({x} : Set X)) = closure ({f x} : Set Y)
  rw [closure_image_closure f.continuous, image_singleton]

/-- Extend a map to a sober space by sending each irreducible closed subset to the
generic point of the closure of its image. -/
noncomputable def extend [QuasiSober Y] [T0Space Y] (f : C(X, Y)) :
    C(IrreducibleCloseds X, Y) :=
  ⟨fun F => (map f f.continuous F).isIrreducible.genericPoint, by
    rw [continuous_def]
    intro S hS
    let V : Opens Y := ⟨S, hS⟩
    convert (openSet ⟨f ⁻¹' (V : Set Y), V.isOpen.preimage f.continuous⟩).isOpen using 1
    ext F
    exact (((map f f.continuous F).isIrreducible.isGenericPoint_genericPoint
      (map f f.continuous F).isClosed).mem_open_set_iff V.isOpen).trans
        (map_mem_openSet_iff f F V)⟩

theorem extend_isGenericPoint [QuasiSober Y] [T0Space Y]
    (f : C(X, Y)) (F : IrreducibleCloseds X) :
    IsGenericPoint (extend f F) (map f f.continuous F : Set Y) :=
  (map f f.continuous F).isIrreducible.isGenericPoint_genericPoint
    (map f f.continuous F).isClosed

theorem extend_mem_iff [QuasiSober Y] [T0Space Y]
    (f : C(X, Y)) (F : IrreducibleCloseds X) (V : Opens Y) :
    extend f F ∈ V ↔ ((F : Set X) ∩ f ⁻¹' (V : Set Y)).Nonempty :=
  ((extend_isGenericPoint f F).mem_open_set_iff V.isOpen).trans
    (map_mem_openSet_iff f F V)

@[simp]
theorem extend_comp_unit [QuasiSober Y] [T0Space Y] (f : C(X, Y)) :
    (extend f).comp (unit X) = f := by
  ext x
  have hx : IsGenericPoint (f x) (map f f.continuous (unit X x) : Set Y) := by
    rw [map_unit]
    exact isGenericPoint_closure
  exact (extend_isGenericPoint f (unit X x)).eq hx

theorem extend_unique [QuasiSober Y] [T0Space Y] (f : C(X, Y))
    (h : C(IrreducibleCloseds X, Y)) (heq : h.comp (unit X) = f) :
    h = extend f :=
  continuous_ext_of_comp_unit (heq.trans (extend_comp_unit f).symm)

/-- A sober space is homeomorphic to its soberification via the unit. -/
noncomputable def unitHomeomorph (X : Type u) [TopologicalSpace X]
    [QuasiSober X] [T0Space X] : X ≃ₜ IrreducibleCloseds X := by
  letI : PartialOrder X := specializationOrder X
  exact {
    toEquiv := (irreducibleSetEquivPoints (α := X)).symm.toEquiv
    continuous_toFun := (unit X).continuous
    continuous_invFun := by
      rw [continuous_def]
      intro S hS
      convert (openSet ⟨S, hS⟩).isOpen using 1
      ext F
      change F.isIrreducible.genericPoint ∈ S ↔ ((F : Set X) ∩ S).Nonempty
      exact (F.isIrreducible.isGenericPoint_genericPoint F.isClosed).mem_open_set_iff hS }

@[simp]
theorem unitHomeomorph_apply [QuasiSober X] [T0Space X] (x : X) :
    unitHomeomorph X x = unit X x :=
  rfl

@[simp]
theorem unitHomeomorph_symm_apply [QuasiSober X] [T0Space X]
    (F : IrreducibleCloseds X) :
    (unitHomeomorph X).symm F = F.isIrreducible.genericPoint :=
  rfl

end TopologicalSpace.IrreducibleCloseds
