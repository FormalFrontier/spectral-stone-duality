/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality

/-!
# Using spectral Stone duality

These named clients use only the aggregate public import. The natural-number
cylinder refinement theorem is public; the other clients are private. This
separate default build target is not part of the core library aggregate. The
clients exercise the advertised structures and maps without opening private
implementations.
-/

open CategoryTheory CategoryTheory.Limits Order Set TopologicalSpace Topology
  SpectralStoneDuality Opposite
open SpectralStoneDuality.PrimeIdealSpectrum

universe u v w

namespace SpectralStoneDualityExamples

variable {A : Type u} [DistribLattice A] [BoundedOrder A]

private theorem spectrumIsSpectral : SpectralSpace (PrimeIdealSpectrum A) :=
  inferInstance

private noncomputable def spectrumPoints :
    PrimeIdealSpectrum A ≃ₜ Locale.PT (Order.Ideal A) := pointHomeomorph

private noncomputable def allOpens :
    Order.Ideal A ≃o Opens (PrimeIdealSpectrum A) := idealOpenOrderIso

private theorem compactBasicOpen (I : Order.Ideal A) :
    IsCompact (basicOpen I) ↔ ∃ a, I = Order.Ideal.principal a :=
  isCompact_basicOpen_iff I

private theorem specialization (P Q : PrimeIdealSpectrum A) :
    P ⤳ Q ↔ P.1 ≤ Q.1 := specializes_iff_ideal_le P Q

-- Recover a compact open from its corresponding lattice element.
private theorem recoverCompactOpen (U : CompactOpens (PrimeIdealSpectrum A)) :
    compactOpenOrderIso ((compactOpenOrderIso (A := A)).symm U) = U :=
  OrderIso.apply_symm_apply _ U

private theorem spectrumIdentity :
    spectrumComap (BoundedLatticeHom.id A) = id := spectrumComap_id

private theorem spectralPullback {B : Type v} [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) : IsSpectralMap (spectrumComap f) :=
  isSpectralMap_spectrumComap f

private theorem basicOpenPullback {B : Type v} [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) (a : A) :
    spectrumComap f ⁻¹' basicOpen (Order.Ideal.principal a) =
      basicOpen (Order.Ideal.principal (f a)) :=
  spectrumComap_preimage_basicOpen_principal f a

private noncomputable def duality : BddDistLatᵒᵖ ≌ SpectralCat := stoneDuality

private noncomputable def reconstructedSpace (X : SpectralCat) :
    X ≃ₜ PrimeIdealSpectrum (CompactOpens X) := spaceSpectrumHomeomorph X

private noncomputable def naturalReconstruction :
    𝟭 SpectralCat ≅ compactOpenFunctor ⋙ spectrumFunctor := spaceUnitIso

-- Source and target universes are independent in this general topology helper.
private theorem constructibleContinuity {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsSpectralMap f) :
    @Continuous X Y (constructibleTopology X) (constructibleTopology Y) f :=
  SpectralStoneDuality.IsSpectralMap.continuous_constructible hf

section Limits

variable {J : Type v} [SmallCategory J] [IsCofiltered J]
  (F : J ⥤ TopCat.{max v u})
  (hX : ∀ j, SpectralSpace (F.obj j))
  (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f))

include hX hmap

private theorem spectralLimit : SpectralSpace (TopCat.limitCone F).pt :=
  spectralSpace_limit_of_spectral F hX hmap

-- Nonemptiness is separate and needs an objectwise hypothesis.
private theorem nonemptyLimit (hne : ∀ j, Nonempty (F.obj j)) :
    Nonempty (TopCat.limitCone F).pt := nonempty_limit_of_spectral F hX hmap hne

end Limits

section CompactOpenBasis

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
  (D : J ⥤ TopCat.{max v u}) (C : Cone D)
  (hC : IsLimit C)
  (hX : ∀ j, SpectralSpace (D.obj j))
  (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (D.map f))

include hC hX hmap

private theorem specifiedConeBasis :
    Opens.IsBasis (Set.range (compactOpenCylinder D C)) :=
  compactOpenCylinders_isBasis D C hC hX hmap

omit hC in
private theorem chosenConeBasis [HasLimit D] :
    Opens.IsBasis (Set.range (chosenLimitCompactOpenCylinder D)) :=
  chosenLimitCompactOpenCylinders_isBasis D hX hmap

end CompactOpenBasis

section DirectedCompactOpenBasis

/-- Every neighborhood in a natural-number inverse limit of spectral spaces contains a
compact-open cylinder around the given point. -/
public theorem natRefinement (D : Natᵒᵖ ⥤ TopCat.{0}) [HasLimit D]
    (hX : ∀ i : Nat, SpectralSpace (D.obj (op i)))
    (hmap : ∀ {a b : Natᵒᵖ} (f : a ⟶ b), IsSpectralMap (D.map f))
    (W : Opens ((limit D : TopCat.{0}))) (x : (limit D : TopCat.{0})) (hx : x ∈ W) :
    ∃ (i : Nat) (U : Opens (D.obj (op i))), IsCompact (U : Set (D.obj (op i))) ∧
      x ∈ (Opens.map (limit.π D (op i))).obj U ∧
        (Opens.map (limit.π D (op i))).obj U ≤ W := by
  obtain ⟨_, ⟨k, rfl⟩, hxU, hUW⟩ :=
    Opens.isBasis_iff_nbhd.mp (directedCompactOpenCylinders_isBasis D hX hmap) hx
  change Σ i : Nat, {U : Opens (D.obj (op i)) // IsCompact (U : Set (D.obj (op i)))} at k
  rcases k with ⟨i, ⟨U, hUc⟩⟩
  exact ⟨i, U, hUc, hxU, hUW⟩

private def emptyNatDiagram : Natᵒᵖ ⥤ TopCat.{0} :=
  (Functor.const Natᵒᵖ).obj (TopCat.of Empty)

private instance emptySpectral : SpectralSpace Empty where

private theorem emptyNatBasis :
    Opens.IsBasis (Set.range (directedCompactOpenCylinder emptyNatDiagram)) := by
  apply directedCompactOpenCylinders_isBasis emptyNatDiagram
  · intro _
    change SpectralSpace Empty
    infer_instance
  · intro a b f
    change IsSpectralMap (id : Empty → Empty)
    exact isSpectralMap_id

private theorem emptyNatNoPoints (x : (limit emptyNatDiagram : TopCat.{0})) : False :=
  Empty.elim ((limit.π emptyNatDiagram (op 0)) x)

end DirectedCompactOpenBasis

-- No closedness or compactness of the subspace itself is assumed.
private theorem liftSubspaceCompactOpen {X : Type u} [TopologicalSpace X]
    [PrespectralSpace X] {Y : Set X} {V : Set Y}
    (hVo : IsOpen V) (hVc : IsCompact V) :
    ∃ U : CompactOpens X, Subtype.val '' V = Y ∩ (U : Set X) :=
  exists_compactOpen_image_eq_inter hVo hVc

private theorem detectSubspaceSpectralMap {X : Type u} [TopologicalSpace X]
    [PrespectralSpace X] {Y : Set X} {Z : Type v} [TopologicalSpace Z]
    (g : Z → Y) (hg : IsSpectralMap ((Subtype.val : Y → X) ∘ g)) :
    IsSpectralMap g := isSpectralMap_to_subtype_of_comp g hg

end SpectralStoneDualityExamples
