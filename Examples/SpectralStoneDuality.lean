/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import SpectralStoneDuality

/-!
# Using spectral Stone duality

These stable named private clients use only the aggregate public import. They
are a separate default build target, not additional library API. They exercise
the advertised structures and maps without opening private implementations.
-/

open CategoryTheory Order Set TopologicalSpace Topology SpectralStoneDuality
open SpectralStoneDuality.PrimeIdealSpectrum

universe u v

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
