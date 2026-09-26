/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SpectralStoneDuality.Functoriality
public import Mathlib.Order.Category.BddDistLat

/-!
# Spectral spaces and Stone functors

`SpectralCat` bundles spectral spaces with spectral maps. `spectrumFunctor`
maps `BddDistLatᵒᵖ` to this category, and `compactOpenFunctor` goes back by
pulling back compact opens. The principal-compact-open identification is
natural and supplies the lattice-side isomorphism `latticeUnitIso`.
The space-side reconstruction and the assembled equivalence are in the
`Reconstruction` and `Equivalence` modules.
-/

public section

set_option warningAsError true

open CategoryTheory Order Set TopologicalSpace Topology

universe u

namespace SpectralStoneDuality

/-- Spectral spaces with spectral maps. -/
structure SpectralCat where
  /-- The underlying type of points. -/
  carrier : Type u
  [topology : TopologicalSpace carrier]
  [spectral : SpectralSpace carrier]

attribute [instance] SpectralCat.topology SpectralCat.spectral

namespace SpectralCat

instance : CoeSort SpectralCat (Type u) := ⟨carrier⟩

/-- Bundle a spectral space. -/
abbrev of (X : Type u) [TopologicalSpace X] [SpectralSpace X] : SpectralCat where
  carrier := X

/-- Morphisms of bundled spectral spaces. -/
@[ext]
structure Hom (X Y : SpectralCat) where
  /-- The underlying spectral map. -/
  hom' : SpectralMap X Y

instance : CategoryTheory.Category SpectralCat where
  Hom X Y := Hom X Y
  id X := ⟨SpectralMap.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : CategoryTheory.ConcreteCategory SpectralCat (SpectralMap · ·) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- The underlying spectral map of a bundled morphism. -/
abbrev Hom.hom {X Y : SpectralCat} (f : Hom X Y) :=
  CategoryTheory.ConcreteCategory.hom (C := SpectralCat) f

/-- Bundle a spectral map as a morphism of spectral spaces. -/
abbrev ofHom {X Y : Type u} [TopologicalSpace X] [SpectralSpace X]
    [TopologicalSpace Y] [SpectralSpace Y] (f : SpectralMap X Y) :
    of X ⟶ of Y :=
  CategoryTheory.ConcreteCategory.ofHom (C := SpectralCat) f

@[ext]
theorem ext {X Y : SpectralCat} {f g : X ⟶ Y} (h : ∀ x, f.hom x = g.hom x) : f = g :=
  CategoryTheory.ConcreteCategory.hom_ext _ _ h

end SpectralCat

/-- Compact opens of a quasi-separated space form a distributive lattice. -/
instance compactOpensDistribLattice (X : Type u) [TopologicalSpace X]
    [QuasiSeparatedSpace X] :
    DistribLattice (TopologicalSpace.CompactOpens X) :=
  SetLike.coe_injective.distribLattice _ .rfl .rfl
    TopologicalSpace.CompactOpens.coe_sup TopologicalSpace.CompactOpens.coe_inf

/-- Pullback of compact opens along an unbundled spectral map. -/
@[expose]
def spectralMapCompactOpenComap {X Y : Type u} [TopologicalSpace X] [SpectralSpace X]
    [TopologicalSpace Y] [SpectralSpace Y] (f : SpectralMap X Y) :
    BoundedLatticeHom (TopologicalSpace.CompactOpens Y)
      (TopologicalSpace.CompactOpens X) where
  toFun U :=
    ⟨⟨f ⁻¹' (U : Set Y),
      (map_spectral f).isCompact_preimage_of_isOpen U.isOpen U.isCompact⟩,
      U.isOpen.preimage (map_spectral f).continuous⟩
  map_sup' U V := by ext; rfl
  map_inf' U V := by ext; rfl
  map_top' := by ext; rfl
  map_bot' := by ext; rfl

/-- Pullback of compact opens along a morphism of bundled spectral spaces. -/
@[expose]
def compactOpenComap {X Y : SpectralCat} (f : X ⟶ Y) :
    BoundedLatticeHom (TopologicalSpace.CompactOpens Y)
      (TopologicalSpace.CompactOpens X) :=
  spectralMapCompactOpenComap f.hom

/-- The prime-spectrum functor from bounded distributive lattices, contravariantly. -/
@[expose]
noncomputable def spectrumFunctor :
    CategoryTheory.Functor BddDistLatᵒᵖ SpectralCat where
  obj A := SpectralCat.of (PrimeIdealSpectrum A.unop)
  map f := SpectralCat.ofHom
    ⟨PrimeIdealSpectrum.spectrumComap f.unop.hom,
      PrimeIdealSpectrum.isSpectralMap_spectrumComap f.unop.hom⟩
  map_id A := by
    apply SpectralCat.ext
    intro P
    rfl
  map_comp f g := by
    apply SpectralCat.ext
    intro P
    rfl

/-- Compact opens, contravariantly, as a functor on spectral spaces. -/
@[expose]
noncomputable def compactOpenFunctor :
    CategoryTheory.Functor SpectralCat BddDistLatᵒᵖ where
  obj X := Opposite.op (BddDistLat.of (TopologicalSpace.CompactOpens X))
  map f := (BddDistLat.ofHom (compactOpenComap f)).op
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply BddDistLat.ext
    intro U
    apply TopologicalSpace.CompactOpens.ext
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply BddDistLat.ext
    intro U
    apply TopologicalSpace.CompactOpens.ext
    rfl

/-- Naturality of the principal-compact-open identification. -/
theorem compactOpenOrderIso_symm_naturality
    {X Y : BddDistLat} (f : X ⟶ Y)
    (U : TopologicalSpace.CompactOpens (PrimeIdealSpectrum X)) :
    f ((PrimeIdealSpectrum.compactOpenOrderIso (A := X)).symm U) =
      (PrimeIdealSpectrum.compactOpenOrderIso (A := Y)).symm
        (spectralMapCompactOpenComap
          (⟨PrimeIdealSpectrum.spectrumComap f.hom,
            PrimeIdealSpectrum.isSpectralMap_spectrumComap f.hom⟩ :
            SpectralMap (PrimeIdealSpectrum Y) (PrimeIdealSpectrum X)) U) := by
  apply (PrimeIdealSpectrum.compactOpenOrderIso (A := Y)).injective
  rw [OrderIso.apply_symm_apply]
  let a := (PrimeIdealSpectrum.compactOpenOrderIso (A := X)).symm U
  have hU : PrimeIdealSpectrum.compactOpenOrderIso (A := X) a = U :=
    OrderIso.apply_symm_apply _ U
  change PrimeIdealSpectrum.principalCompactOpen (f a) = spectralMapCompactOpenComap
    (⟨PrimeIdealSpectrum.spectrumComap f.hom,
      PrimeIdealSpectrum.isSpectralMap_spectrumComap f.hom⟩ :
      SpectralMap (PrimeIdealSpectrum Y) (PrimeIdealSpectrum X)) U
  apply TopologicalSpace.CompactOpens.ext
  change PrimeIdealSpectrum.basicOpen (Order.Ideal.principal (f a)) =
    PrimeIdealSpectrum.spectrumComap f.hom ⁻¹' (U : Set (PrimeIdealSpectrum X))
  rw [← hU]
  change PrimeIdealSpectrum.basicOpen (Order.Ideal.principal (f a)) =
    PrimeIdealSpectrum.spectrumComap f.hom ⁻¹'
      PrimeIdealSpectrum.basicOpen (Order.Ideal.principal a)
  exact (PrimeIdealSpectrum.spectrumComap_preimage_basicOpen_principal f.hom a).symm

/-- The lattice-side component of Stone duality. -/
noncomputable def latticeUnitComponent (A : BddDistLatᵒᵖ) :
    A ≅ (spectrumFunctor ⋙ compactOpenFunctor).obj A :=
  (BddDistLat.Iso.mk (PrimeIdealSpectrum.compactOpenOrderIso (A := A.unop))).symm.op

/-- The natural lattice-side unit `A ≅ QCOuv(Spec A)` in the opposite category. -/
noncomputable def latticeUnitIso :
    𝟭 BddDistLatᵒᵖ ≅ spectrumFunctor ⋙ compactOpenFunctor :=
  NatIso.ofComponents latticeUnitComponent fun {X Y} f ↦ by
    apply Quiver.Hom.unop_inj
    apply BddDistLat.ext
    intro U
    exact compactOpenOrderIso_symm_naturality f.unop U

end SpectralStoneDuality
