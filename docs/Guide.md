# Spectral spaces and bounded distributive lattices

This is a guide to the *reusable library*, not a source-coverage declaration. Start
with `import SpectralStoneDuality`; the module-specific imports below are public
alternatives. The [generated historical API](API.md) binds its seven original leaves
to frozen sources, while the [compact-open cylinder API](CompactOpenBasis.md) is a
manual supplement for the new leaf; [Examples/SpectralStoneDuality.lean](../Examples/SpectralStoneDuality.lean)
is a separately compiled client of the aggregate public import.

## Prime spectra and the open-set convention

`SpectralStoneDuality.PrimeIdealSpectrum A` is the subtype of prime **order
ideals** of a distributive lattice with bounded order. The `BoundedOrder A`
parameter is retained at this public boundary even though the underlying
subtype expression only uses the distributive lattice instance: it is the
bounded-lattice object used throughout the spectrum API, including prime
properness, the compact top open and functoriality. The retained native linter
reported this parameter unused in the abbreviation's body. At preparation on
September 26, 2026, PR19 review3225 accepted this narrow convention departure,
not a linter pass or full-release approval. That historical disposition does not
assert acceptance of a later revision; consult its exact-revision release record.
It has not been suppressed or removed. In particular `A` need not
be nontrivial; its prime spectrum may be empty.

For an order ideal `I`, `PrimeIdealSpectrum.basicOpen I` is `D(I)`, the prime
ideals `P` for which `I` is *not* contained in `P`. This orientation matters:
`basicOpen_subset_iff` says `D(I) ⊆ D(J)` iff `I ≤ J`, and
`specializes_iff_ideal_le` identifies specialization of prime ideals with
inclusion. In the complementary `primeFilter` representation, the inclusion
direction reverses. `pointHomeomorph` identifies the spectrum with frame
points of `Order.Ideal A`; `idealOpenOrderIso` identifies the ideals with **all**
opens. The proof of order reflection for `D` invokes prime separation, not
set-theoretic inclusion alone. `isCompact_basicOpen_iff` says `D(I)` is
topologically quasi-compact iff `I` is principal, using compact elements of
the ideal completion. Compactness never assumes Hausdorffness.

The compact principal opens form a basis. Quasi-separatedness follows by
intersecting principal opens, compactness from the top basic open, and
quasi-sobriety from the prime ideal attached to an irreducible closed set.
Together with `T0Space`, these supply `SpectralSpace (PrimeIdealSpectrum A)`.

## Maps, reconstruction and naturality

For `f : BoundedLatticeHom A B`, `PrimeIdealSpectrum.spectrumComap f`
sends a prime ideal of `B` to its preimage in `A`. It is contravariant:
`spectrumComap_comp` reverses composition and
`spectrumComap_preimage_basicOpen_principal` computes the inverse image of a
principal basic open. The induced map is spectral, not just continuous.
`principalCompactOpen` and `compactOpenOrderIso` identify `A` with the compact
opens of its spectrum. The latter's application simp theorem is
`compactOpenOrderIso_apply`.

`SpectralCat` bundles a spectral space and uses spectral maps as morphisms.
`spectrumFunctor : BddDistLatᵒᵖ ⥤ SpectralCat` and
`compactOpenFunctor : SpectralCat ⥤ BddDistLatᵒᵖ` use the opposite category to
record contravariance. `latticeUnitIso` is the natural lattice-side
identification. For a spectral space `X`, `spaceToSpectrum X` sends a point to
the prime ideal of compact opens avoiding it. Its inverse recovers the generic
point of the corresponding nonempty irreducible closed set; **sobriety is
essential**. `spaceSpectrumHomeomorph` and `spaceUnitIso` provide the space-side
homeomorphism and natural isomorphism. `stoneDuality` packages the two functors
and their isomorphisms into `BddDistLatᵒᵖ ≌ SpectralCat`. It does not apply to
arbitrary non-sober spaces or assert a Boolean/Stone-space equivalence.

## Cofiltered limits and subspaces

The `Limits` API uses an independently quantified small `J : Type v`, a
cofiltered category `[IsCofiltered J]`, and a diagram
`F : J ⥤ TopCat.{max v u}`. `spectralSpace_limit_of_spectral` requires
`hX : ∀ j, SpectralSpace (F.obj j)` and spectrality of every diagram map;
these hypotheses are explicit. It proves spectrality of the compatible-section
limit. `nonempty_limit_of_spectral` additionally requires
`hne : ∀ j, Nonempty (F.obj j)`. It does *not* claim nonemptiness merely
from spectrality. The general helper
`IsSpectralMap.continuous_constructible` permits independent source and target
universes.

For compactness, the proof equips the diagram with constructible topologies,
obtains a compact Hausdorff compatible-section limit, and forgets the finer
topologies via `fromConstructibleLimit`. Limit projections are spectral;
compact-open inverse-image cylinders form a basis under cofilteredness.
Sobriety is checked by taking generic points of closures of the projected
irreducible closed subset and proving their compatibility. Refer to the
linked statements for the exact size and topology parameters.

`CompactOpenBasis` adapts the native cofiltered set basis to an `Opens.IsBasis` of
compact-open cylinders. For an arbitrary specified `C : Cone D` with `IsLimit C`,
it uses `C.π.app`; for a chosen limit it uses the literal `limit.π D`.
The general diagram requires `J : Type v`, `[Category.{w} J]`,
`[IsCofiltered J]`, `D : J ⥤ TopCat.{max v u}`, spectral stages and spectral
diagram arrows. The `Iᵒᵖ` version has the same-universe target `TopCat.{v}`
and assumes a **nonempty directed index preorder**, not nonempty stage spaces.
The [manual supplement](CompactOpenBasis.md) lists all eight declarations and
exact hypotheses. The existing `Limits` set-basis result remains unchanged.

The `Subspace` module has an independent basis-level theorem
`exists_compactOpen_image_eq_inter_of_basis`. In a prespectral `X`,
`exists_compactOpen_image_eq_inter` lifts any **compact open of `Y : Set X`**
to the intersection of `Y` with an ambient compact open; neither `Y` closed
nor `Y` compact is assumed. The proof takes a finite ambient basic-open
subcover of the compact image of the subspace open. If `g : Z → Y` becomes a
spectral map after composition with `Subtype.val : Y → X`, then
`isSpectralMap_to_subtype_of_comp` detects spectrality of `g` using that lift.

## Using this guide

The root [README](../README.md) gives the exact toolchain, private dependency
prerequisite and build commands. [API.md](API.md) displays frozen native doc-gen4
headers of seven leaves, not the new manual supplement, self-contained proof terms
or a complete raw declaration census.
The [API reproduction contract](README.md) explains revision bindings and
data-only tests. Examples are compiled by the default build but are private
clients, not additional exported interfaces. At preparation on September 26, 2026,
the author stored-proof application on the frozen sources was complete, while
full-release acceptance of the combined artifact remained outstanding. Later
decisions are recorded against exact revisions; this guide does not certify
release acceptance, rights clearance or source correspondence.
