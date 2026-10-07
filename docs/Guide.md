# Spectral spaces and bounded distributive lattices

This is a guide to the *reusable library*, not a source-coverage declaration.
Start with `import SpectralStoneDuality`; the module-specific imports below are
public alternatives. The [historical native API](API.md) displays seven original
leaves; the cylinder leaves have manual supplements for
[compact-open cylinder bases](CompactOpenBasis.md),
[single-cylinder descent](LimitCylinderDescent.md) and
[finite-cylinder descent](FiniteCylinderDescent.md). The closed-generizations,
finite-preservation, finite quasi-sobriety and cofinite APIs are described below.
The finite compact-open reconstruction API is described below as well.
The single `SpectralStoneDualityExamples` library includes these roots:
[duality/limits](../Examples/SpectralStoneDuality.lean),
[single-cylinder clients](../Examples/LimitCylinderDescent.lean),
[finite-cylinder clients](../Examples/FiniteCylinderDescent.lean),
[generic-point removal examples](../SpectralStoneDualityExamples/GenericPointRemoval.lean),
[soberification examples](../SpectralStoneDualityExamples/Soberification.lean),
[thin-lattice coproduct examples](../SpectralStoneDualityExamples/LatticeExtensive.lean),
[finite-preservation examples](../SpectralStoneDualityExamples/LatticePreserves.lean),
[closed-generization examples](../SpectralStoneDualityExamples/NhdsKer.lean),
[cofinite examples](../SpectralStoneDualityExamples/Cofinite.lean),
[finite-space examples](../SpectralStoneDualityExamples/FiniteSobriety.lean),
[locally closed examples](../SpectralStoneDualityExamples/LocallyClosed.lean),
[constructible-subspace examples](../SpectralStoneDualityExamples/ConstructibleSubspace.lean),
[finite-coordinate examples](../SpectralStoneDualityExamples/FiniteCoordinates.lean),
[finite-coordinate limit examples](../SpectralStoneDualityExamples/FiniteCoordinateLimits.lean),
and [limit-map examples](../SpectralStoneDualityExamples/LimitMaps.lean).

## Prime spectra and the open-set convention

`SpectralStoneDuality.PrimeIdealSpectrum A` is the subtype of prime **order
ideals** of a distributive lattice with bounded order. The `BoundedOrder A`
parameter is retained at this public boundary even though the underlying
subtype expression only uses the distributive lattice instance: it is the
bounded-lattice object used throughout the spectrum API, including prime
properness, the compact top open and functoriality. The historical native linter
reports this parameter unused in the abbreviation's *body*; the exposed
interface deliberately retains bounded order. This is not a linter pass and
has not been suppressed. In particular `A` need not
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

This realizes the bounded-lattice spectral duality of Fujiwara and Kato,
*Foundations of Rigid Geometry I*, arXiv:1308.4734v5, Chapter 0, §2.2(b),
Theorem 2.2.8, using Mathlib's prime ideals and spectral topology and
Ideal Completion's compact-principal theorem.

## Finite compact-open coordinates

`FiniteCoordinates.Stage F` consists of the **realized** compact-open membership
patterns on a finite family `F`, with the subspace topology inherited from a
product of Sierpiński `Prop` spaces. It is finite and spectral. Coordinate
opens, the continuous surjection `point F`, and the continuous surjective
`restrict` maps give concrete refinements even for the empty space. These
stages do **not** generally carry the quotient topology of `point F`: one
coordinate of a discrete two-point space already gives a counterexample.

`FiniteCoordinates.Family X` is the compatible product subtype. The forward
map `toFamily` is continuous; `inducing_toFamily` uses the singleton-coordinate
cylinders and the compact-open basis to recover the topology. `injective_toFamily`
then adds `T0Space X`. Surjectivity needs `CompactSpace X`,
`QuasiSeparatedSpace X`, `PrespectralSpace X` and `QuasiSober X`, but **not**
`T0Space X`. For a compatible family, the compact opens with false singleton
coordinate define a closed intersection `C`. Every true compact open meets
`C` by finite-stage realization and compactness; the finite-stage meet law
and the compact-open basis make `C` irreducible. A generic point of `C`
recovers every coordinate. Under `SpectralSpace X`, `spaceHomeomorph X`
packages the resulting bijective inducing map as `X ≃ₜ Family X`.
The finite spectral approximations are motivated by the representation
question in Fujiwara–Kato, Remark 2.2.4(2); they do not establish its
ring-spectrum assertion. The Sierpiński coordinate and generic-point APIs
are provided by Mathlib.

## Finite preservation in order categories

The [`CategoryTheory.Lattice.Preserves`](../SpectralStoneDuality/CategoryTheory/Lattice/Preserves.lean)
module concerns functors between the **element-order categories** of two bounded
lattices, not functors of `BddDistLat`. With independent carrier universes,
`Functor.map_top_of_preservesFiniteLimits` and
`Functor.map_inf_of_preservesFiniteLimits` recover the top and binary meet laws
from preservation of finite limits. Dually,
`Functor.map_bot_of_preservesFiniteColimits` and
`Functor.map_sup_of_preservesFiniteColimits` recover bottom and binary join.
The nullary theorems only require partial orders with top/bottom, and the
binary theorems only require the corresponding semilattices.

On bounded lattices, `Functor.toBoundedLatticeHom` constructs the map with
object function `F.obj`; `Functor.toBoundedLatticeHom_apply` simplifies
application. `Functor.toBoundedLatticeHom_toFunctor` recovers the functor,
`BoundedLatticeHom.toFunctor_toBoundedLatticeHom` recovers the homomorphism,
and `BoundedLatticeHom.equivFiniteLimitColimitPreservingFunctor` packages the
two directions. Mathlib provides the forward finite-preservation instances
for the functor of a bounded homomorphism. The proof uses preserved terminal
and initial objects for the nullary laws and preserved binary fans/cofans
for meets/joins, without adding top/bottom to the binary lemmas. Identity,
nonconstant Boolean-square projection and `Fin 1` instantiate the API;
constant-top and constant-bottom examples distinguish the nullary laws.
These results require no distributivity or nontriviality; they neither
construct (co)limits in the category of lattice *objects* nor assert a
source-specific categorical classification.
The distributive bounded special case occurs in Fujiwara–Kato, §2.2(b);
the Lean proof extends it to arbitrary bounded lattices and uses Mathlib's
finite-(co)limit preservation instances.

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
This generalizes Fujiwara–Kato, Theorem 2.2.10: its directed-system
statement uses compact-open lattice colimits, whereas this proof compares
constructible topologies through Mathlib's limit APIs.

For compactness, the proof equips the diagram with constructible topologies,
obtains a compact Hausdorff compatible-section limit, and forgets the finer
topologies via `fromConstructibleLimit`. Limit projections are spectral;
compact-open inverse-image cylinders form a basis under cofilteredness.
Sobriety is checked by taking generic points of closures of the projected
irreducible closed subset and proving their compatibility. Refer to the
linked statements for the exact size and topology parameters.

The [limit-map theorems](../SpectralStoneDuality/LimitMaps.lean) also show that
the projection of any supplied limiting cone is surjective when all spectral
transition maps are surjective, and closed when all spectral transition maps
are closed. The latter does not require surjectivity. These projection results
allow a cofiltered-or-empty index category because the selected stage supplies
an object; they assume no nonempty stages or Hausdorff spaces.
These generalize Fujiwara–Kato, Theorem 2.2.13 and Corollary 2.2.14,
with supplied categorical cones and the stated weaker map hypotheses.

`CompactOpenBasis` adapts the native cofiltered set basis to an `Opens.IsBasis` of
compact-open cylinders. For an arbitrary specified `C : Cone D` with `IsLimit C`,
it uses `C.π.app`; for a chosen limit it uses the literal `limit.π D`.
The general diagram requires `J : Type v`, `[Category.{w} J]`,
`[IsCofiltered J]`, `D : J ⥤ TopCat.{max v u}`, spectral stages and spectral
diagram arrows. The `Iᵒᵖ` version has the same-universe target `TopCat.{v}`
and assumes a **nonempty directed index preorder**, not nonempty stage spaces.
The [manual supplement](CompactOpenBasis.md) lists all eight declarations and
exact hypotheses. The existing `Limits` set-basis result remains unchanged.

`LimitCylinderDescent` takes a small cofiltered `J`, spectral stages and spectral
maps, and an actual cone `C` with `IsLimit C`. For an open compact `U` and open
`V` at stage `i`, inclusion of their inverse-image cylinders under `C.π.app i`
is equivalent to the same inclusion under `F.map X.hom` for some `X : Over i`.
Its chosen-limit version uses `limit.π`; its neighborhood version produces a
compact open containing the projection range whose inverse image is all of a
later stage. Empty stages and limits are allowed. No surjective transition,
inhabited stage or sheaf/section theorem is assumed or supplied. See the
[manual guide](LimitCylinderDescent.md) for names, exact assumptions and proof
provenance; none of these declarations belongs to the frozen native API output.

`FiniteCylinderDescent` uses the same small cofiltered actual-cone hypotheses
and a finite, possibly empty, type of labels. It descends a family of compact
opens simultaneously to a stage over a selected index. Its simultaneous
containment theorem uses commuting triangles, not only a common predecessor
object. Its cover theorem obtains a cover of the **whole stage**, with the
original labels and target inclusions intact. No stage is assumed inhabited,
and no desired eventual containment is a premise. An empty labelled cover of
an empty limit consequently yields an empty later stage. These are topology
results, not a sheaf gluing or section-colimit isomorphism theorem. The
[finite-cylinder supplement](FiniteCylinderDescent.md) records exact statements
and close proof-expression provenance.

The `Subspace` module has an independent basis-level theorem
`exists_compactOpen_image_eq_inter_of_basis`. In a prespectral `X`,
`exists_compactOpen_image_eq_inter` lifts any **compact open of `Y : Set X`**
to the intersection of `Y` with an ambient compact open; neither `Y` closed
nor `Y` compact is assumed. The proof takes a finite ambient basic-open
subcover of the compact image of the subspace open. If `g : Z → Y` becomes a
spectral map after composition with `Subtype.val : Y → X`, then
`isSpectralMap_to_subtype_of_comp` detects spectrality of `g` using that lift.

The [locally closed topology](../SpectralStoneDuality/Topology/LocallyClosed.lean)
shows that an inducing spectral map into a prespectral quasi-separated space
has quasi-separated source, without injectivity. In a prespectral
quasi-separated ambient space, a compact locally closed subset is retrocompact:
replace the open factor of its open-closed presentation with a compact open
containing the subset, then intersect with compact opens. Its ordinary subtype
is prespectral, compact and quasi-separated, even if the ambient space is not
compact. The cylinder-descent proof uses these results for compact locally
closed counterexample sets. See the [examples](../SpectralStoneDualityExamples/LocallyClosed.lean)
for empty, non-`T₀`, noninjective and noncompact-ambient boundaries; none of the
three conclusions alone implies sobriety.
This strengthens Fujiwara–Kato, Proposition 2.2.3, by removing ambient
compactness; it does not infer sobriety from the three conclusions.

## Soberification

For any space `X`, `IrreducibleCloseds X` consists of nonempty irreducible
closed subsets with opens detected by nonempty intersection with opens of
`X`. The unit sends `x` to the closure of `{x}`; maps into `T₀` quasi-sober
spaces extend uniquely, yielding a reflection in `TopCat`. Fujiwara–Kato,
§2.1(b), Proposition 2.1.3 states the sober reflection. The proof here
develops the open-set and extension argument directly with Mathlib's
irreducible-closed API, rather than following the source's cited EGA proof.

## Constructibly closed spectral subspaces

The [constructible-subspace topology](../SpectralStoneDuality/Topology/ConstructibleSubspace.lean)
uses `IsClosed[constructibleTopology X] S`, not the narrower predicate
`IsConstructible S`. For spectral `X`, it gives `SpectralSpace S` and a spectral
inclusion `S → X`; inclusion into any containing subspace follows by
`isSpectralMap_to_subtype_of_comp`. A family `F` needs only
`∀ U ∈ F, ∃ V ∈ F, IsOpen V ∧ IsCompact V ∧ V ⊆ U` to make `⋂₀ F`
spectral; no openness assumption on the other members is needed. The compact-open
neighborhoods of `x` intersect to `nhdsKer {x}`, whose points `y` satisfy
`y ⤳ x`. The [examples](../SpectralStoneDualityExamples/ConstructibleSubspace.lean)
show that constructible closedness does not require generization stability,
and that an infinite compact-open intersection need not be open.

## Finite irreducible sets and quasi-sobriety

For any topology, a finite irreducible subset contains a generic point of its
closure: `IsIrreducible.exists_isGenericPoint_closure_of_finite`. Cover the set
by the finitely many closed singleton closures and use irreducibility to find
one that contains the whole set. For closed sets, use
`IsIrreducible.exists_isGenericPoint_of_finite`; every finite space has a
`QuasiSober` instance, without a separation or nonemptiness assumption.
Quasi-sobriety alone does not imply `T₀`: in the indiscrete two-point space,
both points are generic for the whole space. The
[examples](../SpectralStoneDualityExamples/FiniteSobriety.lean) also exhibit
the non-`T₁` space `Prop` and an infinite cofinite obstruction.

## Cofinite spaces and quasi-sobriety

The [cofinite topology](../SpectralStoneDuality/Topology/Cofinite.lean) is
quasi-sober exactly when the underlying type is finite:
`CofiniteTopology.quasiSober_iff_finite X` works for any universe and includes
the empty type. Finite cofinite spaces are discrete, hence quasi-sober; their
`T₁` property makes them sober. For an infinite type, the whole cofinite space
is a nonempty irreducible closed set. It has no generic point: the closure of
each singleton is just that singleton. The corollary
`CofiniteTopology.not_quasiSober X` packages this obstruction under
`[Infinite X]`. The [examples](../SpectralStoneDualityExamples/Cofinite.lean)
test the empty, two-point and Nat cases independently of the separate
soberification-unit nonsurjectivity example.
The infinite obstruction occurs in Fujiwara–Kato, Exercise 0.2.1;
the iff theorem also proves the finite and empty directions.

## Closed generizations

For any topological space `X` and point `x`, Mathlib's `nhdsKer ({x} : Set X)`
consists of the generizations of `x`. If `X` is `T₀`, then
`isClosed_singleton_nhdsKer_iff x z` states that the singleton of a point
`z : nhdsKer {x}` is closed exactly when `(z : X) = x`.
The corollary `isClosed_singleton_nhdsKer x` proves closedness of the
original point without requiring a closed singleton in `X`.
The [upper-set `Fin 2` example](../SpectralStoneDualityExamples/NhdsKer.lean)
has two generizations, of which only the original is closed; an indiscrete
two-point space shows why `T₀` matters.
The closed-generization observation is from Fujiwara–Kato, §2.1(a),
with the same contextual `T₀` assumption, using Mathlib's `nhdsKer` formalization.

## Using this guide

The root [README](../README.md) gives the build instructions and
[bibliography](../README.md#references). [API.md](API.md) displays a
historical subset of the library API; the cylinder APIs are described in
their manual supplements. Example roots give usable clients, not additional
interfaces of the core library.
