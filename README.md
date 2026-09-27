# spectral-stone-duality

Lean theory of the contravariant equivalence between bounded distributive lattices
and spectral spaces, with reusable topology of spectral limits and subspaces.

The September 27, 2026 finite-cylinder registration candidate adds a tenth
public leaf and a third explicit example root, for fourteen own Lean modules.
Its two Lean payloads are unchanged from the focused destination transfer
`77b6f14`; changed-root required
CI, fresh exact destination review, acceptance and the next official release
remain pending. The preceding cylinder-descent contribution is accepted at
`ec25325f882df909055d62e61c390066aec91ad9` and published as
`5e2cf4120087d32b1456e0244de46741d85dc83d` (same tree), verified September 27.
Historical preparation accounts and
measurements below retain their original scope; they do not certify this candidate.

## Mathematical scope

For a bounded distributive lattice `A`, the library constructs its prime-ideal
spectrum and identifies it with the point space of its frame of order ideals.
Every open has the form `D(I)`, the prime ideals not containing the ideal `I`.
Such an open is quasi-compact exactly when `I` is principal. Here compactness
means topological quasi-compactness; no Hausdorff hypothesis is intended.
Specialization is prime-ideal inclusion, or reverse inclusion of the complementary
prime filters. A trivial lattice is allowed and has an empty prime spectrum.

Bounded lattice homomorphisms act contravariantly by spectral maps. Compact opens
recover the original lattice, and points recover any spectral space from its
compact-open lattice. These natural identifications give
`SpectralStoneDuality.stoneDuality : BddDistLatᵒᵖ ≌ SpectralCat`.

The topology API also proves that small cofiltered limits of spectral spaces along
spectral maps are spectral, that the projections are spectral, and that compact-open
cylinders form a basis on any specified limiting cone or the actual chosen limit.
Nonemptiness of the limit is a separate theorem requiring every diagram object
to be nonempty; cylinder-basis theorems do not require it. Independently, a
compact open of any subspace
of a prespectral space lifts to an ambient compact open; the subspace need not be
closed or compact. Spectrality of a map to that subspace can be detected after
composing with its inclusion.

For an actual limiting cone, containment of a compact-open cylinder in an open
cylinder is witnessed at a stage over their common index. A neighborhood of a
projection's range contains a compact-open neighborhood whose inverse image is
eventually the entire stage. These results allow empty stages and empty limits;
they assume neither surjective transitions nor objectwise nonemptiness.

Finite labelled families of compact opens on an actual limit descend together
over a chosen index. Their compact-open/open containments hold at one coherent
stage; a finite cover of the limit descends to a cover of an entire stage while
preserving the labels and target inclusions. The family may be empty.

This is a reusable order/topology library, not a formalization of all rigid
geometry or a reconstruction theorem for arbitrary non-sober spaces. Source-specific
correspondence and coverage decisions are maintained outside this repository.

## Modules and public API

Use `import SpectralStoneDuality` for the whole library, or import a leaf below.
All library modules opt into Lean's module system; the root publicly re-exports
the ten leaves. Implementation-local helpers remain private.

| Module under `SpectralStoneDuality` | Selected interfaces |
| --- | --- |
| `PrimeSpectrum` | `PrimeIdealSpectrum`, `pointHomeomorph`, `idealOpenOrderIso`, `isCompact_basicOpen_iff`, specialization laws |
| `Functoriality` | `spectrumComap`, its identity/composition/preimage laws, `compactOpenOrderIso` |
| `Category` | `SpectralCat`, `spectrumFunctor`, `compactOpenFunctor`, `latticeUnitIso` |
| `Reconstruction` | `spaceToSpectrum`, `spaceSpectrumHomeomorph`, `spaceUnitIso` |
| `Equivalence` | `stoneDuality` |
| `Limits` | `spectralSpace_limit_of_spectral`, `nonempty_limit_of_spectral`, spectral projections and compact-open cylinder basis |
| `CompactOpenBasis` | `compactOpenCylinders_isBasis`, `chosenLimitCompactOpenCylinders_isBasis`, `directedCompactOpenCylinders_isBasis` and their cylinder/index definitions |
| `Subspace` | `exists_compactOpen_image_eq_inter`, `isSpectralMap_to_subtype_of_comp` |
| `LimitCylinderDescent` | `limitCylinder_subset_iff_eventually`, `chosenLimitCylinder_subset_iff_eventually`, `exists_compactOpen_eventually_full` |
| `FiniteCylinderDescent` | `exists_finiteCompactOpen_cylinders`, `finiteCylinder_subset_eventually`, `exists_finiteCompactOpen_fullStageCover` |

Names in the first two rows, apart from `PrimeIdealSpectrum`, are in the namespace
`SpectralStoneDuality.PrimeIdealSpectrum`; the other listed names are in
`SpectralStoneDuality`. The `Limits` diagram APIs use `J : Type v`, `[SmallCategory J]`
and `F : J ⥤ TopCat.{max v u}`. The general constructible-continuity helper supports
independent source and target universes.
The separate `CompactOpenBasis` API permits `[Category.{w} J]` rather than
`[SmallCategory J]` with `D : J ⥤ TopCat.{max v u}` and a specified `IsLimit C`;
its chosen version assumes `[HasLimit D]` and its `Iᵒᵖ` specialization uses
`[Preorder I] [IsDirectedOrder I] [Nonempty I]` and `TopCat.{v}`. See the
[manual module API](docs/CompactOpenBasis.md) for exact hypotheses.
The [cylinder-descent guide](docs/LimitCylinderDescent.md) states the separate
small-cofiltered-category, actual-cone and `Over i` hypotheses precisely.
The [finite-cylinder guide](docs/FiniteCylinderDescent.md) adds `[Finite α]`
without an inhabited-family or inhabited-stage assumption.

## Build and examples

Install [elan](https://github.com/leanprover/elan) and the toolchain in
`lean-toolchain` (Lean `v4.34.0-rc2`). The exact development inputs are:

- mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`;
- ideal-completion `001e3b7508184ecd51e0d86177cb1d54508bf59d`;
- the complete ten-package resolved graph in `lake-manifest.json`.

The [ideal-completion dependency](https://github.com/FormalFrontier/ideal-completion)
is a private GitHub repository; a downstream user needs authorized GitHub access.
The full commit above is its official release published on September 25, 2026,
with tree `ec847510a5d92e0473060f1d6d8bb33c0484164e`. Its publication included
a clean consumer of that exact GitHub URL and full revision. The source tree is
identical to the internally pinned dependency used in the ordinary-main review
of `e6e5b4c`; the transport URL and commit identity differ. This does not claim
that every reader or development agent already has private GitHub access, or
that Spectral itself has release acceptance. Tags are deferred.

Fetch the matching mathlib cache before building. Do not proceed to the build if
the cache fetch fails. After changing pins or replacing `.lake`, fetch it again.

```sh
lake exe cache get
lake --wfail build
```

The no-target build includes both the library and the separate
`SpectralStoneDualityExamples` target. The named private clients in
[`Examples/SpectralStoneDuality.lean`](Examples/SpectralStoneDuality.lean) use only
the public aggregate import and demonstrate spectra, maps, reconstruction,
equivalence, mixed-universe continuity, limits and arbitrary subspaces. To build
the Examples target after a successful cache fetch:

```sh
lake --wfail build SpectralStoneDualityExamples
```

That target also has a second explicit root,
[`Examples/LimitCylinderDescent.lean`](Examples/LimitCylinderDescent.lean), with
three named direct-import clients for actual cones, eventual-full neighborhoods
and chosen limits. Its third explicit root,
[`Examples/FiniteCylinderDescent.lean`](Examples/FiniteCylinderDescent.lean),
has four named public test theorems for finite labelled descent, coherent
containment, whole-stage covers and the empty-family case. Both earlier example
sources are unchanged. All three roots are configured for the default build;
the final candidate's combined check remains
pending, distinct from the successful focused transfer checks.

For example, the checked clients recover an arbitrary compact open from the
corresponding lattice element by `OrderIso.apply_symm_apply` and use the
objectwise nonempty hypothesis explicitly in the nonempty-limit theorem.

## Guide, API and observed build costs

The [mathematical guide](docs/Guide.md) explains spectrum conventions, map
orientation, sobriety, limit hypotheses and arbitrary-subspace lifting. The
[generated Markdown API](docs/API.md) retains 99 historical native display sites
from the original seven unchanged leaves, with frozen same-tree source ranges;
the eighth
leaf is documented in a [manual API supplement](docs/CompactOpenBasis.md), and
the ninth in the [cylinder-descent guide](docs/LimitCylinderDescent.md), and
the tenth in the [finite-cylinder guide](docs/FiniteCylinderDescent.md). None
was part of native generation. The historical API's [reproduction recipe](docs/README.md),
[input/output manifest](docs/api-manifest.json) and maintained bounded
[adapter](scripts/generate_api.py) and [tests](scripts/test_generate_api.py)
bind the exact source and tool revisions. These display records do not replace
the complete transitive axiom audit of built repository declarations.
The [credits](docs/CREDITS.md) distinguish
project expression, mathematical background and adapted project tooling.

Measured **on the historical analyzed graph** with internal Ideal revision
`a6f4d9c9614c20fe05f947902373d60e05504291`, not the translated GitHub transport:
the dependency tree is identical, but these are not measurements of a new fetch
or build at the published pin and are not portable speed guarantees. The accepted-
main owner verification of `e6e5b4c` on September 25, 2026 fetched the matching
mathlib cache in **95.087 s**, built all nine own sources under the two named
targets in **14.013 s** (1,929 Lake jobs) and compiled a separate public-import
client in **3.004 s**. Its 113 samples across the *whole verification job*
observed a **6,406,950,912-byte working peak** and **1,097,351,168-byte anonymous
peak** under a 23-GiB cgroup; these are sampled whole-job observations, not
per-target memory ceilings or a claim about uncached builds. This documentation
author's September 26 cached all-default build took **15 elapsed wall seconds**
for 1,929 jobs under a 15-GiB cgroup. Its cgroup-wide `memory.peak` was already
14,468,243,456 bytes before that build and remained unchanged afterward; it
includes the cache-download page cache and cannot isolate build memory. The
native documentation generation additionally ran nine module-specific `single`
steps of approximately **2.5–3.1 s each** and one `fromDb` step of **1.27 s**;
the separate core-tool build and dependency fetch are prerequisites and are not
included in those step times. Storage for cached dependencies may be multiple
GiB (about 7.8 GiB in this worktree). Network, hardware, cache availability,
memory accounting and cold compilation can change all these costs substantially.

## Development and release status

The computational release checks are a successful build of the pinned candidate
and a complete transitive axiom audit, including private repository declarations;
only `propext`, `Classical.choice` and `Quot.sound` are permitted. An ordinary
Lean build checks proofs. Separate stored-proof replay is not a release
prerequisite. Applicable unchanged evidence is reused; the historical replay
and native-documentation records below do not cover the new module or clients.
The compact-open basis contribution has its own successful default build and
standard-axiom results for all eight new public and seven new private example
declarations, retained in the development review record. Independent acceptance
and publication are separate decisions recorded against exact revisions.

The mathematical development and module-system/example/metadata repair at
`e6e5b4c` had independent ordinary-main review (PR18 review 3097, acceptance in
issue17 comment41638, integration comment41666 and owner verification
comment41731). At preparation on September 26, 2026, the earlier documentation
assembly `2bf169e` had received PR19 review3225 requesting corrections to two
bundled-map equality notes and unqualified review-status prose. This combined
successor corrects those notes and records the exact public dependency
translation; fresh acceptance of this successor was not yet recorded at
preparation. These are historical statements, not a claim about later decisions.
Ordinary development acceptance is not release or source-coverage certification.

The frozen nine-module sources have a completed author application of the
raw-artifact transitive-axiom and separate stored-body checks, reconciled in
the retained development owner intake dated September 26, 2026:
272 own raw occurrences (266 separate stored bodies and six structural replay
units), including private helpers, generated declarations and 17 private example
declarations. Their recorded transitive axiom sets contain only `propext`,
`Classical.choice` and `Quot.sound`. This is *evidence for*, not independent
acceptance of, full-release proof integrity or source correspondence; it does
not recheck the proof bodies of mathlib or the ideal-completion dependency.
The 272 loaded-environment names in the API inventory are a distinct measurement,
not a substitute for that raw-artifact application.

At that preparation checkpoint, final release acceptance still required fresh
independent review of this
documentation, the complete public API and inherited proof evidence, selected
linter dispositions, dependency status and rights/history. The unsuppressed
`unusedArguments` finding on the public `PrimeIdealSpectrum` abbreviation and
the original Examples style-lint path collisions are disclosed in the
[reproduction notes](docs/README.md). A corrected, exact-file Examples
text-style invocation passed with the optional missing-nolints warning; the
declaration-linter finding remains a nonpass. Successful
native API rendering and observed costs do not establish these other gates.
The exact-revision release records, rather than this historical preparation
account, identify any subsequent acceptance and publication.

Readiness work preserves names, mathematical statements, proofs and private
helpers. The module-system visibility boundary is intentional; code accessing
implementation-private declarations is unsupported. Downstream public-import
checks, rather than name preservation alone, establish compatibility.

## References, authors and license

The mathematics is classical Stone duality and spectral-space topology.
Fujiwara and Kato, *Foundations of Rigid Geometry I*, arXiv
[1308.4734v5](https://arxiv.org/abs/1308.4734v5), Chapter 0, Section 2.2,
is a motivating reference, not a claim of whole-section formalization or an
authorization to reproduce the book. Lean, mathlib's native order ideals,
frame points, spectral spaces and categorical topology, and the ideal-completion
library supply the formal infrastructure. No source PDF or source excerpt is bundled.

Authors: Formal Frontier Agents.

Original project contributions are licensed under the [Apache License 2.0](LICENSE).
Development and independent review use distinct AI-agent executions with Lean,
Lake and Git. This collective credit does not assert a copyright holder, human
authorship, mathematical novelty or source-author endorsement. Dependency authors
retain their own credit and applicable license terms. Final redistribution review
must cover incorporated third-party expression and generated assets, not just
this license label. Shipped [origin and contributor details](docs/CREDITS.md)
and the root [`formalization.yaml`](formalization.yaml) record
the scope, AI involvement and review status using format v0.4.

The source-maintainer team maintains this library; Anchor coordinates its
readiness work.
