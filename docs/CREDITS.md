# Origin and contributors

Authors: Formal Frontier Agents. Original project contributions carry
Apache-2.0 notices and are distributed under the [project license](../LICENSE).
This collective credit does not identify a copyright holder, confer rights in
third-party material or imply endorsement by the authors of a mathematical
reference. Contributor origins below distinguish original expression from
project adaptations; exact internal donor and review records are retained
separately from these public reader-facing credits.

## Lean development

Anchor, a Formal Frontier source maintainer, authored the project's original
prime-spectrum, functoriality, category, reconstruction, equivalence and
cofiltered-limit developments. The library's seven initial leaves, subsequent
mixed-universe limit and arbitrary-subspace APIs, and public module boundary
were developed and reviewed by distinct Formal Frontier agent contributors.
[`PrimeSpectrum`](../SpectralStoneDuality/PrimeSpectrum.lean),
[`Limits`](../SpectralStoneDuality/Limits.lean) and
[`Subspace`](../SpectralStoneDuality/Subspace.lean) document the shipped
mathematical statements; [the guide](Guide.md) explains their conventions.

The [compact-open cylinder-basis module](../SpectralStoneDuality/CompactOpenBasis.lean)
adapts earlier original project Lean research by Anchor into a reusable
specified-cone, chosen-limit and directed-index interface. Its
[manual supplement](CompactOpenBasis.md) gives the eight public declarations.

The [single-cylinder descent](../SpectralStoneDuality/LimitCylinderDescent.lean)
module closely adapts Anchor's original project Lean proof expression for
compact locally closed subspaces and counterexample diagrams. Another Formal
Frontier agent assembled the source-independent actual-cone descent,
chosen-limit and eventually-full results, named clients and
[guide](LimitCylinderDescent.md); a separate contributor adapted the module
paths and namespaces for this library. This is **reuse of project proof
expression**, not merely reliance on mathematical ideas or a claim to have
copied any source-book expression.

The [finite-cylinder descent](../SpectralStoneDuality/FiniteCylinderDescent.lean)
module likewise closely adapts Anchor's original single-cylinder finite
subcover, common-stage, pullback-union and cone-triangle proofs and finite
labelled stage selection. The collaborating contributor added coherent
`wideCospan` arrows and a whole-stage cover argument, with four named clients
and a [manual guide](FiniteCylinderDescent.md); a separate contributor
performed its destination adaptation. Anchor registered both cylinder modules
in the public import and example target. These are original project expression
and subsequent agent adaptations, not imports from a source research checkout.

The [soberification topology](../SpectralStoneDuality/Topology/Soberification.lean)
and [reflective adjunction](../SpectralStoneDuality/Topology/Category/Soberification.lean)
were developed by Formal Frontier agent contributors using mathlib's
irreducible-closed and category APIs. The
[soberification examples](../SpectralStoneDualityExamples/Soberification.lean)
exercise empty, non-separated, already sober and non-sober input spaces.

## Mathematical sources and dependencies

The mathematics draws on classical bounded distributive-lattice Stone duality
and spectral topology. Fujiwara and Kato, *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5), Chapter 0, §2.2,
is a motivating reference, not a claim of complete source formalization or
source-author approval. No book PDF, scan, figure or excerpt is shipped.

Lean and [mathlib](https://github.com/leanprover-community/mathlib4) supply
the proof assistant and native order, topology and category APIs. The
separately maintained [ideal-completion](https://github.com/FormalFrontier/ideal-completion)
library supplies ideal-completion and compact-principal results at the
published pin in [`lakefile.toml`](../lakefile.toml). Dependency authors
retain their own notices and license terms; those repositories are fetched,
not vendored. Authorized access is needed for the private ideal-completion
dependency. Neither dependency is credited as original project expression.

## Documentation tooling

[`scripts/generate_api.py`](../scripts/generate_api.py) and
[`scripts/test_generate_api.py`](../scripts/test_generate_api.py) adapt original
Formal Frontier documentation tooling authored by Anchor in the
`coherent-modules` and `adic-modules` projects. The adaptation changes the
source selection, inventory, notes and tests for this library while preserving
the tooling's existing author/SPDX notices. Native display headers and source
docstrings originate in this library's own Lean source and doc-gen4 output;
the 38 additional API notes are marked as authored, not source docstrings.
Only the historical Markdown API is shipped, not doc-gen4 HTML, scripts,
assets or third-party documentation. See the [historical API contract](README.md)
for its exact analyzed/translated input distinction.
