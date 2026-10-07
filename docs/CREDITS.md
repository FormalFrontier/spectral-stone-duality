# Sources and contributors

Authors: Formal Frontier Agents. AI agents developed the library, examples
and documentation. Original project contributions carry Apache-2.0 notices
and are distributed under the [project license](../LICENSE). This collective
credit does not identify a copyright holder, grant rights in other works or
imply endorsement by the authors cited below.

## Lean development

Anchor authored the project's original prime-spectrum, functoriality,
category, reconstruction, equivalence and
cofiltered-limit developments. Other Formal Frontier contributors developed
the mixed-universe limit, arbitrary-subspace, finite-coordinate and topology
APIs, as well as the examples and public module boundary.
[`PrimeSpectrum`](../SpectralStoneDuality/PrimeSpectrum.lean),
[`Limits`](../SpectralStoneDuality/Limits.lean) and
[`Subspace`](../SpectralStoneDuality/Subspace.lean) document the shipped
mathematical statements; [the guide](Guide.md) explains their conventions.

The [compact-open cylinder-basis module](../SpectralStoneDuality/CompactOpenBasis.lean)
and the original project Lean research it adapts were authored by
contributing Formal Frontier agents. The module supplies a reusable
specified-cone, chosen-limit and directed-index interface. Its
[manual supplement](CompactOpenBasis.md) gives the eight public declarations.

The [single-cylinder descent](../SpectralStoneDuality/LimitCylinderDescent.lean)
module closely adapts Anchor's original project Lean proof expression for
compact locally closed subspaces and counterexample diagrams. Other Formal
Frontier contributors assembled the specified-cone descent, chosen-limit and
eventually-full results and their [guide](LimitCylinderDescent.md), and adapted
the expressions to this library. This is **reuse of project proof expression**,
not merely reliance on mathematical ideas or copying of source-book expression.

The [finite-cylinder descent](../SpectralStoneDuality/FiniteCylinderDescent.lean)
module likewise closely adapts Anchor's original single-cylinder finite
subcover, common-stage, pullback-union and cone-triangle proofs and finite
labelled stage selection. Other contributors developed the coherent
`wideCospan` arrows, whole-stage cover and [guide](FiniteCylinderDescent.md),
and adapted the expressions to this library. These are original project
expression and subsequent agent adaptations, not third-party book text.

The [soberification topology](../SpectralStoneDuality/Topology/Soberification.lean)
and [reflective adjunction](../SpectralStoneDuality/Topology/Category/Soberification.lean)
were developed by Formal Frontier agent contributors using mathlib's
irreducible-closed and category APIs. The
[soberification examples](../SpectralStoneDualityExamples/Soberification.lean)
exercise empty, non-separated, already sober and non-sober input spaces.

## Mathematical sources and prior formalizations

Fujiwara and Kato, *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5), Chapter 0,
§§2.1–2.2, supply published Stone-duality, soberification and spectral-limit
statements and ideas. The lattice and spectrum modules realize Theorem
2.2.8. The cofiltered results generalize Theorems 2.2.10 and 2.2.13 and
Corollary 2.2.14; their constructible-limit proof uses mathlib rather than
the source's lattice-colimit argument. The soberification proofs develop
the open-intersection construction directly rather than following the
source's cited EGA proof.

The locally closed API generalizes Proposition 2.2.3 without ambient
compactness. Cofinite quasi-sobriety is characterized in both directions,
including finite and empty spaces, beyond the infinite obstruction in Exercise
0.2.1. The closed-generization statement keeps the contextual `T₀`
assumption of §2.1(a). Finite spectral coordinates are motivated by the
representation question in Remark 2.2.4(2), but construct no ring and do
not prove a ring-spectrum representation. The cylinder arguments use compact
locally closed subspaces and finite-subcover techniques from Propositions
2.2.3 and 2.2.9, yet their labelled and specified-cone conclusions are not assertions
of the source. SGA 4, Tome I, Exposé II, Definition 4.5, supplies the
terminology of universally disjoint sums, not the lattice proofs here.
See the [bibliography](../README.md#references) and module references for
full details and version-specific locations. No book PDF, scan, figure or
excerpt is shipped; citation grants no right to reproduce source expression.

Lean and [mathlib](https://github.com/leanprover-community/mathlib4) supply
the proof assistant and previously formalized order, topology and category
APIs. The separately maintained [ideal-completion](https://github.com/FormalFrontier/ideal-completion)
library supplies ideal-completion and compact-principal results at the pin in
[`lakefile.toml`](../lakefile.toml). Their proof techniques and interfaces
are used here. Dependency authors retain their own notices and license terms;
neither dependency is credited as original project expression.

The generic-point fork and its independent closed points follow the earlier
Formal Frontier formalization in *Valuation Integers*. Its topological
specialization laws are combined here with mathlib's specialization-order and
topological-category APIs for the discrete-incidence gluing square. The
finite-space motivation follows Stefan Schröer, *A simple proof for Hochster's
Theorem*, §2. Schröer credits an antecedent of Y. Ershov; Ershov's original
text was not consulted.

## Documentation tooling

[`scripts/generate_api.py`](../scripts/generate_api.py) and
[`scripts/test_generate_api.py`](../scripts/test_generate_api.py) adapt original
Formal Frontier documentation tooling authored by Anchor in the
`coherent-modules` and `adic-modules` projects. The adaptation changes the
source selection, inventory, notes and tests for this library while preserving
the tooling's existing author/SPDX notices. Native display headers and source
docstrings originate in this library's Lean source and doc-gen4 output;
the separately authored API notes are not source docstrings. See the
[API reference](API.md) for the historical generated entries.
