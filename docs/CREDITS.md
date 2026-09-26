# Origin, contributors and redistribution

Authors: Formal Frontier Agents. Original project contributions are under the
[complete Apache-2.0 license](../LICENSE); the root license was byte-matched
against Apache's official `LICENSE-2.0.txt` during this preparation. The
collective credit is not a copyright-owner assertion. Formal Frontier's
standing operator authorization covers verified original project contributions
for Apache-2.0 distribution. It does not cover copied third-party expression.
At preparation on September 26, 2026, this combined assembly was an unaccepted
development candidate. Independent rights review, including the actual proposed
public history, is a release requirement; later decisions are revision-specific.

## Tracked original expression

The tracked development first introduced the seven leaves in the commits
below. All are credited to Anchor (Source Maintainer) in Git; later merge
commits do not replace their actual author commits.

| Shipped Lean source | First project expression and relevant successor |
| --- | --- |
| `SpectralStoneDuality/PrimeSpectrum.lean` | `184e009` prime spectrum; `dd3adcc` specialization; `55ec5ce` module boundary; `e6e5b4c` exposed data |
| `SpectralStoneDuality/Functoriality.lean` | `7ad3fe1` spectrum maps; `55ec5ce` module boundary; `e6e5b4c` exposed data and private definitional witness |
| `SpectralStoneDuality/Category.lean` | `6ea16cc` functors; `55ec5ce` module boundary; `e6e5b4c` exposed data; `64d7289` projection/morphism docstrings |
| `SpectralStoneDuality/Reconstruction.lean` | `6126860` point reconstruction; `55ec5ce` module boundary |
| `SpectralStoneDuality/Equivalence.lean` | `6cd1051` assembled equivalence; `55ec5ce` module boundary |
| `SpectralStoneDuality/Limits.lean` | `40851d1` cofiltered limits; `b9a036f` independent universes; `55ec5ce` module boundary |
| `SpectralStoneDuality/Subspace.lean` | `a8e6cc8` arbitrary-subspace lifting; `55ec5ce` module boundary |
| `SpectralStoneDuality.lean` | `184e009` root import; subsequently extended through `55ec5ce` |
| `Examples/SpectralStoneDuality.lean` | `55ec5ce` separate named clients; `e6e5b4c` public-import repair |

`184e009` introduced the original project `lean-toolchain`, `lakefile.toml`,
`lake-manifest.json` and `.gitignore`. The historical documentation assembly left
its three pin/build files unchanged; this combined successor changes the two
Lake configuration files as described below, not the toolchain. `716904b` introduced `README.md`;
`55ec5ce` introduced the original Apache `LICENSE` and v0.4
`formalization.yaml` as well as the examples and README readiness text;
`ba49030` pinned the official internal ideal-completion dependency and updated
those documents. `e6e5b4c` is the ordinary-main repair by Worker A Task
`hive-request-98fe100318be420b41f003a72a01b4c79aae3264`, UID
`d6d4024a-6315-42c8-9063-ffe336bacd3a`. It exposed eight data definitions,
inlined the two prior private constructions verbatim in their public versions,
retained forty private helpers and added two private definitional witnesses.
The pre-repair project code, not external source text, is the expression
predecessor. The initial standalone documentation author is Worker B Task
`hive-request-266965db45b8ebe199a0f18a18198ee933fc2bbb`, UID
`ca1bbd66-45d3-48a9-a402-f5ce5f66a099`, request
`c45692fe38e98b2cd13a58d57c4b5d97`.

The frozen-source proof application was authored by Worker A Task
`hive-request-f8db1376b7f99c5c7cf7523d2657b2681cca37df`, UID
`07e91065-2c50-4c8c-ba3c-de14bf7d8d7e` (issue 17 comment 42800),
and reconciled by Anchor
in comment 42839; neither action changed shipped Lean. The subsequent
documentation and lint-disposition successor is authored by Worker B Task
`hive-request-76d5aa7fb571f01cc3991f62167a36a2afb4bd7b`, UID
`e0518da7-217d-4b2e-811a-fb55913d3b51`, request
`c966e42fb0513618edf8006a02816f5d`. It updates the release-status,
lint reproduction and proof-evidence descriptions, metadata, bounded API
generator/tests and regenerated Markdown using the unchanged native records.
It adds no mathematical code, external expression or third-party rights grant.

Anchor authored the subsequent combined repair: corrected the two authored
`SpectralCat.Hom.ext`/`ext_iff` notes to distinguish bundled-map and pointwise
equality, dated preparation-status claims, and translated the dependency pin to
its already published identical-tree GitHub release. The maintained adapter
now binds historical native inputs and translated release inputs separately,
with exact-hash refusal controls. Nine Lean files and historical native records
are unchanged; this is original project tooling and prose, not a new proof audit
or an automatic transfer of the earlier review.

## Mathematical sources and dependencies

The mathematical background is classical bounded distributive-lattice Stone
duality and spectral topology, with Fujiwara and Kato, *Foundations of Rigid
Geometry I*, arXiv:1308.4734v5, Chapter 0 §2.2 as a motivating reference.
Their book is not a redistributed component or an endorsement; no PDF, scan,
figure or substantial source excerpt ships. Source-level correspondence and
coverage decisions remain in their designated repository. The Lean code
uses mathematical ideas and public APIs, not an assertion that the book's
protected expression may be copied.

Lean, mathlib at `83abb3e776bdefcbc447a1e44d0debe4010039e5`, and the
official private GitHub ideal-completion snapshot
`001e3b7508184ecd51e0d86177cb1d54508bf59d` (tree
`ec847510a5d92e0473060f1d6d8bb33c0484164e`) are declared,
separately maintained dependencies. The historical native analysis used
`a6f4d9c9614c20fe05f947902373d60e05504291`, whose tree is identical;
commit identity, transport and the two configuration hashes differ. They are fetched, not vendored; their
copyright, attribution, NOTICE and licensing terms stay with their own
repositories. This tree does not copy their source files. The bounded API
renderer runs an unchanged, separately checked-out leanprover/doc-gen4 at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`; neither its generated
HTML/JS/fonts nor any dependency documentation ships here.

## Adapted project documentation tooling

`scripts/generate_api.py` and `scripts/test_generate_api.py` adapt original
Formal Frontier project code from `FormalFrontier/adic-modules` commit
`0e95f905ff0224d95378ddd6535ddb9655f322b5` (Anchor), under its existing
Apache-2.0 SPDX/author notices. That implementation itself adapts the project
`FormalFrontier/coherent-modules` implementation (Anchor) at
`1270dfa78e1d60d20ae15841b47be43dcc231287`, including native class,
constructor and field handling. This adaptation preserves the original notices
and Git-first/source-only/parentless fallback checks but replaces module,
display and note inventories, source URLs, counts and all test fixtures with
this library's actual native records. Native headers and docstrings are derived
from this project's own source through the unmodified doc-gen4 tool; the 38
separately authored missing-docstring notes are labeled in the API. The exact
adapter diff and native inputs reside in the separate evidence branch; neither
the Adic author commit nor this assembly has an automatic transferred review.

Release reviewers must still inspect all shipped mathematical expression,
documentation and this derivative tooling, verify actual rights and historic
public-ref reachability, and decide any copyright uncertainty. Previous agent
reviews and this author record are not legal or full-release acceptance.
