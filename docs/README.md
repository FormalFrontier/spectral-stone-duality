# Bounded native Markdown API and manual supplement

The new eighth leaf, [`CompactOpenBasis`](CompactOpenBasis.md), has a separate
manual API supplement listing all eight declarations and exact hypotheses.
It was not in the frozen native doc-gen4 run, historical 99 display sites,
loaded-environment census or raw-artifact application below. These historical
counts and receipts cannot certify the new leaf or changed public-import and
example bytes. Do not regenerate or reinterpret the old records as if the new
module had been analyzed; the manual supplement is not native output.

[API.md](API.md) binds all 99 historical doc-gen4 display sites in seven library leaves to
exact native names, kinds, preserved visible header tokens, source docstrings
and line ranges. [Guide.md](Guide.md) explains the mathematics; [CREDITS.md](CREDITS.md)
records project expression and adaptation origins. `SpectralStoneDuality.lean`
is an aggregate public re-export and `Examples/SpectralStoneDuality.lean` is a
separate default build client: both have **zero native display sites**, not an
omission. There are 38 authored API notes explicitly labeled **not source
docstrings**. Two structures, their constructors and fields are represented
according to the native display records; a field and its constructor may
share an enclosing source range.

The separate full-import **loaded-environment inventory** at frozen source
revision `64d7289b76f6973bd37a9d9098e545437d6a7142` observed 272
target-owned declarations through `env.constants`. It did not enumerate raw
private artifact parts and is not a complete raw-artifact census. Of those
loaded declarations, 173 have no native display site: 112 private, 58
nonprivate with `env.isAutoDecl = true`, and three nonprivate with
`env.isAutoDecl = false`: `SpectralStoneDuality.PrimeIdealSpectrum.basicOpen.eq_1` and the
recursors `SpectralStoneDuality.SpectralCat.rec` and
`SpectralStoneDuality.SpectralCat.Hom.rec`. A *display site* is not a unique
kernel declaration count or a complete proof, visibility or rights audit.
The equation and two recursors are generated despite the false classification
flag. The historical raw-artifact inventory and stored-body application used
their own checking units; 272 is not a prescribed total for another revision.
Current computational release checks are the pinned build and complete actual
transitive standard-axiom audit, including private repository declarations.
Separate stored-proof replay and fresh doc generation are not prerequisites.

The frozen nine-module raw-artifact author application separately checks 272
raw occurrences as 266 stored bodies plus six structural replay units, including
private/generated declarations and the 17 private example declarations; the
owner reconciled the receipts in issue 17 comment 42839. These raw occurrences
must not be joined by count alone to the 272 *loaded* `env.constants` names.
Their transitive axioms are limited to the three permitted foundations. An
independent release acceptance of the combined artifact remained outstanding at
preparation on September 26, 2026. Later decisions belong to exact-revision
release records; this is a historical preparation account, not a live status.

This tree ships Markdown, relative links and an input/output manifest; it does
not ship the native HTML website, JS, styles, fonts, search or dependency
documentation. No browser rendering or full dependency-site coverage has been
claimed. Historical full-revision GitHub source URL strings are verified as
native input records, not asserted to be live or reachable in an independent
public lineage. The historical `[Source]` links resolve within this tree for
the original seven leaves, whose source bytes and native ranges remain unchanged.
The aggregate import and Examples file have changed and did not contribute
native display sites; the added eighth leaf has only its manual supplement.

## Reproduce native input and generated output

To reproduce the frozen generated Markdown, work in a separate checkout with
the nine historical Lean inputs and translated Lake configuration unchanged
(for example, the prior public-release revision
`698de8ace0c572cf3766529aa3edcede548e9848`). This candidate deliberately
changes the aggregate and Examples sources, so `generate_api.py --check`
**rejects it for input drift**; do not reinterpret the historical manifest
as a check of this candidate. In the separate checkout, use the nine
authenticated historical `declaration-data-*.bmp` records from the retained native
generation evidence (obtain that evidence from the maintainer). They are not
bundled website assets. No development ancestry or dependency cache is needed
for these data-only commands:

```sh
native_data=/absolute/path/to/authenticated/historical/doc-data
python3 -B scripts/generate_api.py --native-data "$native_data" --source-revision 64d7289b76f6973bd37a9d9098e545437d6a7142 --check
python3 -B scripts/test_generate_api.py --native-data "$native_data"
python3 -B -O scripts/test_generate_api.py --native-data "$native_data"
python3 -B -OO scripts/test_generate_api.py --native-data "$native_data"
```

The historical generated API and new manual supplement are directly usable
without this evidence or historical checkout.
For an optional new native generation, the following is the **historical input
recipe**, not a claim that the translated release configuration was analyzed.
It additionally requires access to the exact historical source checkout and its
declared dependencies; that development commit need not exist in public history.
Use a separate, unchanged `leanprover/doc-gen4` checkout at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db` with its committed manifest
and Lean `v4.34.0-rc2`; build only this core tool with `lake build doc-gen4`.
It is not a build dependency of this library. The C compiler must be on `PATH`
for doc-gen4's native SQLite dependencies. In the **historical source checkout**
at `64d7289b76f6973bd37a9d9098e545437d6a7142`, install
the pinned toolchain, retain its historical ten-package `lake-manifest.json`, fetch
the matching mathlib cache successfully *before* a library build, and build
all default targets, including the Examples module:

```sh
release_root="$PWD"
native_source=/absolute/path/to/exact/historical/source
python3 - "$native_source" <<'PY'
import hashlib, pathlib, runpy, sys
adapter = runpy.run_path("scripts/generate_api.py")
root = pathlib.Path(sys.argv[1])
actual = {p: hashlib.sha256((root / p).read_bytes()).hexdigest()
          for p in adapter["INPUTS"]}
if actual != adapter["ANALYZED_INPUTS"]:
    raise SystemExit("historical source/pin drift")
PY
cd "$native_source"
lake exe cache get
lake --wfail build
docgen_executable=/absolute/path/to/doc-gen4/.lake/build/bin/doc-gen4
docs_work=$(mktemp -d)
mkdir "$docs_work/analysis" "$docs_work/rendered"
source_revision=64d7289b76f6973bd37a9d9098e545437d6a7142
for leaf in PrimeSpectrum Functoriality Category Reconstruction Equivalence Limits Subspace; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" "SpectralStoneDuality.$leaf" api.db "https://github.com/FormalFrontier/spectral-stone-duality/blob/$source_revision/SpectralStoneDuality/$leaf.lean"
done
lake env "$docgen_executable" single --build "$docs_work/analysis" SpectralStoneDuality api.db "https://github.com/FormalFrontier/spectral-stone-duality/blob/$source_revision/SpectralStoneDuality.lean"
lake env "$docgen_executable" single --build "$docs_work/analysis" Examples.SpectralStoneDuality api.db "https://github.com/FormalFrontier/spectral-stone-duality/blob/$source_revision/Examples/SpectralStoneDuality.lean"
lake env "$docgen_executable" bibPrepass --build "$docs_work/rendered" --none
lake env "$docgen_executable" fromDb --build "$docs_work/rendered" --manifest "$docs_work/rendered/manifest.json" "$docs_work/analysis/api.db"
cd "$release_root"
python3 -B scripts/generate_api.py --native-data "$docs_work/rendered/doc-data" --source-revision "$source_revision" --check
python3 -B scripts/test_generate_api.py --native-data "$docs_work/rendered/doc-data"
python3 -B -O scripts/test_generate_api.py --native-data "$docs_work/rendered/doc-data"
python3 -B -OO scripts/test_generate_api.py --native-data "$docs_work/rendered/doc-data"
```

Create both directories **before** the SQLite `single` opener. `lake env` binds
the native tool to this project's compiled sources and exact imports. Native
`single` receives a URL without a fragment; doc-gen4 itself appends
`#Lstart-Lend`. Save argv, native stdout/stderr/warnings and exit status,
both native manifests, `api.db` and all nine `declaration-data-*.bmp` inputs
for a serious review. Do not ship raw native HTML simply because `fromDb`
emits it into the temporary directory. For an intentionally reviewed inventory
update, omit `--check` to regenerate `API.md` and `api-manifest.json` from
matching, authenticated native records, then verify the new tree.

## Exact provenance and bounded controls

The committed format-2 [api-manifest.json](api-manifest.json) separates all
**twelve historical analyzed inputs** from all **twelve release inputs** (nine
`.lean` files and three configuration files in each), every module path,
the tool and analyzed source revisions, all 99 display names, each canonical
native record, the adapter, tests, inventory and notes and the generated Markdown
hash. Only `lakefile.toml` and `lake-manifest.json` differ: the historical Ideal
revision `a6f4d9c9614c20fe05f947902373d60e05504291` becomes official private
GitHub revision `001e3b7508184ecd51e0d86177cb1d54508bf59d`, with the identical
tree `ec847510a5d92e0473060f1d6d8bb33c0484164e`. The exact two release config
hashes bind the URL, revision, manifest `inputRev` and all other dependencies;
there is no general same-tree exception. This recorded tree correspondence was
checked separately against actual dependency Git objects and publication evidence;
the data-only adapter does not fetch or attest those remote objects. Historical
native-record hashes remain unchanged. The fixed [inventory](../scripts/api_inventory.json) additionally binds
each displayed name to its literal native kind, display-kind tokens, module,
docstring bytes, visible signature tokens and bounded source range. Rendering
normalizes whitespace only; it retains implicit binders and modifiers. Source
namespaces and elaboration context govern native pretty-printing, so a displayed
header is not promised to elaborate in isolation. Generated Markdown links
use current-tree relative paths, not historical remote URLs.

Both modes enforce fixed expected hashes in the adapter, not hashes learned from
the current files or a modified manifest. When the analyzed historical commit
exists, the adapter checks all twelve historical input hashes against that Git
object and compares the nine sources and toolchain byte-for-byte with the release;
the two configs must match their separately fixed translated hashes. Only an explicitly missing
commit, or a source-only tree with no `.git` marker, permits the committed
dual hash-manifest fallback with the same fixed translation. Broken Git, command failure, wrong object type, wrong
module, name, URL/revision/range, missing/extra/duplicate display, token or
source/pin drift must fail. `--check` compares both generated files byte-for-byte.
The supplied-record tests also cover same-tree relative links, unique anchors,
changed literals and docstrings, source-only and parentless single-commit Git
histories, and incorrect Git objects; `-O` and `-OO` exercise optimized modes.

These controls only validate data presented to them. They do not prove that
arbitrary supplied JSON was produced by doc-gen4, authenticate HTML in a
browser, or check proofs. Review the separate native receipts, loaded inventory,
completed frozen proof application, source semantics, rights and release
candidate independently.

## Selected lint configuration and retained nonpasses

After a successful matching cache fetch, the retained selected checks were a
15-linter full-import declaration driver and mathlib's pinned `lint-style` on the
root, all seven leaves and Examples. The declaration check exited 1: the
`PrimeIdealSpectrum` abbreviation's `[BoundedOrder A]` argument is unused in
its *body*. The public type nevertheless advertises bounded distributive
lattices, and its topology, compact-open and functoriality interface uses that
domain. At preparation on September 26, 2026, PR19 review3225 accepted this
narrowly justified unsuppressed convention departure, without approving the
complete artifact. This historical disposition is not a linter pass or acceptance
of a later revision; consult its exact-revision release record. The declaration driver's Examples check had zero
findings among 17 declarations.

The root and seven-leaf text-style invocations exited 0 but warned that the
optional `scripts/nolints-style.txt` file is missing (treated as empty). The
original isolated and combined Examples invocations exited 1: in the pinned
tool's source-search path, `Examples.SpectralStoneDuality` resolved first to
the dependency `ideal-completion/Examples/SpectralStoneDuality.lean`, which
does not exist. To lint the exact shipped Examples file without excluding or
editing it, build the tool once and prepend this checkout to `LEAN_SRC_PATH`:

```sh
lake exe cache get
lake --wfail build lint-style
lake env bash -c 'export LEAN_SRC_PATH="$PWD:$LEAN_SRC_PATH"; exec .lake/packages/mathlib/.lake/build/bin/lint-style Examples.SpectralStoneDuality'
```

The selected style tool's module-source lookup uses `LEAN_SRC_PATH` but reads
the linted file relative to its current working directory. Run these commands
from this repository root; do not use `--fix` or suppress a finding. This is a
bounded Examples text-style check, not a replacement for the separate
15-linter run. With the pinned graph and this checkout first in the source
path, the exact-file Examples check exits 0 (with the optional missing-nolints
warning); the two uncorrected path-collision attempts remain failed receipts.
`lake check-lint` has no configured Lake lint driver and exited 1; this is a
configuration limitation, not a successful selected check.
