# Bounded native Markdown API and manual supplements

The [API reference](API.md) preserves **99 historical native doc-gen4 display
sites in seven leaves**, not a census of the current Lean modules or
all private/generated declarations. The root aggregate import and the original
Examples client have zero native display sites; they were included as inputs,
not omitted accidentally. Thirty-eight authored notes are explicitly labelled
**not source docstrings**. Three additional leaves are documented in manual
supplements: [compact-open cylinder bases](CompactOpenBasis.md) (eight public
declarations), [single-cylinder descent](LimitCylinderDescent.md) (three
theorems) and [finite-cylinder descent](FiniteCylinderDescent.md) (three
producer theorems). The lattice and soberification leaves are linked from the
[library README](../README.md); none of these later leaves has native display
records in this reference. Their import-only clients are not additional public
API. See the [mathematical guide](Guide.md) and [credits](CREDITS.md).

The historical reference records native names, kinds, visible header tokens,
source docstrings and source ranges. A field and its constructor may share an
enclosing source range. The seven original leaf sources and toolchain are
byte-identical between the native analysis and the current tree. The aggregate,
Examples and Lake configuration inputs have since changed; see the
[aggregate](../SpectralStoneDuality.lean) for its imports and
[`lakefile.toml`](../lakefile.toml) for the example roots. The manifest's
historical release inputs and its `api_sha256` refer to the **earlier snapshot**,
not to this checkout's complete input set or API introduction. The historical
hashes cannot certify modified inputs without matching authenticated native
generation.

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
their own checking units; 272 is not a prescribed total for the present full
inventory. Successful pinned-build evidence and a complete transitive
standard-axiom audit, including private repository declarations, apply when
relevant Lean source, build targets and configuration, resolved dependencies,
toolchain and checker inputs and required coverage match. Reuse matching
evidence across prose-only commits; renew only affected checks for changed
inputs or missing coverage. Separate stored-proof replay and fresh doc
generation are not prerequisites.

Separate historical raw-artifact application on the earlier nine-source graph
counted 272 occurrences (266 stored bodies and six structural replay units,
including private/generated declarations and private examples), with transitive
axioms limited to `propext`, `Classical.choice` and `Quot.sound`. This is not
the same measurement as the 272 *loaded* `env.constants` names or an audit of
this source tree. These historical numbers alone do not establish the present
full inventory or certify changed Lean inputs; use applicable exact-input
build and private-inclusive axiom-audit evidence for those claims.

This tree ships Markdown, relative links and an input/output manifest; it does
not ship the native HTML website, JS, styles, fonts, search or dependency
documentation, browser rendering or full dependency-site coverage. Historical
full-revision GitHub source URLs are retained as native input records; their
reachability in an independent public lineage is not established. The
historical `[Source]` links resolve within this tree for the original seven
leaves, whose source bytes and native ranges remain unchanged; the three
cylinder leaves have manual supplements instead of native display records.

## Reproduce native input and generated output

To reproduce the **historical generated API and its original whole-file hash**,
use an unchanged checkout of the older public snapshot
`698de8ace0c572cf3766529aa3edcede548e9848`, not this later checkout.
Its nine source/toolchain bytes and translated Lake configuration match the
fixed manifest. The aggregate, Examples and Lake inputs, as well as the API
introduction, differ in this checkout. `generate_api.py --check` cannot certify
this file or tree using the older manifest. In the historical checkout, use the
nine authenticated historical `declaration-data-*.bmp` records from the retained native
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

The historical generated API and three manual supplements are directly usable
without this evidence or historical checkout.
For an optional new native generation, the following is the **historical input
recipe**, not a claim that the translated release configuration was analyzed
or a request to regenerate docs for the current tree.
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
to verify provenance. Do not ship raw native HTML simply because `fromDb`
emits it into the temporary directory. To update the inventory from matching,
authenticated native records, omit `--check` when regenerating `API.md` and
`api-manifest.json`, then verify the new tree.

## Exact provenance and bounded controls

The committed format-2 [api-manifest.json](api-manifest.json) separates all
**twelve historical analyzed inputs** from all **twelve release-translated inputs** (nine
`.lean` files and three configuration files in each), every module path,
the tool and analyzed source revisions, all 99 display names, each canonical
native record, four documentation script/data inputs and the **old** generated
Markdown hash. Between analyzed and translated records only `lakefile.toml`
and `lake-manifest.json` differ: the historical Ideal
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
object and compares the nine sources and toolchain byte-for-byte with the old
translated snapshot;
the two configs must match their separately fixed translated hashes. Only an explicitly missing
commit, or a source-only tree with no `.git` marker, permits the committed
dual hash-manifest fallback with the same fixed translation. Broken Git, command failure, wrong object type, wrong
module, name, URL/revision/range, missing/extra/duplicate display, token or
source/pin drift must fail. `--check` compares both generated files byte-for-byte.
The supplied-record tests also cover same-tree relative links, unique anchors,
changed literals and docstrings, source-only and parentless single-commit Git
histories, and incorrect Git objects; `-O` and `-OO` exercise optimized modes.

These controls apply to the matching historical snapshot, not the aggregate,
Examples, Lake inputs or API introduction in this checkout. They only
validate data presented to them. They do not prove that
arbitrary supplied JSON was produced by doc-gen4, authenticate HTML in a
browser, or check proofs. Native provenance, loaded inventories, historical
proof application, source semantics and rights require separate evidence.

## Selected lint configuration and retained nonpasses

After a successful matching cache fetch, the retained selected checks were a
15-linter full-import declaration driver and mathlib's pinned `lint-style` on the
root, all seven leaves and Examples. The declaration check exited 1: the
`PrimeIdealSpectrum` abbreviation's `[BoundedOrder A]` argument is unused in
its *body*. The public type nevertheless advertises bounded distributive
lattices, and its topology, compact-open and functoriality interface uses that
domain. This is an unsuppressed historical linter nonpass, not a claim of a
successful declaration-linter run on the current tree. The earlier Examples
declaration check had zero findings among its 17 declarations.

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
