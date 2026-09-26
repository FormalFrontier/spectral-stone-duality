#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Generate this library's Markdown API from pinned native doc-gen4 records.

This is a deliberately fixed-library adapter, not a general documentation
certifier, a Lean parser, or a proof check. Native generation receipts remain
separate review evidence. See docs/README.md for the reproduction contract.
"""
import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess

TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
SOURCE = "64d7289b76f6973bd37a9d9098e545437d6a7142"
LEAVES = (
    "PrimeSpectrum", "Functoriality", "Category", "Reconstruction", "Equivalence",
    "Limits", "Subspace",
)
MODULE_PATHS = {
    **{"SpectralStoneDuality." + name: "SpectralStoneDuality/" + name + ".lean"
       for name in LEAVES},
    "SpectralStoneDuality": "SpectralStoneDuality.lean",
    "Examples.SpectralStoneDuality": "Examples/SpectralStoneDuality.lean",
}
MODULES = tuple(MODULE_PATHS)
INPUTS = tuple(MODULE_PATHS.values()) + (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json")
HERE = Path(__file__).resolve().parent
EXPECTED = json.loads((HERE / "api_inventory.json").read_bytes())
NOTES = json.loads((HERE / "api_notes.json").read_bytes())
GITHUB_SOURCE = "https://github.com/FormalFrontier/spectral-stone-duality/blob/"
# Fixed historical native-analysis inputs, not hashes learned from the current
# checkout or its manifest. Changing this contract requires renewed review.
ANALYZED_INPUTS = {
    "Examples/SpectralStoneDuality.lean": "78ae0f9ea2a7d415a2382d03c7d831223272e5fe8b9d22fefd2a5bef37649686",
    "SpectralStoneDuality.lean": "28995697f418749db40ad8f78e39725757847caf3b76e094a3424d6beebf5c07",
    "SpectralStoneDuality/Category.lean": "94b35bd49d51a9f27b8f8e8c03e9856769dbc450db9aebd89f8c9dbcdc2a58f2",
    "SpectralStoneDuality/Equivalence.lean": "88104933a786c7e1e9c43975d12e12225509e34bfd09643045bb8c0ac137cf2c",
    "SpectralStoneDuality/Functoriality.lean": "4863e7e78fc106dd96390c80100fc8c4131e90d7c20bab0c495c2b98ffecf77c",
    "SpectralStoneDuality/Limits.lean": "43d0cf729e20955959320b77aec6b75fad0970ec1a2c8307114e7e76e96fae71",
    "SpectralStoneDuality/PrimeSpectrum.lean": "54e2a6a7b60a2fed629b7900c9824f865f1ab69df0a3d86c0da4c7a6e66ad9a1",
    "SpectralStoneDuality/Reconstruction.lean": "c8021a2c2199f632af5250f776dcc222e6a66d0b5928a6b04e2b9b0d1e825aac",
    "SpectralStoneDuality/Subspace.lean": "f983b18feac8aac19442ae534e0355ae421c87878f39159ea99847193386d091",
    "lake-manifest.json": "f988303fdebcd8aa557378db2330774c4fd3ecf59c2788482e1dfa82fe8481e4",
    "lakefile.toml": "ff2b317a49d99ddb925a3a93ad68bad2a326a3f9f268531e2656b00f3b737047",
    "lean-toolchain": "8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88",
}
RELEASE_CONFIGS = {
    "lakefile.toml": "7ebdda62d980a42166b4e4b4fc4ea72adac18808e90250b669ca3979d131fe9d",
    "lake-manifest.json": "5d57d715a574f6ff89d30d4e90bdb39f6d559a69847ac7da103eb35c99e78240",
}
RELEASE_INPUTS = {**ANALYZED_INPUTS, **RELEASE_CONFIGS}
DEPENDENCY_TRANSLATION = {
    "dependency": "ideal-completion",
    "historical_revision": "a6f4d9c9614c20fe05f947902373d60e05504291",
    "release_revision": "001e3b7508184ecd51e0d86177cb1d54508bf59d",
    "release_url": "https://github.com/FormalFrontier/ideal-completion.git",
    "identical_tree": "ec847510a5d92e0473060f1d6d8bb33c0484164e",
    "changed_config_paths": sorted(RELEASE_CONFIGS),
}
NATIVE_RECORDS = {
    "Examples.SpectralStoneDuality": "8f8bba99e032f3b6bce2c73541422768e28921235e9097f39f61be383a86558b",
    "SpectralStoneDuality": "58e2687846ae0bdabb01a66ed4a7a108c9c0cfb4a6b3ec9872146e0ec55300fc",
    "SpectralStoneDuality.Category": "d1b0dfbb12cdbeb107df94f558771f8bf386f5a5dd61ef68daf163e92d4ed3e1",
    "SpectralStoneDuality.Equivalence": "e3934ec71df35d2a411106d8bcc4f354d715a6eb431606c58814062467dc2ac3",
    "SpectralStoneDuality.Functoriality": "9306db62cfcb3dbd86b1893315c3f68132c187999ca191d9d70239582a812764",
    "SpectralStoneDuality.Limits": "290ec01ad2ce7ba52f1f049084e55128f6902b1804bf8c6b32bf09b36a74f786",
    "SpectralStoneDuality.PrimeSpectrum": "8f4ae81e1a6ab0773e7d3aad356534dcf4810ea12f63191768ba483fee60c52b",
    "SpectralStoneDuality.Reconstruction": "ff7fba527d2baf865311b18ab7455e908c3cb7d3d72bcdd091b66a8fda544baf",
    "SpectralStoneDuality.Subspace": "ad7e53ec92eea53c90ff310f303f25994c7c86a059b54bc8becddfae71e25281",
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def source_range(info, revision, path, sources):
    """Validate the pinned native GitHub linker, not remote URL availability."""
    line_count = len(sources[path].splitlines())
    require(type(info["line"]) is int and 0 < info["line"] <= line_count,
            "invalid native source line")
    expected = GITHUB_SOURCE + revision + "/" + path
    match = re.fullmatch(re.escape(expected) + r"#L([1-9][0-9]*)-L([1-9][0-9]*)",
                         info["sourceLink"])
    require(match is not None, "native GitHub source URI or range differs")
    start, end = map(int, match.groups())
    require(start == info["line"] and start <= end <= line_count,
            "native GitHub range disagrees with source line/bounds")
    return start, end


def release_source_binding(sources):
    require(set(sources) == set(INPUTS), "source/pin inventory differs")
    require({path: digest(raw) for path, raw in sources.items()} == RELEASE_INPUTS,
            "source/pin drift from fixed release inputs")


def manifest_source_binding(manifest, revision, sources):
    """Reproduction without development ancestry; metadata is not an attestation."""
    release_source_binding(sources)
    require(type(manifest.get("format")) is int and manifest["format"] == 2
            and manifest.get("docgen_revision") == TOOL,
            "unsupported provenance manifest")
    require(manifest.get("analyzed_source_revision") == revision and
            manifest.get("modules") == list(MODULES) and
            manifest.get("module_paths") == MODULE_PATHS, "manifest source selection differs")
    require(revision == SOURCE and manifest.get("analyzed_inputs") == ANALYZED_INPUTS
            and manifest.get("dependency_translation") == DEPENDENCY_TRANSLATION
            and manifest.get("native_record_sha256") == NATIVE_RECORDS,
            "historical native provenance or dependency translation differs")
    require(manifest.get("inputs") == RELEASE_INPUTS,
            "source/pin drift from recorded manifest")


def git_source_binding(root, revision, sources):
    """Validate both sides of the one fixed config translation, not a bypass."""
    require(revision == SOURCE, "wrong frozen analyzed source revision")
    release_source_binding(sources)
    for path in INPUTS:
        old = subprocess.check_output(["git", "--no-replace-objects", "show",
                                       revision + ":" + path], cwd=root)
        require(digest(old) == ANALYZED_INPUTS[path], "historical input drift: " + path)
        if path not in RELEASE_CONFIGS:
            require(old == sources[path], "source/toolchain drift: " + path)


def git_source_available(root, revision):
    """Only a source-only tree or Git's explicit missing result permits fallback."""
    marker = root / ".git"
    if not marker.exists() and not marker.is_symlink():
        return False
    probe = subprocess.run(["git", "--no-replace-objects", "cat-file", "--batch-check"],
                           input=(revision + "\n").encode(), cwd=root,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(probe.returncode == 0, "cannot inspect selected Git object; refusing fallback")
    line = probe.stdout.decode().strip()
    if line == revision + " missing":
        return False
    require(re.fullmatch(re.escape(revision) + r" commit [0-9]+", line) is not None,
            "selected Git object is not a commit")
    return True


class Header(HTMLParser):
    """Keep all visible text, including every implicit argument; discard markup."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        attrs = dict(attrs)
        require(not any(attribute.startswith("on") for attribute in attrs), "active header attribute")
        if tag == "div" and "decl_type" in attrs.get("class", "").split():
            self.text.append(" ")
        self.stack.append((tag, set(attrs.get("class", "").split())))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected header declaration")

    def rendered(self):
        # Whitespace alone is normalized; all tokens and implicit binders remain.
        return " ".join("".join(self.text).split())


def render(records, revision, sources):
    require(revision == SOURCE, "wrong frozen source revision")
    require(set(records) == set(MODULES), "shipped module records differ")
    release_source_binding(sources)
    require(len(EXPECTED) == 99 and len(NOTES) == 38 and set(NOTES) <= set(EXPECTED),
            "bounded documentation inventory differs")
    rows = []
    found = {}
    for module in MODULES:
        record = records[module]
        require(record["name"] == module, "native module name differs")
        for row in record["declarations"]:
            info = row["info"]
            name, kind = info["name"], info["kind"]
            require(name in EXPECTED and EXPECTED[name]["kind"] == kind
                    and EXPECTED[name]["module"] == module, "unexpected public name/kind/module")
            require(name not in found, "duplicate public declaration")
            path = MODULE_PATHS[module]
            start, end = source_range(info, revision, path, sources)
            require((start, end) == (EXPECTED[name]["start"], EXPECTED[name]["end"]),
                    "native source span differs from fixed inventory")
            require(info["docLink"] == "./" + module.replace(".", "/") + ".html#" + name,
                    "native self link differs")
            header = Header(row["header"])
            require("".join(header.names) == name
                    and "".join(header.kinds) == EXPECTED[name]["display_kind"],
                    "native header identity differs")
            text = header.rendered()
            require(digest(text.encode()) == EXPECTED[name]["header_sha256"],
                    "native display signature differs, including implicit parameters")
            require("```" not in text and "```" not in info["doc"], "unsupported Markdown fence")
            require(bool(info["doc"].strip()) == (name not in NOTES),
                    "native docstring presence differs from source inventory")
            require(digest(info["doc"].encode()) == EXPECTED[name]["doc_sha256"],
                    "native source docstring differs")
            found[name] = EXPECTED[name]
            rows.append(dict(name=name, kind=kind, header=text, module=module,
                             doc=info["doc"].strip(), path=path, line=info["line"], end=end))
    require(found == EXPECTED, "missing public declaration")
    rows.sort(key=lambda row: (MODULES.index(row["module"]), row["line"], row["name"]))
    lines = ["# Generated API reference", "",
             "This reference contains all 99 native library display sites in seven leaves:",
             "51 theorems, 33 definitions, eleven instances, two structures and two",
             "constructors. The aggregate and separately built Examples module have no",
             "display sites. Import `SpectralStoneDuality` for the complete library;",
             "`Examples.SpectralStoneDuality` is not re-exported.",
             "At preparation on September 26, 2026, the separate frozen-source raw-artifact",
             "proof application was complete; full-release acceptance was not yet recorded.",
             "API display sites do not certify proofs or subsequent release acceptance.",
             "Native display-site counts are not a complete kernel-declaration census.", "",
             "Headers below are native doc-gen4 display signatures, not complete declarations",
             "with proof bodies. All native visible tokens, including implicit parameters and",
             "literal noncomputable modifiers, are retained; whitespace alone is normalized.",
             "Native pretty-printing uses each source namespace, notation and type inference;",
             "consult the linked source for suppressed inferred types and universe conventions.",
             "These displayed fragments are not promised to elaborate alone in a fresh namespace.",
             "Source links are relative to this same checkout.", "",
             "The source/pin hashes and generation provenance are in [api-manifest.json](api-manifest.json).",
             "See [generation instructions](README.md) and the [mathematical guide](Guide.md).",
             "Where no source docstring exists, a separately authored **API note** is labeled explicitly.", ""]
    lines += ["## Complete module inventory", "", "| Module | Display sites |", "| --- | --- |"]
    lines += ["| `" + module + "` | " + str(len(records[module]["declarations"])) + " |" for module in MODULES]
    lines += ["", "Native display sites and raw kernel declarations are distinct.",
              "The separate full-import loaded-environment inventory observed 272",
              "target-owned declarations through `env.constants`, not raw private artifact parts.",
              "This is not a complete raw-artifact census. Of those loaded declarations, 173 have",
              "no display site (112 private, 58 nonprivate automatically generated,",
              "and three nonprivate with `env.isAutoDecl = false`):",
              "`SpectralStoneDuality.PrimeIdealSpectrum.basicOpen.eq_1`,",
              "`SpectralStoneDuality.SpectralCat.rec` and",
              "`SpectralStoneDuality.SpectralCat.Hom.rec`.",
              "The two recursors are generated by the structures; `basicOpen.eq_1`",
              "is a generated equation theorem, despite their false classification flag.",
              "The completed frozen-source author application counted 272 raw occurrences:",
              "266 separate stored bodies and six structural replay units, including private",
              "declarations and examples. This count is independent of the 272 loaded names;",
              "equal totals do not establish a name-for-name correspondence. At preparation",
              "on September 26, 2026, full-release acceptance remained outstanding; later",
              "decisions belong to the exact-revision release records, not this generator.", ""]
    previous = None
    for row in rows:
        if row["module"] != previous:
            previous = row["module"]
            scope = "library leaf" if previous.startswith("SpectralStoneDuality.") else "aggregate or separate example module (zero display sites)"
            lines += ["## " + previous, "", "Scope: " + scope + ".", ""]
        anchor = "api-" + digest(row["name"].encode())[:16]
        # Code spans prevent GFM autolinking constructor names ending in .mk.
        lines += ['<a id="' + anchor + '"></a>', "", "### `" + row["name"] + "`", "",
                  "```lean", row["header"], "```", ""]
        if row["doc"]:
            lines += [row["doc"], ""]
        else:
            note = NOTES[row["name"]]
            require(isinstance(note, str) and bool(note.strip()) and "```" not in note,
                    "invalid authored API note")
            lines += ["**API note (not a source docstring):** " + note, ""]
        lines += [f"[Source](../{row['path']}#L{row['line']}-L{row['end']}) (native source range).", ""]
    markdown = "\n".join(lines).encode()
    native_hashes = {module: digest(json.dumps(records[module], sort_keys=True).encode())
                     for module in MODULES}
    require(native_hashes == NATIVE_RECORDS, "historical native record drift")
    manifest = dict(format=2, generator="scripts/generate_api.py", docgen_revision=TOOL,
                    analyzed_source_revision=revision, modules=list(MODULES),
                    module_paths=MODULE_PATHS, library_display_sites=99,
                    boundary_client_display_sites=0,
                    documentation_inputs={str(path.relative_to(HERE.parent)): digest(path.read_bytes())
                        for path in (HERE / "generate_api.py", HERE / "test_generate_api.py",
                                  HERE / "api_inventory.json", HERE / "api_notes.json")},
                    inputs={path: digest(sources[path]) for path in sorted(sources)},
                    analyzed_inputs=ANALYZED_INPUTS,
                    dependency_translation=DEPENDENCY_TRANSLATION,
                    native_display_declarations=[row["name"] for row in rows],
                    native_record_sha256=native_hashes,
                    api_sha256=digest(markdown), proof_certification=False,
                    release_acceptance=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True,
                   help="native fromDb output doc-data directory")
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--check", action="store_true", help="compare, never write")
    args = parser.parse_args()
    require(args.source_revision == SOURCE, "wrong frozen analyzed source revision")
    root = Path(__file__).resolve().parent.parent
    sources = {path: (root / path).read_bytes() for path in INPUTS}
    # A public release has independent ancestry: its analyzed development commit
    # need not be present. Prefer the exact Git object when available, otherwise
    # require the already committed complete dual source/pin manifest. Both paths
    # enforce the fixed historical-to-release config translation. Neither branch
    # attests that supplied JSON was genuinely produced by the native tool.
    if git_source_available(root, args.source_revision):
        git_source_binding(root, args.source_revision, sources)
        binding = "git-object"
    else:
        manifest = json.loads((root / "docs/api-manifest.json").read_bytes())
        manifest_source_binding(manifest, args.source_revision, sources)
        binding = "committed-source-hashes"
    require({path.name for path in args.native_data.glob("declaration-data-*.bmp")} ==
            {"declaration-data-" + module + ".bmp" for module in MODULES}, "native module file inventory differs")
    records = {module: json.loads((args.native_data / ("declaration-data-" + module + ".bmp")).read_bytes())
               for module in MODULES}
    api, manifest = render(records, args.source_revision, sources)
    if not args.check:
        (root / "docs").mkdir(exist_ok=True)
    for name, raw in [("API.md", api), ("api-manifest.json", manifest)]:
        target = root / "docs" / name
        if args.check:
            require(target.read_bytes() == raw, "generated file differs: " + name)
        else:
            target.write_bytes(raw)
    print(json.dumps(dict(status="matched" if args.check else "generated",
                          declarations=len(EXPECTED), api_sha256=digest(api),
                          source_binding=binding, release_acceptance=False)))


if __name__ == "__main__":
    main()
