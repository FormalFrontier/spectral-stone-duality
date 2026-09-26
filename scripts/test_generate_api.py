# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only controls on supplied native records; no Lean or doc-gen4 rerun.

The caller must authenticate the input directory separately. These tests exercise
the bounded adapter, not the native provenance of arbitrary supplied JSON.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

import generate_api as api

ROOT = Path(__file__).resolve().parent.parent
RECORDS = {}
SOURCES = {path: (ROOT / path).read_bytes() for path in api.INPUTS}


def fixture():
    return copy.deepcopy(RECORDS), dict(SOURCES)


def first(records):
    return records[api.MODULES[0]]["declarations"][0]


class Controls(unittest.TestCase):
    def test_declaration_headings_are_literal_code_spans(self):
        records, sources = fixture()
        raw, _ = api.render(records, api.SOURCE, sources)
        headings = [line for line in raw.decode().splitlines() if line.startswith("### ")]
        self.assertEqual(len(headings), len(api.EXPECTED))
        self.assertEqual(set(headings), {"### `" + name + "`" for name in api.EXPECTED})
        for name in ("SpectralStoneDuality.SpectralCat.mk",
                     "SpectralStoneDuality.SpectralCat.Hom.mk"):
            self.assertIn("### `" + name + "`", headings)
            self.assertNotIn("### " + name, headings)

    def test_loaded_inventory_is_not_raw_artifact_coverage(self):
        records, sources = fixture()
        raw, _ = api.render(records, api.SOURCE, sources)
        self.assertIn(b"loaded-environment inventory observed 272", raw)
        self.assertIn(b"not a complete raw-artifact census", raw)
        self.assertIn(b"266 separate stored bodies and six structural replay units", raw)
        self.assertNotIn(b"full-import raw census", raw)
        instructions = (ROOT / "docs/README.md").read_text()
        self.assertIn("loaded-environment inventory", instructions)
        self.assertIn("must not be joined by count alone", instructions)

    def test_complete_real_record_reproduction(self):
        records, sources = fixture()
        raw, manifest = api.render(records, api.SOURCE, sources)
        self.assertEqual(raw, (ROOT / "docs/API.md").read_bytes())
        self.assertEqual(manifest, (ROOT / "docs/api-manifest.json").read_bytes())
        facts = json.loads(manifest)
        self.assertEqual(raw.count(b"\n### "), 99)
        self.assertEqual(raw.count(b"**API note (not a source docstring):**"), 38)
        self.assertEqual(facts["library_display_sites"], 99)
        self.assertEqual(facts["boundary_client_display_sites"], 0)
        self.assertEqual(len(facts["inputs"]), 12)
        self.assertEqual(facts["analyzed_inputs"], api.ANALYZED_INPUTS)
        self.assertEqual(facts["inputs"], api.RELEASE_INPUTS)
        self.assertEqual(facts["dependency_translation"], api.DEPENDENCY_TRANSLATION)
        self.assertEqual(facts["native_record_sha256"], api.NATIVE_RECORDS)
        self.assertEqual({path for path in api.INPUTS
                          if facts["inputs"][path] != facts["analyzed_inputs"][path]},
                         {"lakefile.toml", "lake-manifest.json"})
        self.assertEqual(len(facts["documentation_inputs"]), 4)
        self.assertEqual(set(facts["native_record_sha256"]), set(api.MODULES))
        self.assertFalse(facts["proof_certification"])
        self.assertFalse(facts["release_acceptance"])
        for module in api.MODULES[-2:]:
            self.assertEqual(records[module]["declarations"], [])

    def test_all_visible_tokens_and_literal_kinds(self):
        raw = (ROOT / "docs/API.md").read_bytes()
        for record in RECORDS.values():
            for row in record["declarations"]:
                self.assertIn(api.Header(row["header"]).rendered().encode(), raw)
        self.assertIn(b"noncomputable def SpectralStoneDuality.stoneDuality", raw)
        self.assertIn(b"abbrev SpectralStoneDuality.PrimeIdealSpectrum", raw)
        self.assertIn(b"structure SpectralStoneDuality.SpectralCat", raw)
        self.assertIn(b"constructor SpectralStoneDuality.SpectralCat.mk", raw)
        self.assertEqual({record["display_kind"] for record in api.EXPECTED.values()},
                         {"theorem", "instance", "def", "noncomputable def",
                          "abbrev", "structure", "constructor"})
        from collections import Counter
        self.assertEqual(Counter(record["kind"] for record in api.EXPECTED.values()),
                         {"theorem": 51, "def": 33, "instance": 11,
                          "structure": 2, "ctor": 2})
        self.assertEqual(Counter(record["display_kind"] for record in api.EXPECTED.values()),
                         {"theorem": 51, "def": 13, "noncomputable def": 13,
                          "abbrev": 7, "instance": 11, "structure": 2,
                          "constructor": 2})

    def test_parser_entities_and_nested_names(self):
        self.assertEqual(api.Header('<div><span>{A : Type u} [Module R A]</span> :'
                                    '<div class="decl_type">x &lt; y</div></div>').rendered(),
                         '{A : Type u} [Module R A] : x < y')
        self.assertEqual(api.Header('<span><span>SpectralCat</span>.<span>Hom</span></span>').rendered(),
                         'SpectralCat.Hom')

    def test_parser_rejects_invalid_markup(self):
        for text in ('<script>x</script>', '<div><span></div>', '<div>unclosed',
                     '<span onclick="x">x</span>', '<div><!--comment--></div>',
                     '<!DOCTYPE html>', 'outside', '<div/>tail'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                api.Header(text)

    def test_name_kind_module_and_completeness_refusals(self):
        mutations = [lambda records: records.pop(api.MODULES[-1]),
                     lambda records: records.update(Extra=dict(name="Extra", declarations=[])),
                     lambda records: records[api.MODULES[0]]["declarations"].pop(),
                     lambda records: records[api.MODULES[0]]["declarations"].append(copy.deepcopy(first(records))),
                     lambda records: records[api.MODULES[1]]["declarations"].append(copy.deepcopy(first(records))),
                     lambda records: records[api.MODULES[0]].update(name="Wrong")]
        for key, value in (("name", "Wrong"), ("kind", "axiom"), ("line", 0),
                           ("line", 999999), ("line", True), ("docLink", "wrong")):
            mutations.append(lambda records, field=key, replacement=value:
                             first(records)["info"].update({field: replacement}))
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                records, sources = fixture()
                mutate(records)
                with self.assertRaises(ValueError):
                    api.render(records, api.SOURCE, sources)

    def test_signature_token_and_implicit_binder_loss(self):
        for needle, replacement in (("noncomputable def", "def"),
                                    (">Type</a> u", ">Type</a> v"),
                                    (">BoundedOrder<", ">DistribLattice<")):
            records, sources = fixture()
            row = next(row for record in records.values() for row in record["declarations"]
                       if needle in row["header"])
            row["header"] = row["header"].replace(needle, replacement)
            with self.subTest(needle=needle), self.assertRaises(ValueError):
                api.render(records, api.SOURCE, sources)
        records, sources = fixture()
        row = next(row for record in records.values() for row in record["declarations"]
                   if row["info"]["name"] == "SpectralStoneDuality.PrimeIdealSpectrum")
        visible = api.Header(row["header"]).rendered()
        self.assertIn('[BoundedOrder A]', visible)
        from html import escape
        name = row['info']['name']
        tail = visible[len('abbrev ' + name):].replace('[BoundedOrder A]', '')
        row['header'] = ('<div><span class="decl_kind">abbrev</span> '
                         '<span class="decl_name">' + escape(name) + '</span>'
                         '<span>' + escape(tail) + '</span></div>')
        with self.assertRaises(ValueError):
            api.render(records, api.SOURCE, sources)

    def test_docstring_bytes_and_absence_refused(self):
        for missing in (False, True):
            records, sources = fixture()
            row = next(row for record in records.values() for row in record["declarations"]
                       if (row["info"]["name"] in api.NOTES) == missing)
            row["info"]["doc"] = "fabricated" if missing else row["info"]["doc"] + "changed"
            with self.subTest(missing=missing), self.assertRaises(ValueError):
                api.render(records, api.SOURCE, sources)

    def test_source_url_and_exact_range_refusals(self):
        records, sources = fixture()
        info = first(records)["info"]
        valid = info["sourceLink"]
        base, fragment = valid.split("#")
        changes = [valid.replace("github.com", "github.com.evil.invalid"),
                   valid.replace("https://", "http://"),
                   valid.replace("/spectral-stone-duality/", "/other/"),
                   valid.replace(api.SOURCE, "b" * 40),
                   valid.replace("PrimeSpectrum.lean", "Other.lean"), base,
                   valid + "?query=1", valid + "\n", base + "#L1-L2",
                   base + "#L1-L0", base + "#L1-L999999",
                   base + "#L01-L2", base + "#L1", valid + "#extra"]
        self.assertTrue(fragment.startswith("L"))
        for value in changes:
            with self.subTest(value=value):
                altered = copy.deepcopy(records)
                first(altered)["info"]["sourceLink"] = value
                with self.assertRaises(ValueError):
                    api.render(altered, api.SOURCE, sources)

    def test_source_inventory_and_frozen_revision(self):
        records, sources = fixture()
        for revision in ("main", "a" * 40, api.SOURCE[:-1], api.SOURCE.upper()):
            with self.subTest(revision=revision), self.assertRaises(ValueError):
                api.render(records, revision, sources)
        for path in sources:
            altered = dict(sources)
            altered.pop(path)
            with self.subTest(path=path), self.assertRaises(ValueError):
                api.render(records, api.SOURCE, altered)

    def test_manifest_binding_all_twelve_inputs(self):
        manifest = json.loads((ROOT / "docs/api-manifest.json").read_bytes())
        api.manifest_source_binding(manifest, api.SOURCE, SOURCES)
        for key, value in (("format", 1), ("format", True), ("docgen_revision", "b" * 40),
                           ("analyzed_source_revision", "b" * 40),
                           ("modules", list(api.MODULES[:-1])), ("module_paths", {}),
                           ("inputs", {}), ("analyzed_inputs", {}),
                           ("dependency_translation", {}), ("native_record_sha256", {})):
            with self.subTest(key=key), self.assertRaises(ValueError):
                api.manifest_source_binding(dict(manifest, **{key: value}), api.SOURCE, SOURCES)
        for path in api.INPUTS:
            with self.subTest(path=path), self.assertRaises(ValueError):
                api.manifest_source_binding(manifest, api.SOURCE, dict(SOURCES, **{path: b"changed"}))

    def test_bundled_ext_notes_and_historical_status(self):
        for suffix in ("ext", "ext_iff"):
            name = "SpectralStoneDuality.SpectralCat.Hom." + suffix
            note = api.NOTES[name]
            self.assertIn("hom' fields", note)
            self.assertIn("bundled SpectralMap values", note)
            self.assertIn("SpectralMap.ext", note)
            self.assertIn("SpectralCat." + suffix, note)
        raw, _ = api.render(RECORDS, api.SOURCE, SOURCES)
        self.assertIn(b"At preparation on September 26, 2026", raw)
        self.assertNotIn(b"is still pending", raw)
        self.assertNotIn(b"complete but awaits", raw)

    def test_fixed_source_and_native_binding_cannot_learn_drift(self):
        manifest = json.loads((ROOT / "docs/api-manifest.json").read_bytes())
        for path in api.INPUTS:
            altered = dict(SOURCES, **{path: SOURCES[path] + b"\n"})
            forged = copy.deepcopy(manifest)
            forged["inputs"][path] = api.digest(altered[path])
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, "drift"):
                api.manifest_source_binding(forged, api.SOURCE, altered)
            with self.subTest(render_path=path), self.assertRaisesRegex(ValueError, "drift"):
                api.render(RECORDS, api.SOURCE, altered)
        records, sources = fixture()
        records[api.MODULES[0]]["unrendered-extra"] = "changed"
        with self.assertRaisesRegex(ValueError, "historical native record drift"):
            api.render(records, api.SOURCE, sources)

    def test_exact_translation_metadata_refusals(self):
        manifest = json.loads((ROOT / "docs/api-manifest.json").read_bytes())
        for key in api.DEPENDENCY_TRANSLATION:
            changed = copy.deepcopy(manifest)
            changed["dependency_translation"][key] = "wrong"
            with self.subTest(key=key), self.assertRaises(ValueError):
                api.manifest_source_binding(changed, api.SOURCE, SOURCES)
        for path in api.INPUTS:
            changed = copy.deepcopy(manifest)
            changed["analyzed_inputs"][path] = "0" * 64
            with self.subTest(path=path), self.assertRaises(ValueError):
                api.manifest_source_binding(changed, api.SOURCE, SOURCES)

    def test_same_tree_links_and_unique_anchors(self):
        markdown = (ROOT / "docs/API.md").read_text()
        links = re.findall(r"\[Source\]\(\.\./([^#)]+)#L(\d+)-L(\d+)\)", markdown)
        self.assertEqual(len(links), 99)
        for path, start, end in links:
            self.assertIn(path, api.MODULE_PATHS.values())
            self.assertTrue((ROOT / path).is_file())
            self.assertGreaterEqual(int(start), 1)
            self.assertLessEqual(int(start), int(end))
            self.assertLessEqual(int(end), len((ROOT / path).read_text().splitlines()))
        anchors = re.findall(r'<a id="(api-[0-9a-f]{16})"></a>', markdown)
        self.assertEqual(len(anchors), 99)
        self.assertEqual(len(set(anchors)), 99)
        self.assertEqual(set(anchors),
                         {"api-" + api.digest(name.encode())[:16] for name in api.EXPECTED})
        for target in ("api-manifest.json", "README.md", "Guide.md"):
            self.assertIn("](" + target + ")", markdown)
            self.assertTrue((ROOT / "docs" / target).is_file())

    def test_cli_source_only_parentless_drift_and_broken_git(self):
        with tempfile.TemporaryDirectory(prefix="spectral-api-controls-") as temporary:
            root = Path(temporary) / "candidate"
            native = Path(temporary) / "native"
            native.mkdir()
            for module, record in RECORDS.items():
                (native / ("declaration-data-" + module + ".bmp")).write_text(json.dumps(record))
            paths = list(api.INPUTS) + ["scripts/" + path for path in
                    ("generate_api.py", "test_generate_api.py", "api_inventory.json",
                     "api_notes.json")]
            paths += ["docs/API.md", "docs/api-manifest.json"]
            for path in paths:
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / path, target)
            argv = [sys.executable, "-B"] + ["-O"] * sys.flags.optimize + ["scripts/generate_api.py", "--native-data", str(native),
                    "--source-revision", api.SOURCE, "--check"]
            def run(ok, expected):
                result = subprocess.run(argv, cwd=root, capture_output=True)
                self.assertEqual(result.returncode == 0, ok, result.stderr.decode())
                self.assertIn(expected, (result.stdout + result.stderr).decode())
            def drift_controls():
                # Same refusals in source-only, parentless, and historical-object modes.
                for path in api.INPUTS:
                    old = (root / path).read_bytes()
                    try:
                        (root / path).write_bytes(old + b"\n")
                        run(False, "drift")
                    finally:
                        (root / path).write_bytes(old)
                for path in ("lakefile.toml", "lake-manifest.json"):
                    old = (root / path).read_bytes()
                    for needle, replacement in (
                        (api.DEPENDENCY_TRANSLATION["release_url"], "https://wrong.invalid/repo.git"),
                        (api.DEPENDENCY_TRANSLATION["release_revision"], api.DEPENDENCY_TRANSLATION["historical_revision"]),
                        ("83abb3e776bdefcbc447a1e44d0debe4010039e5", "a" * 40),
                    ):
                        self.assertIn(needle.encode(), old)
                        try:
                            (root / path).write_bytes(old.replace(needle.encode(), replacement.encode()))
                            run(False, "drift")
                        finally:
                            (root / path).write_bytes(old)
                old = (root / "lake-manifest.json").read_bytes()
                changed = json.loads(old)
                changed["packages"][0]["inputRev"] = "main"
                try:
                    (root / "lake-manifest.json").write_text(json.dumps(changed))
                    run(False, "drift")
                finally:
                    (root / "lake-manifest.json").write_bytes(old)
            run(True, 'committed-source-hashes')
            drift_controls()
            for path in (api.INPUTS[0], "lake-manifest.json", "docs/API.md",
                         "scripts/api_notes.json", "scripts/test_generate_api.py"):
                old = (root / path).read_bytes()
                (root / path).write_bytes(old + b"\n")
                run(False, "drift" if path in api.INPUTS else "generated file differs")
                (root / path).write_bytes(old)
            (root / ".git").write_text("invalid worktree marker\n")
            run(False, "refusing fallback")
            (root / ".git").unlink()
            subprocess.run(["git", "init", "-q", str(root)], check=True, capture_output=True)
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Fixture",
                            "-c", "user.email=fixture@example.invalid", "commit", "-qm",
                            "Synthetic independent-root fixture"], check=True)
            count = subprocess.check_output(["git", "-C", str(root), "rev-list", "--count", "HEAD"])
            self.assertEqual(count.strip(), b"1")
            self.assertFalse(api.git_source_available(root, api.SOURCE))
            run(True, 'committed-source-hashes')
            drift_controls()
            head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"]).decode().strip()
            tree = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD^{tree}"]).decode().strip()
            self.assertTrue(api.git_source_available(root, head))
            with self.assertRaisesRegex(ValueError, "not a commit"):
                api.git_source_available(root, tree)
            if api.git_source_available(ROOT, api.SOURCE):
                subprocess.run(["git", "-C", str(root), "fetch", "--quiet", "--no-tags",
                                "--depth=1", str(ROOT), api.SOURCE], check=True, capture_output=True)
                self.assertTrue(api.git_source_available(root, api.SOURCE))
                run(True, 'git-object')
                drift_controls()
            (native / "declaration-data-Extra.bmp").write_text("{}")
            run(False, "native module file inventory differs")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True)
    args = parser.parse_args()
    api.require({path.name for path in args.native_data.glob("declaration-data-*.bmp")} ==
                {"declaration-data-" + module + ".bmp" for module in api.MODULES}, "native file inventory differs")
    RECORDS.update({module: json.loads((args.native_data / ("declaration-data-" + module + ".bmp")).read_bytes())
                    for module in api.MODULES})
    unittest.main(argv=[sys.argv[0]], verbosity=2)
