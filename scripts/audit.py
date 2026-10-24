#!/usr/bin/env python3
"""Check the public source package before building it.

This is a conservative, repository-specific preparation check. It neither runs
Lean's parser nor replaces Palomar's authenticated dependency, licence, metadata,
and source-closure checks. Run from any directory with Python 3.11 or later.
The checked-in formalization.yaml uses JSON, a strict subset of YAML, so this
script needs only the standard library.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PRINCIPAL_NAMES = [f"VerifiedPaper.t{i:02d}" for i in range(1, 14)]
EXPECTED_NAMES = PRINCIPAL_NAMES + ["VerifiedPaper.all_principal"]
SKIP_DIRS = {".git", ".lake"}
COMPILED_SUFFIXES = {
    ".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace",
    ".ir", ".exe", ".pyc", ".pdb", ".cmi", ".cmx",
}
ARXIV_MATH = {
    "math.AC", "math.AG", "math.AP", "math.AT", "math.CA", "math.CO", "math.CT",
    "math.CV", "math.DG", "math.DS", "math.FA", "math.GM", "math.GN", "math.GR",
    "math.GT", "math.HO", "math.IT", "math.KT", "math.LO", "math.MG", "math.MP",
    "math.NA", "math.NT", "math.OA", "math.OC", "math.PR", "math.QA", "math.RA",
    "math.RT", "math.SG", "math.SP", "math.ST",
}
ERRORS: list[str] = []
WARNINGS: list[str] = []


def check(condition: bool, message: str) -> None:
    if not condition:
        ERRORS.append(message)


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate key: {key}")
        result[key] = value
    return result


def read_json(path: Path, limit: int) -> dict:
    check(path.is_file() and not path.is_symlink(), f"missing regular file: {path.name}")
    if not path.is_file():
        return {}
    check(path.stat().st_size <= limit, f"oversized file: {path.name}")
    try:
        value = json.loads(path.read_text(encoding="utf-8-sig"), object_pairs_hook=unique_object)
        check(isinstance(value, dict), f"{path.name} must contain one mapping")
        return value if isinstance(value, dict) else {}
    except (UnicodeError, ValueError) as error:
        ERRORS.append(f"{path.name}: {error}; retain the documented JSON-compatible YAML format")
        return {}


def text(value: object, maximum: int | None = None) -> bool:
    return isinstance(value, str) and bool(value.strip()) and (maximum is None or len(value) <= maximum)


def names(value: object, field: str) -> None:
    check(isinstance(value, list) and bool(value), f"{field} must be a nonempty list")
    if not isinstance(value, list):
        return
    for person in value:
        name = person.get("name") if isinstance(person, dict) else person
        check(text(name), f"{field}: each person needs a nonempty name")
        check(not isinstance(name, str) or not re.search(r"\b(Codex|OpenAI|ChatGPT|GPT|AI agent|AI model)\b", name, re.I),
              f"{field}: reserve human authorship and responsibility for people")


def strip_lean_comments_and_strings(source: str) -> str:
    """Preserve newlines while removing nested comments and string literals."""
    output = []
    pos = depth = 0
    while pos < len(source):
        if depth:
            if source.startswith("/-", pos):
                depth += 1
                output.extend("  ")
                pos += 2
            elif source.startswith("-/", pos):
                depth -= 1
                output.extend("  ")
                pos += 2
            else:
                output.append("\n" if source[pos] == "\n" else " ")
                pos += 1
        elif source.startswith("/-", pos):
            depth = 1
            output.extend("  ")
            pos += 2
        elif source.startswith("--", pos):
            end = source.find("\n", pos)
            end = len(source) if end < 0 else end
            output.extend(" " * (end - pos))
            pos = end
        elif source[pos] == '"':
            output.append(" ")
            pos += 1
            while pos < len(source):
                if source[pos] == "\\":
                    output.extend("  ")
                    pos += 2
                elif source[pos] == '"':
                    output.append(" ")
                    pos += 1
                    break
                else:
                    output.append("\n" if source[pos] == "\n" else " ")
                    pos += 1
        else:
            output.append(source[pos])
            pos += 1
    check(depth == 0, "unterminated Lean block comment (Lean compilation also checks this)")
    return "".join(output)


def audit_metadata() -> None:
    metadata = read_json(ROOT / "formalization.yaml", 256 * 1024)
    check(metadata.get("version") == "v0.4", "formalization.yaml version must be v0.4")
    project = metadata.get("project", {})
    check(text(project.get("name"), 300), "project.name must be nonempty and <=300 characters")
    check(text(project.get("description"), 10000), "project.description must be nonempty and <=10000 characters")
    names(project.get("authors"), "project.authors")
    names(project.get("responsible_maintainers"), "project.responsible_maintainers")
    def reject_templates(value):
        if isinstance(value, str):
            check(not re.match(r"^\s*TEMPLATE(?::|$)", value), "retained TEMPLATE metadata value")
        elif isinstance(value, dict):
            for child in value.values():
                reject_templates(child)
        elif isinstance(value, list):
            for child in value:
                reject_templates(child)
    reject_templates(metadata)
    check(project.get("license") == "Apache-2.0", "this package's project.license must be Apache-2.0")
    classification = metadata.get("classification", {})
    arxiv = classification.get("arxiv", [])
    check(isinstance(arxiv, list) and 1 <= len(arxiv) <= 8 and all(isinstance(x, str) for x in arxiv)
          and len(set(arxiv)) == len(arxiv) and set(arxiv) <= ARXIV_MATH,
          "classification.arxiv must contain 1–8 distinct official mathematics categories")
    msc = classification.get("msc2020", [])
    check(isinstance(msc, list) and len(msc) <= 8 and all(isinstance(x, str) and re.fullmatch(r"\d{2}[A-Z]\d{2}", x) for x in msc)
          and len(set(msc)) == len(msc), "classification.msc2020 must contain at most 8 distinct five-character codes")
    methods = metadata.get("automation", {}).get("methods", [])
    check(isinstance(methods, list) and bool(methods) and all(isinstance(m, dict) and text(m.get("method")) for m in methods),
          "automation.methods needs nonempty method descriptions")
    check(text(metadata.get("review", {}).get("status")), "review.status must describe completed review")
    sources = metadata.get("sources", [])
    check(isinstance(sources, list) and bool(sources), "sources must be nonempty")
    if isinstance(sources, list):
        relationships = {"formalizes", "adapts", "independently-proves", "background", "other"}
        for source in sources:
            check(isinstance(source, dict) and text(source.get("title")) and source.get("relationship") in relationships,
                  "every source needs a title and recognized relationship")
        source_maps = [s for s in sources if isinstance(s, dict)]
        original = any(s.get("type") == "original-proof" for s in source_maps)
        if original:
            check(all(s.get("relationship") in {"background", "other"} for s in source_maps)
                  and all(s.get("relationship") == "other" for s in source_maps if s.get("type") == "original-proof"),
                  "original-proof sources cannot coexist with substantive source relationships")
        else:
            check(any(s.get("relationship") in {"formalizes", "adapts", "independently-proves"} for s in source_maps),
                  "source-based formalization needs a substantive source relationship")
    check("repository" not in metadata or metadata["repository"] == {"role": "substantive-development"},
          "this repository contains the substantive development; no thin-wrapper declaration is appropriate")
    status = metadata.get("status", {})
    check(status.get("sorry_count") == 0 and status.get("sorry_in_definitions") == 0, "proof-development hole counts must both be 0")
    check(isinstance(status.get("axioms"), list) and set(status.get("axioms", [])) <= ALLOWED_AXIOMS,
          "status.axioms must be a subset of the three permitted standard axioms")

    conventional = re.compile(r"^(LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(\.(md|markdown|txt))?$", re.I)
    licenses = [p for p in ROOT.iterdir() if conventional.fullmatch(p.name)]
    check(len(licenses) == 1, "exactly one conventional root licence file is required")
    if len(licenses) == 1:
        license_text = licenses[0].read_text(encoding="utf-8-sig")
        check(0 < licenses[0].stat().st_size <= 1024 * 1024, "root licence must be nonempty and <=1MiB")
        check("Apache License" in license_text and "Version 2.0, January 2004" in license_text
              and "END OF TERMS AND CONDITIONS" in license_text, "root licence must contain the Apache 2.0 standard licence")
        identifiers = re.findall(r"SPDX-License-Identifier:\s*([^\r\n]+)", license_text)
        check(not identifiers or identifiers == ["Apache-2.0"], "root licence SPDX identifier disagrees with metadata")


def audit_sources() -> dict:
    files = []
    total_bytes = 0
    source_hashes = {}
    def public_paths():
        for directory, dirs, names in os.walk(ROOT, followlinks=False):
            dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
            for name in list(dirs):
                p = Path(directory) / name
                check(not p.is_symlink(), f"submitted symlink is forbidden: {p.relative_to(ROOT)}")
                if p.is_symlink():
                    dirs.remove(name)
            for name in sorted(names):
                yield Path(directory) / name
    for path in public_paths():
        relative = path.relative_to(ROOT)
        if any(part in SKIP_DIRS for part in relative.parts):
            continue
        check(not path.is_symlink(), f"submitted symlink is forbidden: {relative.as_posix()}")
        if not path.is_file():
            continue
        files.append(path)
        total_bytes += path.stat().st_size
        check(not any(suffix in path.suffixes for suffix in COMPILED_SUFFIXES), f"compiled output outside .lake: {relative.as_posix()}")
        with path.open("rb") as stream:
            prefix = stream.read(256)
        check(not prefix.startswith(b"version https://git-lfs.github.com/spec/v1"), f"Git LFS pointer: {relative.as_posix()}")
        if path.suffix != ".lean":
            continue
        source = path.read_text(encoding="utf-8-sig")
        source_hashes[relative.as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
        check(len(source.splitlines()) <= 10000, f"Lean file exceeds10000 lines: {relative.as_posix()}")
        cleaned = strip_lean_comments_and_strings(source)
        if path.name != "lakefile.lean":
            check(re.match(r"\s*module\b", cleaned) is not None, f"missing Lean module header: {relative.as_posix()}")
        holes = re.findall(r"\b(?:sorry|admit)\b", cleaned)
        if relative.as_posix() == "Challenge.lean":
            check(len(holes) == 14 and len(re.findall(r"\bsorry\b", cleaned)) == 14,
                  "Challenge.lean must contain exactly 14 deliberate statement holes")
            check(path.stat().st_size <= 100 * 1024 and len(source.splitlines()) <= 1000,
                  "Challenge.lean exceeds the 100 KiB/1,000 line limit")
            if path.stat().st_size > 32 * 1024 or len(source.splitlines()) > 300:
                WARNINGS.append("Challenge exceeds Palomar's 32 KiB/300 line auditability warning threshold")
            for imports in re.findall(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)", cleaned):
                check(all(name == "Mathlib" or name.startswith("Mathlib.") for name in imports.split()),
                      "Challenge imports must come directly from canonical Mathlib only")
        else:
            check(not holes, f"proof-development hole in {relative.as_posix()}")
        for pattern in [r"\baxiom\b", r"\bunsafe\b", r"\bnative_decide\b", r"\bimplemented_by\b", r"\bextern\b",
                        r"Lean\.ofReduceBool", r"debug\.skipKernelTC", r"debug\.skipKernelCheck"]:
            check(re.search(pattern, cleaned) is None, f"disallowed proof-trust construct {pattern} in {relative.as_posix()}")
    check(total_bytes <= 500 * 1024 * 1024, "source package exceeds Palomar's 500 MiB limit")
    check(not (ROOT / ".gitmodules").exists(), "Git submodules are not allowed")
    return {"files": len(files), "bytes": total_bytes, "lean_sources": len(source_hashes), "source_sha256": source_hashes}


def audit_environment() -> None:
    check((ROOT / "lakefile.toml").is_file() and not (ROOT / "lakefile.lean").exists(), "retain exactly the declarative lakefile.toml")
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
    check(toolchain == "leanprover/lean4:v4.35.0-rc3", "this snapshot is pinned to Lean 4.35.0-rc3; audit future changes explicitly")
    manifest = read_json(ROOT / "lake-manifest.json", 1024 * 1024)
    packages = manifest.get("packages", [])
    check(isinstance(packages, list) and bool(packages), "commit the complete dependency manifest")
    mathlib = None
    for package in packages:
        if not isinstance(package, dict):
            ERRORS.append("manifest package must be a mapping")
            continue
        check(package.get("type") == "git", "this clean package uses only public pinned Git dependencies")
        check(isinstance(package.get("url"), str) and re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?", package["url"]),
              f"dependency must use credential-free public GitHub HTTPS: {package.get('name')}")
        check(isinstance(package.get("rev"), str) and re.fullmatch(r"[0-9a-f]{40}", package["rev"]),
              f"dependency needs a full lowercase 40-character revision: {package.get('name')}")
        if package.get("name") == "mathlib":
            mathlib = package
    check(mathlib is not None, "manifest must pin canonical Mathlib")
    if mathlib:
        check(mathlib.get("url", "").removesuffix(".git") == "https://github.com/leanprover-community/mathlib4", "Mathlib must use its canonical repository")
        with (ROOT / "lakefile.toml").open("rb") as stream:
            lakefile = tomllib.load(stream)
        declared = [p for p in lakefile.get("require", []) if p.get("name") == "mathlib"]
        check(len(declared) == 1 and declared[0].get("rev") == mathlib.get("rev"), "Lakefile and manifest Mathlib pins must match")
        dependency_toolchain = ROOT / ".lake" / "packages" / "mathlib" / "lean-toolchain"
        if dependency_toolchain.is_file():
            check(dependency_toolchain.read_text().strip() == toolchain, "installed Mathlib and project toolchains must match exactly")
        else:
            WARNINGS.append("Mathlib is not yet fetched; Palomar authenticates the pin and its exact toolchain independently")
    comparator = read_json(ROOT / "comparator.json", 1024 * 1024)
    check(set(comparator) <= {"challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms", "enable_nanoda"},
          "unexpected Comparator key (external_kernels belongs only in the protected generated local configuration)")
    check(comparator.get("challenge_module") == "Challenge" and comparator.get("solution_module") == "Solution", "Comparator modules must match this package")
    check(comparator.get("theorem_names") == EXPECTED_NAMES, "Comparator must check all 13 principal statements and their conjunction")
    check(comparator.get("definition_names", []) == [], "this formalization compares theorem statements, with no unspecified definitions")
    axioms = comparator.get("permitted_axioms", [])
    check(isinstance(axioms, list) and bool(axioms) and set(axioms) <= ALLOWED_AXIOMS, "Comparator may permit only the three standard axioms")


def main() -> int:
    try:
        audit_metadata()
        report = audit_sources()
        audit_environment()
    except (OSError, UnicodeError, ValueError, TypeError, AttributeError) as error:
        ERRORS.append(str(error))
        report = {}
    for warning in WARNINGS:
        print(f"WARNING: {warning}")
    for error in ERRORS:
        print(f"ERROR: {error}", file=sys.stderr)
    if ERRORS:
        print(f"Package audit failed: {len(ERRORS)} error(s).", file=sys.stderr)
        return 1
    print(f"Package audit passed: {report['lean_sources']} Lean sources; {report['files']} source-package files; {report['bytes']} bytes.")
    print("This local audit is preparation evidence, not a Palomar verification or editorial decision.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
