#!/usr/bin/env python3
"""Static consistency checks for the paper--Lean correspondence manifest.

This script deliberately does not invoke Lean or LaTeX.  It catches stale labels,
misspelled Lean declaration names, and drift between the challenge, solution, and
comparator sources.  A successful run is not a substitute for elaboration by Lean.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


STATEMENT_ENVIRONMENTS = {
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "definition",
}
LABEL_RE = re.compile(r"\\label\{((?:thm|def):[^}]+)\}")
BEGIN_RE = re.compile(
    r"\\begin\{(" + "|".join(sorted(STATEMENT_ENVIRONMENTS)) + r")\}"
)
DECL_RE = re.compile(
    r"^\s*"
    r"(?:@\[[^\]]*\]\s+)*"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|axiom|opaque)\s+"
    r"([^\s\(\{\[:]+)"
)
AUDIT_DECL_RE = re.compile(r"(?m)^\s*theorem\s+(audit_[A-Za-z0-9_']+)\b")


class ManifestError(ValueError):
    pass


@dataclass(frozen=True)
class PaperDeclaration:
    label: str
    kind: str
    file: Path
    line: int


@dataclass(frozen=True)
class LeanDeclaration:
    name: str
    kind: str
    file: Path
    line: int


def _scalar(raw: str, path: Path, line: int) -> Any:
    raw = raw.strip()
    if not raw:
        return None
    if raw.startswith(("\"", "'", "[", "{")):
        if raw.startswith("'"):
            if not raw.endswith("'"):
                raise ManifestError(f"{path}:{line}: unterminated quoted scalar")
            return raw[1:-1].replace("''", "'")
        try:
            return json.loads(raw)
        except json.JSONDecodeError as exc:
            raise ManifestError(f"{path}:{line}: invalid quoted/inline value: {exc}") from exc
    if raw in {"true", "false"}:
        return raw == "true"
    if raw in {"null", "~"}:
        return None
    if re.fullmatch(r"-?\d+", raw):
        return int(raw)
    if raw.startswith((">", "|")):
        raise ManifestError(
            f"{path}:{line}: folded and literal YAML blocks are unsupported; "
            "use a one-line quoted scalar"
        )
    return raw


def _key_value(text: str, path: Path, line: int) -> tuple[str, Any]:
    if ":" not in text:
        raise ManifestError(f"{path}:{line}: expected 'key: value'")
    key, raw = text.split(":", 1)
    key = key.strip()
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key):
        raise ManifestError(f"{path}:{line}: invalid key {key!r}")
    return key, _scalar(raw, path, line)


def load_manifest(path: Path) -> dict[str, Any]:
    """Load the documented, dependency-free YAML subset used by the manifest.

    JSON is accepted as well because it is a YAML subset.  The YAML form supports
    top-level scalars, top-level scalar lists, and a top-level ``entries`` list of
    mappings whose values are scalars or scalar lists.
    """

    text = path.read_text(encoding="utf-8")
    try:
        value = json.loads(text)
    except json.JSONDecodeError:
        value = None
    if value is not None:
        if not isinstance(value, dict):
            raise ManifestError(f"{path}: top-level JSON/YAML value must be a mapping")
        return value

    result: dict[str, Any] = {}
    top_list: str | None = None
    current_entry: dict[str, Any] | None = None
    entry_list: str | None = None

    for line_no, original in enumerate(text.splitlines(), 1):
        if not original.strip() or original.lstrip().startswith("#"):
            continue
        if "\t" in original[: len(original) - len(original.lstrip())]:
            raise ManifestError(f"{path}:{line_no}: indentation must use spaces")
        indent = len(original) - len(original.lstrip(" "))
        stripped = original.strip()

        if indent == 0:
            key, scalar = _key_value(stripped, path, line_no)
            if key in result:
                raise ManifestError(f"{path}:{line_no}: duplicate top-level key {key!r}")
            if scalar is None and key in {"manuscript_files", "paper_files", "entries"}:
                result[key] = []
                top_list = key
            else:
                result[key] = scalar
                top_list = None
            current_entry = None
            entry_list = None
            continue

        if top_list in {"manuscript_files", "paper_files"}:
            if indent != 2 or not stripped.startswith("- "):
                raise ManifestError(f"{path}:{line_no}: expected a two-space-indented list item")
            result[top_list].append(_scalar(stripped[2:], path, line_no))
            continue

        if top_list == "entries":
            if indent == 2 and stripped.startswith("- "):
                current_entry = {}
                result["entries"].append(current_entry)
                entry_list = None
                remainder = stripped[2:].strip()
                if remainder:
                    key, scalar = _key_value(remainder, path, line_no)
                    current_entry[key] = scalar
                continue
            if current_entry is None:
                raise ManifestError(f"{path}:{line_no}: entry field precedes the first entry")
            if indent == 4:
                key, scalar = _key_value(stripped, path, line_no)
                if key in current_entry:
                    raise ManifestError(f"{path}:{line_no}: duplicate entry key {key!r}")
                if scalar is None:
                    current_entry[key] = []
                    entry_list = key
                else:
                    current_entry[key] = scalar
                    entry_list = None
                continue
            if indent == 6 and stripped.startswith("- ") and entry_list:
                current_entry[entry_list].append(_scalar(stripped[2:], path, line_no))
                continue
            raise ManifestError(f"{path}:{line_no}: unsupported entries indentation or syntax")

        raise ManifestError(f"{path}:{line_no}: unexpected indentation")

    return result


def validate_manifest(data: dict[str, Any], path: Path) -> tuple[list[str], list[dict[str, Any]]]:
    manuscript_files = data.get("manuscript_files", data.get("paper_files"))
    entries = data.get("entries")
    if not isinstance(manuscript_files, list) or not all(
        isinstance(item, str) and item for item in manuscript_files
    ):
        raise ManifestError(f"{path}: manuscript_files must be a nonempty list of paths")
    if not manuscript_files:
        raise ManifestError(f"{path}: manuscript_files must not be empty")
    if not isinstance(entries, list) or not entries:
        raise ManifestError(f"{path}: entries must be a nonempty list")

    allowed_kinds = STATEMENT_ENVIRONMENTS | {"structure"}
    allowed_statuses = {"formalized", "intentionally_unformalized"}
    seen_sources: set[str] = set()
    for index, entry in enumerate(entries, 1):
        where = f"{path}: entry {index}"
        if not isinstance(entry, dict):
            raise ManifestError(f"{where} must be a mapping")
        source = entry.get("source")
        kind = entry.get("kind")
        status = entry.get("status")
        lean = entry.get("lean", [])
        if not isinstance(source, str) or not source:
            raise ManifestError(f"{where}: source must be a nonempty string")
        if source in seen_sources:
            raise ManifestError(f"{where}: duplicate source {source!r}")
        seen_sources.add(source)
        if kind not in allowed_kinds:
            raise ManifestError(f"{where}: kind must be one of {sorted(allowed_kinds)}")
        if status not in allowed_statuses:
            raise ManifestError(f"{where}: status must be one of {sorted(allowed_statuses)}")
        if isinstance(lean, str):
            lean = [lean]
            entry["lean"] = lean
        if not isinstance(lean, list) or not all(isinstance(name, str) and name for name in lean):
            raise ManifestError(f"{where}: lean must be a list of nonempty declaration names")
        if status == "formalized" and not lean:
            raise ManifestError(f"{where}: a formalized entry needs at least one Lean declaration")
        if status == "intentionally_unformalized" and lean:
            raise ManifestError(f"{where}: an intentionally unformalized entry must have no Lean names")
        if "headline" in entry and not isinstance(entry["headline"], bool):
            raise ManifestError(f"{where}: headline must be true or false")
        if kind == "structure" and re.match(r"^(?:thm|def):", source):
            raise ManifestError(f"{where}: a structure needs a synthetic, non-label source identifier")
        if kind != "structure" and not re.match(r"^(?:thm|def):", source):
            raise ManifestError(
                f"{where}: a labelled declaration source must begin with 'thm:' or 'def:'"
            )
    return manuscript_files, entries


def strip_tex_comments(text: str) -> str:
    lines: list[str] = []
    for line in text.splitlines(keepends=True):
        cut = len(line)
        for index, char in enumerate(line):
            if char == "%" and (index == 0 or line[index - 1] != "\\"):
                cut = index
                break
        ending = "\n" if line.endswith("\n") else ""
        lines.append(line[:cut] + ending)
    return "".join(lines)


def scan_paper_file(path: Path) -> list[PaperDeclaration]:
    text = strip_tex_comments(path.read_text(encoding="utf-8"))
    declarations: list[PaperDeclaration] = []
    for begin in BEGIN_RE.finditer(text):
        kind = begin.group(1)
        end_marker = rf"\\end\{{{kind}\}}"
        end = re.search(end_marker, text[begin.end() :])
        if end is None:
            line = text.count("\n", 0, begin.start()) + 1
            raise ManifestError(f"{path}:{line}: missing \\end{{{kind}}}")
        body_end = begin.end() + end.start()
        labels = LABEL_RE.findall(text[begin.end() : body_end])
        line = text.count("\n", 0, begin.start()) + 1
        if not labels:
            raise ManifestError(
                f"{path}:{line}: {kind} environment has no primary thm:/def: label"
            )
        if len(labels) != 1:
            raise ManifestError(
                f"{path}:{line}: {kind} environment has multiple primary labels: {labels}"
            )
        declarations.append(PaperDeclaration(labels[0], kind, path, line))
    return declarations


def appendix_lean_section(path: Path) -> str:
    text = strip_tex_comments(path.read_text(encoding="utf-8"))
    heading = re.search(r"\\section\{The Lean formalisations\}", text)
    if heading is None:
        raise ManifestError(f"{path}: cannot find the Appendix B Lean-formalisations section")
    following = re.search(r"\\section\{", text[heading.end() :])
    end = heading.end() + following.start() if following else len(text)
    return text[heading.start() : end].replace(r"\_", "_")


def appendix_code_identifiers(text: str) -> set[str]:
    contents = re.findall(r"\\(?:texttt|leanname)\{([^{}]*)\}", text)
    identifiers: set[str] = set()
    for content in contents:
        identifiers.update(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", content))
    return identifiers


def contains_lean_terminal(identifiers: set[str], name: str) -> bool:
    terminal = name.rsplit(".", 1)[-1]
    return any(identifier == name or identifier.rsplit(".", 1)[-1] == terminal for identifier in identifiers)


def strip_lean_comments(text: str) -> str:
    """Remove line and nested block comments while preserving line boundaries."""

    out: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if not in_string and pair == "/-":
            block_depth = 1
            out.extend("  ")
            index += 2
            continue
        if not in_string and pair == "--":
            while index < len(text) and text[index] != "\n":
                out.append(" ")
                index += 1
            continue
        if char == '"' and (index == 0 or text[index - 1] != "\\"):
            in_string = not in_string
        out.append(char)
        index += 1
    return "".join(out)


def scan_lean_file(path: Path) -> list[LeanDeclaration]:
    text = strip_lean_comments(path.read_text(encoding="utf-8"))
    scopes: list[tuple[str, list[str]]] = []
    declarations: list[LeanDeclaration] = []
    for line_no, line in enumerate(text.splitlines(), 1):
        namespace_match = re.match(r"^\s*namespace\s+([^\s]+)\s*$", line)
        if namespace_match:
            scopes.append(("namespace", namespace_match.group(1).split(".")))
            continue
        if re.match(r"^\s*section(?:\s+[^\s]+)?\s*$", line):
            scopes.append(("section", []))
            continue
        if re.match(r"^\s*mutual\s*$", line):
            scopes.append(("mutual", []))
            continue
        if re.match(r"^\s*end(?:\s+[^\s]+)?\s*$", line):
            if scopes:
                scopes.pop()
            continue

        match = DECL_RE.match(line)
        if not match:
            continue
        kind, raw_name = match.groups()
        namespace = [piece for scope, parts in scopes if scope == "namespace" for piece in parts]
        if raw_name.startswith("_root_."):
            name = raw_name.removeprefix("_root_.")
        else:
            name = ".".join(namespace + [raw_name])
        declarations.append(LeanDeclaration(name, kind, path, line_no))
    return declarations


def endpoint_spans(path: Path) -> dict[str, str]:
    text = strip_lean_comments(path.read_text(encoding="utf-8"))
    matches = list(AUDIT_DECL_RE.finditer(text))
    spans: dict[str, str] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        spans[match.group(1)] = text[match.start() : end]
    return spans


def main() -> int:
    script = Path(__file__).resolve()
    default_lean_root = script.parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=default_lean_root / "paper-correspondence.yaml",
        help="paper correspondence manifest (default: lean/paper-correspondence.yaml)",
    )
    parser.add_argument(
        "--lean-root",
        type=Path,
        default=default_lean_root,
        help="Lean project root (default: inferred from this script)",
    )
    args = parser.parse_args()
    manifest_path = args.manifest.resolve()
    lean_root = args.lean_root.resolve()
    repo_root = lean_root.parent

    errors: list[str] = []
    warnings: list[str] = []
    try:
        data = load_manifest(manifest_path)
        manuscript_files, entries = validate_manifest(data, manifest_path)
    except (OSError, ManifestError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2

    paper_declarations: dict[str, PaperDeclaration] = {}
    for relative in manuscript_files:
        path = repo_root / relative
        if not path.is_file():
            errors.append(f"manifest manuscript file does not exist: {relative}")
            continue
        try:
            found = scan_paper_file(path)
        except ManifestError as exc:
            errors.append(str(exc))
            continue
        for declaration in found:
            previous = paper_declarations.get(declaration.label)
            if previous:
                errors.append(
                    f"duplicate paper label {declaration.label!r}: "
                    f"{previous.file}:{previous.line} and {declaration.file}:{declaration.line}"
                )
            else:
                paper_declarations[declaration.label] = declaration

    manifest_labels = {
        entry["source"]: entry
        for entry in entries
        if re.match(r"^(?:thm|def):", entry["source"])
    }
    missing = sorted(set(paper_declarations) - set(manifest_labels))
    extra = sorted(set(manifest_labels) - set(paper_declarations))
    if missing:
        errors.append("paper declarations missing from manifest: " + ", ".join(missing))
    if extra:
        errors.append("manifest labels not found in statement environments: " + ", ".join(extra))
    for label in sorted(set(paper_declarations) & set(manifest_labels)):
        paper_kind = paper_declarations[label].kind
        manifest_kind = manifest_labels[label]["kind"]
        if paper_kind != manifest_kind:
            errors.append(
                f"{label}: manifest kind {manifest_kind!r} does not match paper environment "
                f"{paper_kind!r}"
            )

    appendix_path = repo_root / "appendices.tex"
    try:
        appendix_text = appendix_lean_section(appendix_path)
        appendix_identifiers = appendix_code_identifiers(appendix_text)
        for entry in entries:
            source = entry["source"]
            if re.match(r"^(?:thm|def):", source) and source not in appendix_text:
                errors.append(f"Appendix B does not mention manifest source label: {source}")
            if entry["status"] == "formalized":
                for name in entry.get("lean", []):
                    if not contains_lean_terminal(appendix_identifiers, name):
                        errors.append(
                            "Appendix B does not mention mapped Lean declaration "
                            f"{name} (terminal name {name.rsplit('.', 1)[-1]!r})"
                        )
    except (OSError, ManifestError) as exc:
        errors.append(str(exc))

    lean_declarations: dict[str, list[LeanDeclaration]] = {}
    for path in lean_root.rglob("*.lean"):
        relative_parts = path.relative_to(lean_root).parts
        if ".lake" in relative_parts or "Archive" in relative_parts:
            continue
        for declaration in scan_lean_file(path):
            lean_declarations.setdefault(declaration.name, []).append(declaration)

    mapped_names = {
        name
        for entry in entries
        if entry["status"] == "formalized"
        for name in entry.get("lean", [])
    }
    for name in sorted(mapped_names):
        matches = lean_declarations.get(name, [])
        if not matches:
            errors.append(f"mapped Lean name is not found as a source declaration: {name}")

    comparator_path = lean_root / "comparator.json"
    comparator: dict[str, Any] = {}
    try:
        comparator = json.loads(comparator_path.read_text(encoding="utf-8"))
        comparator_names = comparator["theorem_names"]
    except (OSError, json.JSONDecodeError, KeyError) as exc:
        errors.append(f"cannot read comparator theorem names from {comparator_path}: {exc}")
        comparator_names = []
    if not isinstance(comparator_names, list) or not all(
        isinstance(name, str) for name in comparator_names
    ):
        errors.append("comparator theorem_names must be a list of strings")
        comparator_names = []
    if len(comparator_names) != 13:
        errors.append(f"comparator must list exactly 13 headline theorems, found {len(comparator_names)}")
    if len(set(comparator_names)) != len(comparator_names):
        errors.append("comparator theorem_names contains duplicates")
    if comparator.get("definition_names") != []:
        errors.append("comparator definition_names must be the empty list")
    comparator_set = set(comparator_names)
    manifest_headlines = {
        name for entry in entries if entry.get("headline") for name in entry.get("lean", [])
    }
    if manifest_headlines != comparator_set:
        errors.append(
            "manifest headline declarations differ from comparator theorem_names; "
            f"only in manifest={sorted(manifest_headlines - comparator_set)}, "
            f"only in comparator={sorted(comparator_set - manifest_headlines)}"
        )

    challenge_path = lean_root / "Challenge.lean"
    solution_path = lean_root / "Solution.lean"
    challenge_spans = endpoint_spans(challenge_path)
    solution_spans = endpoint_spans(solution_path)
    challenge_names = {f"Challenge.{name}" for name in challenge_spans}
    solution_names = {f"Challenge.{name}" for name in solution_spans}
    if challenge_names != comparator_set:
        errors.append(
            "Challenge audit declarations differ from comparator theorem_names; "
            f"only in Challenge={sorted(challenge_names - comparator_set)}, "
            f"only in comparator={sorted(comparator_set - challenge_names)}"
        )
    if solution_names != comparator_set:
        errors.append(
            "Solution audit declarations differ from comparator theorem_names; "
            f"only in Solution={sorted(solution_names - comparator_set)}, "
            f"only in comparator={sorted(comparator_set - solution_names)}"
        )
    challenge_source_declarations = scan_lean_file(challenge_path)
    challenge_propositions = {
        declaration.name
        for declaration in challenge_source_declarations
        if declaration.kind in {"theorem", "lemma"}
    }
    if challenge_propositions != comparator_set:
        errors.append(
            "every theorem or lemma in Challenge.lean must be one of the 13 audited endpoints; "
            f"extra={sorted(challenge_propositions - comparator_set)}, "
            f"missing={sorted(comparator_set - challenge_propositions)}"
        )
    challenge_axioms = [
        declaration for declaration in challenge_source_declarations if declaration.kind == "axiom"
    ]
    if challenge_axioms:
        errors.append(
            "Challenge.lean must not declare axioms: "
            + ", ".join(declaration.name for declaration in challenge_axioms)
        )
    for name, span in challenge_spans.items():
        if not re.search(r"\bsorry\b", span):
            errors.append(f"Challenge.{name} is not a theorem hole containing sorry")
    for name, span in solution_spans.items():
        if re.search(r"\bsorry\b", span):
            errors.append(f"Solution proof Challenge.{name} contains sorry")
        if not re.search(r":=\s*by\b", span):
            errors.append(f"Solution proof Challenge.{name} does not have an explicit ':= by' body")

    formalization_path = lean_root / "formalization.yaml"
    try:
        formalization_text = formalization_path.read_text(encoding="utf-8")
        alignment_names = set(
            re.findall(r'^\s+lean:\s*["\'](Challenge\.audit_[^"\']+)["\']\s*$', formalization_text, re.M)
        )
        if alignment_names != comparator_set:
            errors.append(
                "formalization.yaml alignment differs from comparator theorem_names; "
                f"only in alignment={sorted(alignment_names - comparator_set)}, "
                f"only in comparator={sorted(comparator_set - alignment_names)}"
            )
    except OSError as exc:
        errors.append(f"cannot read {formalization_path}: {exc}")

    structure_entries = [entry for entry in entries if entry["kind"] == "structure"]
    if not structure_entries:
        warnings.append("manifest contains no unnumbered structure entries")

    print(
        "STATIC CHECK ONLY: declaration lookup scans source text; it does not elaborate Lean "
        "or compile LaTeX."
    )
    print(
        f"Scanned {len(paper_declarations)} labelled paper declarations, "
        f"{len(structure_entries)} manifest structure entries, and "
        f"{len(lean_declarations)} distinct Lean source declarations."
    )
    print(
        "NOTE: static source inspection cannot establish that Challenge definitions are "
        "dependency-minimal; that requires semantic review with Lean's elaborated environment."
    )
    for warning in warnings:
        print(f"WARNING: {warning}", file=sys.stderr)
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    if errors:
        print(f"FAILED with {len(errors)} error(s).", file=sys.stderr)
        return 1
    print(
        f"OK: all {len(paper_declarations)} labelled declarations have exactly one manifest "
        "entry, all mapped Lean names were found, and the 13 audit endpoints agree."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
