#!/usr/bin/env python3
"""Generate the Lean source links of the thesis.

Input
  tex/preamble/lean_links_map.tsv   label <TAB> Lean declaration <TAB> scope
      scope is one of
        full        the declaration proves the thesis statement (formal variant)
        component   the declaration proves a component of the statement
        definition  the declaration encodes the defined object
        equation    the label is an equation label (link on the equation number)

Output
  tex/preamble/lean_links_generated.tex   \\DeclareLeanResult / \\DeclareLeanEquation
  tex/tables/lean_coverage.tex            one row per numbered Lean reference

Each declaration is found by its full name in formalization/, so the line
numbers always come from the Lean sources. References are numbered in order of
first appearance of \\LeanResult{label} in the thesis. All links are pinned to
one Git revision (default: the last commit that changed the Lean sources); the script refuses to run when the Lean
sources of the working tree differ from that revision, because the line numbers
would then not match the linked files.

Usage
  python3 tex/scripts/generate_lean_links.py [--rev REV] [--allow-dirty] [--check]
"""
import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TEX = ROOT / "tex"
LEAN = ROOT / "formalization"
MAP = TEX / "preamble" / "lean_links_map.tsv"
OUT_LINKS = TEX / "preamble" / "lean_links_generated.tex"
OUT_TABLE = TEX / "tables" / "lean_coverage.tex"
REPO_URL = "https://github.com/JayPiZimmermann/A-Structural-Approach-to-Explainable-Deep-Learning"
LEAN_DIRS = ("HiddenMonotonicity", "Thesis")
SCOPES = {"full": "Lean variant", "component": "Lean components",
          "definition": "Lean", "equation": "Lean"}
ENVIRONMENTS = {
    "theoremenv": "Theorem", "lemmaenv": "Lemma", "proposition": "Proposition",
    "corollary": "Corollary", "definition": "Definition",
    "observation": "Observation", "remark": "Remark", "remarkenv": "Remark",
    "claim": "Claim",
}
SECTIONING = ("chapter", "section", "subsection", "subsubsection")

DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+"
    r"([^\s:({\[]+)")


def fail(message):
    sys.exit(f"generate_lean_links: {message}")


# ---------------------------------------------------------------- Lean index

def index_lean():
    """Full declaration name -> (path relative to the repository, line)."""
    index, duplicates = {}, set()
    for directory in LEAN_DIRS:
        for path in sorted((LEAN / directory).rglob("*.lean")):
            scopes = []  # (name or None for an anonymous section, is_namespace)
            for number, line in enumerate(path.read_text().splitlines(), 1):
                opened = re.match(r"^\s*(namespace|section)\b\s*(\S*)", line)
                if opened:
                    scopes.append((opened.group(2) or None, opened.group(1) == "namespace"))
                    continue
                closed = re.match(r"^\s*end\b\s*(\S*)\s*$", line)
                if closed and scopes:
                    scopes.pop()
                    continue
                declared = DECLARATION.match(line)
                if not declared:
                    continue
                prefix = [name for name, is_namespace in scopes if is_namespace]
                name = declared.group(1)
                full = name[len("_root_."):] if name.startswith("_root_.") else ".".join(prefix + [name])
                if full in index:
                    duplicates.add(full)
                index[full] = (path.relative_to(ROOT).as_posix(), number)
    return index, duplicates


# ---------------------------------------------------------------- TeX scan

def strip_comment(line):
    return re.sub(r"(?<!\\)%.*", "", line)


def tex_files():
    """Thesis source files in document order, following \\input and \\include."""
    generated = {OUT_LINKS.resolve(), OUT_TABLE.resolve()}
    ordered, seen = [], set()

    def visit(path):
        path = path if path.suffix else path.with_suffix(".tex")
        if not path.exists() or path.resolve() in seen or path.resolve() in generated:
            return
        seen.add(path.resolve())
        ordered.append(path)
        for line in path.read_text().splitlines():
            for name in re.findall(r"\\(?:input|include|appinput\w*)\{([^}]+)\}", strip_comment(line)):
                visit(TEX / name)

    visit(TEX / "main.tex")
    return ordered


def scan_tex():
    """Return (references, labels).

    references: label -> (kind, anchor label) of the first \\LeanResult{label},
    in order of first appearance; kind is the printed name of the enclosing
    theorem-like environment, or "Section".
    labels: every \\label defined in the thesis (aliases excluded).
    """
    references, labels = {}, set()
    for path in tex_files():
        environments = []          # [name, label or None]
        section_label = None
        awaiting_section_label = 0  # lines left in which a section label may follow
        for line in path.read_text().splitlines():
            line = strip_comment(line)
            awaiting_section_label = max(0, awaiting_section_label - 1)
            tokens = re.finditer(
                r"\\begin\{(\w+)\}|\\end\{(\w+)\}|\\label\{([^}]+)\}|"
                r"\\(?:LeanResult|leandecl)\{([^}]+)\}|\\(" + "|".join(SECTIONING) + r")\*?[\[{]",
                line)
            pending = []           # references waiting for the label of their heading
            for token in tokens:
                begin, end, label, reference, sectioning = token.groups()
                if begin in ENVIRONMENTS:
                    environments.append([begin, None])
                elif end in ENVIRONMENTS and environments:
                    environments.pop()
                elif sectioning:
                    awaiting_section_label = 2
                elif label:
                    labels.add(label)
                    if environments and environments[-1][1] is None:
                        environments[-1][1] = label
                        for key in pending:
                            references[key] = (ENVIRONMENTS[environments[-1][0]], label)
                        pending = []
                    elif awaiting_section_label:
                        section_label, awaiting_section_label = label, 0
                elif reference and "#" not in reference and reference not in references:
                    if environments and environments[-1][1] is None:
                        references[reference] = None
                        pending.append(reference)
                    elif environments:
                        references[reference] = (ENVIRONMENTS[environments[-1][0]], environments[-1][1])
                    else:
                        references[reference] = ("Section", section_label)
            for key in pending:
                fail(f"\\LeanResult{{{key}}} stands in a heading without a \\label on the same line ({path})")
    return references, labels


# ---------------------------------------------------------------- output

def tex_escape(text):
    return text.replace("_", r"\_")


def declaration_tex(name):
    return r".\allowbreak ".join(tex_escape(part) for part in name.split("."))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--rev", help="Git revision the links are pinned to "
                        "(default: the last commit that changed the Lean sources)")
    parser.add_argument("--allow-dirty", action="store_true",
                        help="write the files although the Lean sources differ from the revision")
    parser.add_argument("--check", action="store_true", help="verify only; write nothing")
    arguments = parser.parse_args()

    if not arguments.rev:
        arguments.rev = subprocess.run(
            ["git", "-C", str(ROOT), "log", "-1", "--format=%H", "--",
             *[f"formalization/{d}" for d in LEAN_DIRS]],
            stdout=subprocess.PIPE, universal_newlines=True).stdout.strip() or "HEAD"
    revision = subprocess.run(["git", "-C", str(ROOT), "rev-parse", arguments.rev],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              universal_newlines=True)
    if revision.returncode:
        fail(f"unknown revision {arguments.rev}")
    revision = revision.stdout.strip()
    dirty = subprocess.run(["git", "-C", str(ROOT), "diff", "--quiet", revision, "--",
                            *[f"formalization/{d}" for d in LEAN_DIRS]]).returncode != 0
    untracked = subprocess.run(["git", "-C", str(ROOT), "ls-files", "--others", "--exclude-standard",
                                *[f"formalization/{d}" for d in LEAN_DIRS]],
                               stdout=subprocess.PIPE, universal_newlines=True).stdout.strip()
    if (dirty or untracked) and not arguments.allow_dirty:
        fail(f"the Lean sources differ from {revision[:8]}; commit them first or pass --allow-dirty")

    entries = []
    for number, line in enumerate(MAP.read_text().splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 3 or fields[2] not in SCOPES:
            fail(f"{MAP.name}:{number}: expected label<TAB>declaration<TAB>scope")
        entries.append(tuple(fields))
    keys = [label for label, _, _ in entries]
    if len(set(keys)) != len(keys):
        fail("duplicate labels in the map: " + ", ".join(sorted({k for k in keys if keys.count(k) > 1})))

    index, duplicates = index_lean()
    references, labels = scan_tex()
    numbers = {label: position for position, label in enumerate(references, 1)}

    problems = []
    for label in references:
        if label not in keys:
            problems.append(f"\\LeanResult{{{label}}} has no entry in the map")
    for label, declaration, scope in entries:
        if declaration not in index:
            problems.append(f"{label}: declaration {declaration} not found in formalization/")
        elif declaration in duplicates:
            problems.append(f"{label}: declaration name {declaration} is ambiguous")
        if scope == "equation":
            if label not in labels:
                problems.append(f"{label}: equation label is not defined in the thesis (dead entry)")
        elif label not in references:
            problems.append(f"{label}: no \\LeanResult{{{label}}} in the thesis (dead entry)")
    if problems:
        fail("\n  " + "\n  ".join(problems))

    base = f"{REPO_URL}/blob/{revision}"
    links = ["% Generated by scripts/generate_lean_links.py from preamble/lean_links_map.tsv; do not edit.",
             f"\\newcommand{{\\leanrevision}}{{{revision}}}",
             f"\\newcommand{{\\leanbase}}{{{base}}}"]
    for label, declaration, scope in entries:
        path, line = index[declaration]
        links.append(f"\\DeclareLeanResult{{{label}}}{{{base}/{path}\\#L{line}}}"
                     f"{{{declaration}}}{{{SCOPES[scope]}}}{{{numbers.get(label, 0)}}}")
        if scope == "equation":
            links.append(f"\\DeclareLeanEquation{{{label}}}{{{path}}}{{{line}}}")

    table = [
        "% Generated by scripts/generate_lean_links.py; one row per numbered Lean reference.",
        r"{\small",
        r"\begin{longtable}{@{}l l >{\raggedright\arraybackslash}p{0.66\linewidth}@{}}",
        r"\caption[Lean references and their coverage]{Numbered Lean references in order of appearance "
        r"and the linked declaration. An unmarked reference means that the declaration proves the thesis "
        r"statement in a formal variant with explicit hypotheses; $^{\mathrm c}$ marks a declaration that "
        r"proves a component of the statement, and $^{\mathrm d}$ one that encodes the defined object.}"
        r"\label{tab:lean_coverage}\\",
        r"\toprule", r"Reference & Thesis & Lean declaration \\", r"\midrule", r"\endfirsthead",
        r"\toprule", r"Reference & Thesis & Lean declaration \\", r"\midrule", r"\endhead",
        r"\bottomrule", r"\endfoot",
    ]
    by_label = {label: (declaration, scope) for label, declaration, scope in entries}
    for label, position in numbers.items():
        declaration, scope = by_label[label]
        path, line = index[declaration]
        kind, anchor = references[label]
        if anchor is None:
            fail(f"\\LeanResult{{{label}}} has no enclosing labelled statement or section")
        marker = {"component": r"$^{\mathrm c}$", "definition": r"$^{\mathrm d}$"}.get(scope, "")
        table.append(f"\\texttt{{Lean\\_{position}}}{marker} & {kind}~\\ref{{{anchor}}} & "
                     f"\\href{{{base}/{path}\\#L{line}}}{{\\texttt{{{declaration_tex(declaration)}}}}} \\\\")
    table += [r"\end{longtable}", "}"]

    if arguments.check:
        current = (OUT_LINKS.read_text(), OUT_TABLE.read_text())
        if current != ("\n".join(links) + "\n", "\n".join(table) + "\n"):
            fail("the generated files are out of date")
        print("generated files are up to date")
        return
    OUT_LINKS.write_text("\n".join(links) + "\n")
    OUT_TABLE.write_text("\n".join(table) + "\n")
    print(f"pinned {len(entries)} links ({len(numbers)} numbered references) to {revision[:8]}"
          + (" [Lean sources differ from this revision]" if dirty or untracked else ""))


if __name__ == "__main__":
    main()
