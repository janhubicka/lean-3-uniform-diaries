#!/usr/bin/env python3
"""Reject source-level admissions or locally declared proof axioms.

Unlike checking only chosen theorem endpoints, this checks *every*
Lean source in the library. Lean nested comments and double-quoted
strings are skipped so examples in documentation do not trigger it.
This complements, and does not replace, `#print axioms`.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = re.compile(r"\b(sorry|sorryAx|admit)\b|\b(axiom|constant)\s+[\w'.]+")
problems = []


def executable_text(text: str) -> str:
    out = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif in_string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            elif text[i] == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("--", i):
            e = text.find("\n", i)
            if e < 0:
                e = len(text)
            out.extend(" " * (e - i))
            i = e
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or in_string:
        raise ValueError("unterminated comment/string")
    return "".join(out)


files = sorted((ROOT / "ThreeUniformDiaries").rglob("*.lean")) + [ROOT / "ThreeUniformDiaries.lean"]
for path in files:
    src = path.read_text(encoding="utf-8")
    try:
        code = executable_text(src)
    except ValueError as exc:
        problems.append(f"{path.relative_to(ROOT)}: {exc}")
        continue
    for match in TARGET.finditer(code):
        line = code.count("\n", 0, match.start()) + 1
        problems.append(f"{path.relative_to(ROOT)}:{line}: {match.group(0)}")

if problems:
    raise SystemExit("FAIL: untrusted proof admissions / local axioms:\n" +
                     "\n".join(problems))
print(f"PASS: {len(files)} Lean files contain no sorry, admit, locally declared axiom or constant")

# A successful umbrella build must not hide uncompiled local modules.
# Missing imports are a common way old exploratory proof branches evade
# Lean kernel/axiom verification even though the source scan sees them.
modules = {
    ".".join(path.relative_to(ROOT).with_suffix("").parts): path
    for path in files
}
imports = {}
for module, path in modules.items():
    code = executable_text(path.read_text(encoding="utf-8"))
    imports[module] = {
        name
        for line in code.splitlines()
        if line.lstrip().startswith("import ")
        for name in line.strip()[len("import "):].split()
        if name in modules
    }
reachable = set()
frontier = ["ThreeUniformDiaries"]
while frontier:
    module = frontier.pop()
    if module in reachable:
        continue
    reachable.add(module)
    frontier.extend(imports.get(module, set()) - reachable)
orphaned = sorted(modules.keys() - reachable)
if orphaned:
    raise SystemExit("FAIL: Lean modules not compiled by default library target:\n"
                     + "\n".join(orphaned))
print(f"PASS: all {len(files)} local Lean modules are reachable from ThreeUniformDiaries")
