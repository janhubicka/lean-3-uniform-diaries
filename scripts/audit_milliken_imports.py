#!/usr/bin/env python3
"""Inventory the *actual* lean-milliken modules used by the ATR project.

Run before the Lean build so obsolete compatibility modules can be removed
from the upstream library without speculating about downstream imports.
Only source imports count as dependencies; comments are merely context.
"""
from collections import defaultdict
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
paths = [root / "ThreeUniformDiaries.lean", *sorted((root / "ThreeUniformDiaries").rglob("*.lean"))]
imports: dict[str, list[str]] = defaultdict(list)
legacy: dict[str, list[str]] = defaultdict(list)
for path in paths:
    s = path.read_text(encoding="utf-8")
    relative = path.relative_to(root).as_posix()
    for m in re.finditer(r"^\s*import\s+(Milliken(?:\.[A-Za-z0-9_]+)*)\s*$", s, re.M):
        imports[m.group(1)].append(relative)
    for m in re.finditer(
        r"\bMilliken\.(?:Chapter6|HalpernLauchli|StrongEmbedding|StrongTreeSpace|Applications|MillikenTheorem)\b",
        s,
    ):
        line = s.count("\n", 0, m.start()) + 1
        legacy[relative].append(f"{m.group()}:{line}")

print(f"ATR source files: {len(paths)}")
print(f"Distinct directly imported lean-milliken modules: {len(imports)}")
for module, owners in sorted(imports.items()):
    print(f"  {module}: {', '.join(owners)}")
print(f"Legacy namespace mentions (include comments): {sum(map(len, legacy.values()))}")
for path, hits in sorted(legacy.items()):
    print(f"  {path}: {', '.join(hits)}")

# No upstream homogeneous theorem import should be needed by the
# ATR-facing proof; this is the precise condition for deleting those APIs.
for module, owners in imports.items():
    if module == "Milliken" or module in (
        "Milliken.MillikenTheorem",
        "Milliken.Chapter6",
        "Milliken.Applications",
        "Milliken.Applications.PublishedInterfaces",
        "Milliken.Applications.FiniteColour",
    ) or module.startswith("Milliken.HalpernLauchli."):
        raise SystemExit(
            f"ATR still imports obsolete homogeneous API {module}: {owners}"
        )
print("PASS: no direct imports of homogeneous compatibility proof")
