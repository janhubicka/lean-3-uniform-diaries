#!/usr/bin/env python3
"""Audit the diary formalisation's direct use of lean-milliken.

This integration test ensures the project uses the published
general-tree theorem modules instead of duplicating their proofs or
maintaining transitional conditional adapter layers.

Run before Lake compilation. The pinned dependency and full Lean
CI subsequently check the actual declaration types and proof terms.
"""
from collections import defaultdict
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
sources = [
    root / "ThreeUniformDiaries.lean",
    *sorted((root / "ThreeUniformDiaries").rglob("*.lean")),
]
imports: dict[str, list[str]] = defaultdict(list)
for path in sources:
    rel = path.relative_to(root).as_posix()
    source = path.read_text(encoding="utf-8")
    for match in re.finditer(r"^\s*import\s+(Milliken(?:\.[A-Za-z0-9_]+)*)\s*$",
                             source, re.MULTILINE):
        imports[match.group(1)].append(rel)

print(f"Checked {len(sources)} diary Lean modules")
print(f"Distinct imported Milliken modules: {len(imports)}")
for module, sites in sorted(imports.items()):
    print(f"  {module}: {', '.join(sites)}")

legacy_upstream = (
    "Milliken.MillikenTheorem",
    "Milliken.Chapter6",
    "Milliken.Applications",
)
for module, sites in imports.items():
    if (module == "Milliken"
        or module in legacy_upstream
        or module.startswith("Milliken.HalpernLauchli.")):
        raise SystemExit(f"FAIL: obsolete fixed-alphabet Milliken import {module}: {sites}")

retired_local_modules = (
    "MillikenFiniteColour",
    "ATRGeneralMilliken",
    "ATRScalarMillikenTransfer",
    "ATRBoundaryMillikenApplication",
    "ScalarProtectedApproxRealization",
)
for module in retired_local_modules:
    if (root / "ThreeUniformDiaries" / f"{module}.lean").exists():
        raise SystemExit(f"FAIL: retained unused Milliken adapter {module}.lean")
    target = f"ThreeUniformDiaries.{module}"
    for path in sources:
        source = path.read_text(encoding="utf-8")
        if re.search(r"^\s*import\s+" + re.escape(target) + r"\s*$",
                     source, re.MULTILINE):
            raise SystemExit(f"FAIL: obsolete adapter imported in {path}: {target}")

required = (
    "Milliken.GeneralTree.FixedStemBoundaryHL",
    "Milliken.GeneralTree.UnconditionalHLAPI",
)
for module in required:
    if module not in imports:
        raise SystemExit(f"FAIL: public general-tree import {module} has no direct client")

print("PASS: diary proofs import only the reusable general-tree Milliken API")
