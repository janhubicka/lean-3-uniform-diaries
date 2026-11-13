#!/usr/bin/env python3
"""Informational Lean import-dependency report (NOT a dead-code detector).

The main umbrella imports most source modules directly.  Therefore the
integrity gate's 'all modules reachable' check cannot establish that a module
is necessary for the manuscript.  This report counts genuine non-umbrella
imports and identifies *candidates* for manual paper-path review.

Never delete a module automatically from this output: theorem endpoints may be
intended directly for the paper, and counterexamples are valuable regression
certificates even without downstream imports.
"""
from collections import defaultdict
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
MODULES = [ROOT / "ThreeUniformDiaries.lean",
           *sorted((ROOT / "ThreeUniformDiaries").rglob("*.lean"))]
NAME = lambda p: ".".join(p.relative_to(ROOT).with_suffix("").parts)
modules = {NAME(p): p for p in MODULES}
incoming = defaultdict(set)
umbrella = "ThreeUniformDiaries"

for name, path in modules.items():
    # Lean imports are top-level lines.  This tool is informational; the
    # stricter source-integrity script already parses and checks all modules.
    for line in path.read_text(encoding="utf-8").splitlines():
        found = re.fullmatch(r"\s*import\s+([A-Za-z0-9_. ]+)\s*", line)
        if found:
            for target in found.group(1).split():
                if target in modules:
                    incoming[target].add(name)

others = sorted(n for n in modules if n != umbrella)
root_only = [n for n in others if incoming[n] == {umbrella}]
not_imported = [n for n in others if not incoming[n]]
used_by_other = [n for n in others if any(x != umbrella for x in incoming[n])]
counterexamples = [n for n in root_only if re.search(
    r"Counterexample|Obstruction|Collision|NoGo", n)]
conditional = [n for n in root_only if re.search(
    r"Conditional|Reduction|Interface|Compat|Audit|Legacy", n)]
print("Proof dependency hygiene report (informational; do not delete automatically)")
print(f"Local Lean modules (excluding umbrella): {len(others)}")
print(f"Imported by at least one NON-umbrella module: {len(used_by_other)}")
print(f"Imported ONLY by the umbrella: {len(root_only)}")
print(f"Not imported locally at all: {len(not_imported)}")
print(f"Root-only counterexample/obstruction/collision certificates: {len(counterexamples)}")
print(f"Root-only conditional/reduction/interface/audit candidates: {len(conditional)}")
print("Root-only conditional audit candidates (first 80):")
for name in conditional[:80]:
    print("  " + name)
print("Root-only negative-result certificates (retain unless reviewed):")
for name in counterexamples[:80]:
    print("  " + name)
print("No automatic deletion: leaf theorem modules may be paper endpoints.")
