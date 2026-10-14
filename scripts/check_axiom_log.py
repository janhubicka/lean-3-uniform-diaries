#!/usr/bin/env python3
"""Check all #print axioms statements, not just an arbitrary nonempty subset."""
from pathlib import Path
import re
import sys

output = Path(sys.argv[1]).read_text(encoding="utf-8")
source = Path(sys.argv[2]).read_text(encoding="utf-8")
expected = sum(line.lstrip().startswith("#print axioms ") for line in source.splitlines())
reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output, re.S)
no_axioms = len(re.findall(r"does not depend on any axioms", output))
actual_count = len(reports) + no_axioms
if actual_count != expected:
    raise SystemExit(f"FAIL: axiom reports {actual_count} != expected {expected}")
if "sorryAx" in output:
    raise SystemExit("FAIL: sorryAx dependency")
allowed = {"propext", "Classical.choice", "Quot.sound"}
actual = {name.strip() for report in reports
          for name in report.split(",") if name.strip()}
unexpected = actual - allowed
if unexpected:
    raise SystemExit("FAIL: unexpected axioms " + ", ".join(sorted(unexpected)))
print(f"PASS: all {expected} theorem endpoints checked; "
      f"only expected axioms {sorted(actual)}")
