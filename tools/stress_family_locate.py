#!/usr/bin/env python3
"""Helpers for tools/stress_family.sh. Two questions, answered exactly.

  upstream <scratch_lean_root> <tracked_lean_root> <n> <relfile>
      Is every file the planted file imports (transitively, inside the case
      A<n>) byte-identical to the tracked one? The stress test compiles the
      planted file against the BUILT tracked modules; that is a test of the
      planted defect only if nothing upstream of it changed.

  located <file> <decl>[,<decl>...]   (Lean's output on stdin)
      Did Lean report at least one error, and is EVERY error inside the
      declarations where the defect was planted? An error elsewhere would mean
      the mutation broke something it was not meant to, and the rejection
      would not be evidence about the planted claim.
"""
import os
import re
import sys


def case_imports(path, n):
    pat = re.compile(r"^import ChiquipoliFamily\.A%d\.(\w+)\s*$" % n)
    with open(path, encoding="utf-8") as f:
        return [m.group(1) for m in (pat.match(l) for l in f) if m]


def upstream(scratch, tracked, n, rel):
    n = int(n)
    casedir = os.path.join("ChiquipoliFamily", "A%d" % n)
    seen, todo, bad = set(), case_imports(os.path.join(scratch, rel), n), []
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        seen.add(mod)
        a = os.path.join(scratch, casedir, mod + ".lean")
        b = os.path.join(tracked, casedir, mod + ".lean")
        with open(a, "rb") as fa, open(b, "rb") as fb:
            if fa.read() != fb.read():
                bad.append(mod)
        todo.extend(case_imports(a, n))
    if bad:
        print("upstream of the planted file differs from the tracked tree: " + ", ".join(sorted(bad)))
        return 1
    print("%d upstream modules identical to the tracked, built ones" % len(seen))
    return 0


DECL = re.compile(r"^(theorem|lemma|noncomputable def|def|@\[|/--|end |open |instance|example)")


def located(path, decls):
    decls = decls.split(",")
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    ranges = {}
    for d in decls:
        start = next((i for i, l in enumerate(lines, 1)
                      if re.match(r"^(theorem|lemma) %s(\s|$)" % re.escape(d), l)), None)
        if start is None:
            print("planted declaration %s not found in %s" % (d, path))
            return 1
        end = next((i - 1 for i, l in enumerate(lines, 1) if i > start and DECL.match(l)), len(lines))
        ranges[d] = (start, end)
    errs = [int(m.group(1)) for m in re.finditer(r":(\d+):\d+: error", sys.stdin.read())]
    if not errs:
        print("Lean reported no error")
        return 1
    outside = [e for e in errs if not any(a <= e <= b for a, b in ranges.values())]
    if outside:
        print("errors outside the planted declaration(s), at lines %s" % outside[:5])
        return 1
    print("%d error(s), all inside %s" % (len(errs), ", ".join(
        "%s (lines %d-%d)" % (d, a, b) for d, (a, b) in ranges.items())))
    return 0


if __name__ == "__main__":
    cmd, args = sys.argv[1], sys.argv[2:]
    sys.exit(upstream(*args) if cmd == "upstream" else located(*args))
