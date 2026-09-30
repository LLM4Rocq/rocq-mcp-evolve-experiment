#!/usr/bin/env python3
"""Build the debug-only smoke manifest under <repo>/testing/data/manifests/.

(ported from rocq-mcp-evolve, restructured: rocq-mcp-evolve built several dev
manifests here from the disjoint workbook/miniF2F-valid pools; the Lean port
has no separate dev pool -- see datasets.py's module docstring -- so this
script's only remaining job is smoke2)

Output:
  smoke2.jsonl   2 named putnam60 problems (putnam_1977_a3, putnam_1988_b1),
                 UNGUARDED by design (debug only; never a held-out result).

Never touches the guarded load_putnam60() path (see harness/datasets.py).
"""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import datasets

OUT_DIR = os.path.join(datasets.REPO_ROOT, "data", "manifests")


def write_jsonl(name, records):
    path = os.path.join(OUT_DIR, name)
    with open(path, "w", encoding="utf-8") as f:
        for r in records:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    print(f"wrote {path}: {len(records)} records")
    return path


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    smoke2 = datasets.smoke2_records()
    write_jsonl("smoke2.jsonl", smoke2)
    print("\n== summary ==")
    for r in smoke2:
        print(f"  {r['problem_id']}  difficulty={r['difficulty']}  path={r['path']}")
    ids = [r["problem_id"] for r in smoke2]
    assert len(ids) == len(set(ids)), "duplicate problem_ids in smoke2"


if __name__ == "__main__":
    main()
