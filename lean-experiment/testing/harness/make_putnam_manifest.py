#!/usr/bin/env python3
"""Generate the held-out putnam60 manifest — ONLY runnable after the
mechanical unlock (testing/FINAL_UNLOCK file + LEAN_FINAL_EVAL=1); see
testing/FROZEN.md. All access goes through datasets.load_putnam60(), which
enforces the guard and logs the unlock event.

(ported from rocq-mcp-evolve's make_test_manifest.py)
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import common
import datasets

recs = datasets.load_putnam60()  # raises unless unlocked
out = common.MANIFESTS / "putnam60.jsonl"
out.write_text("".join(json.dumps(r) + "\n" for r in recs))
print(f"wrote {len(recs)} records to {out} (held-out; single final run only)")
