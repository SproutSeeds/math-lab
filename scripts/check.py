"""Build math-lab and record a verification receipt in results/check.json.

Runs `lake build MathLab` (a clean rebuild of our files with --rehash is not needed: Lake replays the
messages of cached builds), then reads every `#print axioms` line and counts theorems, `sorry` and
warnings per file of ours. Vendored files under ThirdParty/ are checked by building them; their own
lint warnings are reported separately and not edited.
Usage: python3 scripts/check.py
"""
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

run = subprocess.run(["lake", "build", "MathLab"], cwd=ROOT, capture_output=True, text=True)
text = run.stdout + run.stderr
axioms = {k: [a.strip() for a in v.split(",") if a.strip()]
          for k, v in re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", text)}
files = {}
for src in sorted((ROOT / "MathLab").rglob("*.lean")):
    rel = str(src.relative_to(ROOT))
    body = src.read_text()
    files[rel] = {
        "sha256": hashlib.sha256(body.encode()).hexdigest(),
        "theorems": len(re.findall(r"^theorem ", body, re.M)),
        "sorry": len(re.findall(r"\bsorry\b", body)),
        "warnings": len(re.findall(r"^warning: (?:\S*/)?" + re.escape(rel), text, re.M)),
        "errors": len(re.findall(r"^error: (?:\S*/)?" + re.escape(rel), text, re.M)),
    }
vendored_warnings = len(re.findall(r"^warning: (?:\S*/)?ThirdParty/", text, re.M))
version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
record = {
    "checked_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    "lean_version": version,
    "mathlib_commit": mathlib.get("rev"),
    "returncode": run.returncode,
    "files": files,
    "theorems_total": sum(f["theorems"] for f in files.values()),
    "axioms": axioms,
    "standard_axioms_only": all(set(a) <= STANDARD for a in axioms.values()),
    "vendored_lint_warnings": vendored_warnings,
}
record["pass"] = (run.returncode == 0 and record["standard_axioms_only"] and len(axioms) > 0
                  and all(f["sorry"] == 0 and f["errors"] == 0 for f in files.values()))
(ROOT / "results").mkdir(exist_ok=True)
(ROOT / "results" / "check.json").write_text(json.JSONEncoder(indent=2).encode(record) + "\n")
print(json.JSONEncoder(indent=2).encode({k: record[k] for k in
      ("pass", "returncode", "theorems_total", "standard_axioms_only", "vendored_lint_warnings")}))
for rel, f in files.items():
    print(f"  {rel}: {f['theorems']} theorems, {f['warnings']} warnings, {f['sorry']} sorry")
