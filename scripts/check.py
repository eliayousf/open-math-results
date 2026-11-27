"""Build the Lean library and verify each recorded result."""

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(*args):
    subprocess.run(args, cwd=ROOT, check=True)


def audit_axioms(modules):
    declarations = [f"{module}.main" for module in modules]
    with tempfile.TemporaryDirectory() as directory:
        audit = Path(directory) / "Audit.lean"
        imports = [f"import {module}" for module in modules]
        checks = [f"#print axioms {name}" for name in declarations]
        audit.write_text("\n".join(imports + checks) + "\n", encoding="utf-8")
        result = subprocess.run(
            ("lake", "env", "lean", str(audit)), cwd=ROOT, text=True, stdout=subprocess.PIPE
        )

    print(result.stdout, end="", flush=True)
    result.check_returncode()
    lines = result.stdout.splitlines()
    for name in declarations:
        if f"'{name}' does not depend on any axioms" in lines:
            continue
        prefix = f"'{name}' depends on axioms: "
        report = next((line[len(prefix):] for line in lines if line.startswith(prefix)), "")
        if not report.startswith("[") or not report.endswith("]"):
            raise SystemExit(f"Missing axiom report for {name}")
        axioms = {axiom.strip() for axiom in report[1:-1].split(",") if axiom.strip()}
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            raise SystemExit(f"{name} uses unexpected axioms: {', '.join(sorted(unexpected))}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch-cache", action="store_true", help="fetch imported Mathlib modules")
    options = parser.parse_args()
    sources = sorted((ROOT / "OpenMath").glob("*.lean"))
    if options.fetch_cache:
        cache_imports = {
            module
            for source in [ROOT / "OpenMath.lean", *sources]
            for module in re.findall(r"^import (Mathlib(?:\.[\w.]+)?)$", source.read_text(), re.M)
        }
        if cache_imports:
            run("lake", "exe", "cache", "get", *sorted(cache_imports))

    run("lake", "build", "--wfail")
    if sources:
        modules = [f"OpenMath.{source.stem}" for source in sources]
        run("lake", "env", "leanchecker", "-v", *modules)
        audit_axioms(modules)

    for verifier in sorted((ROOT / "results").glob("*/check.py")):
        run(sys.executable, str(verifier))


if __name__ == "__main__":
    main()
