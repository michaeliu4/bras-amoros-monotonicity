#!/usr/bin/env python3
"""Resume PR 2's audit-helper repair from one exactly pinned public build."""
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

REPOSITORY = "michaeliu4/bras-amoros-monotonicity"
BRANCH = "codex/lean-verification-20261017"
SOURCE_HEAD = "a5d34b7027d21d1c3ad39ba61bd468a1b9ae0bb6"
ORIGIN = {
    "commit": "161425b091a24e6b5afc3f03d9979dc3d930f382",
    "run_id": "39069868966",
    "source_manifest_sha256": "a4a77e67e32d66462a42dae596cc452b86ded4835bb1ec6001602817c69c8d0e",
    "toolchain": "leanprover/lean4:v4.32.1",
}
HELPERS = {
    "prepare.py": "934cd8211ababa8173077b8cbcc12968628f7aaca498b3ec6229dc7a4d6f119d",
    "bootstrap.sh": "97427e2967a8f5aa16bf2838500f91564f3d8d5b28e1b27bf7967a466eb26f57",
    "AxiomAudit.lean.in": "35758ee4aa180d49ed7f340cf44dd70fabc38587e2cce183c8531f0b2f31c367",
    "artifacts.py": "e949bec68027e6851235d460afccf3e3d082e1a24fa222bdc7d783fdd083b9e8",
}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def eligible(event, env):
    pr = event.get("pull_request", {})
    return (
        env.get("GITHUB_EVENT_NAME") == "pull_request"
        and env.get("GITHUB_REPOSITORY") == REPOSITORY
        and event.get("number") == 2
        and pr.get("head", {}).get("ref") == BRANCH
        and pr.get("head", {}).get("repo", {}).get("full_name") == REPOSITORY
        and pr.get("base", {}).get("repo", {}).get("full_name") == REPOSITORY
        and pr.get("base", {}).get("ref") == "main"
    )


def checked_origin(event, env):
    if not eligible(event, env):
        raise SystemExit("Pinned recovery is restricted to the original same-repository PR 2.")
    if digest(".github/lean/source-sha256.json") != ORIGIN["source_manifest_sha256"]:
        raise SystemExit("Recovery source manifest differs from the original public build.")
    for name, expected in HELPERS.items():
        if digest(Path(".github/lean") / name) != expected:
            raise SystemExit(f"Recovery helper differs from the reviewed repair: {name}")
    # Checks every actual Lean source/configuration file, not just the manifest.
    subprocess.run([sys.executable, "-I", ".github/lean/prepare.py"], check=True)
    return dict(ORIGIN)


def restore(event, env):
    origin = checked_origin(event, env)
    dirs = [Path("artifacts/base"), *sorted(Path("artifacts/native").glob("native-*"))]
    for directory in dirs:
        meta = json.loads((directory / "metadata.json").read_text())
        if any(meta.get(key) != value for key, value in origin.items()):
            raise SystemExit(f"Wrong pinned artifact origin: {directory}")
        if meta.get("produced_attempt") not in ("1", "2"):
            raise SystemExit(f"Artifact was not produced in the audited native builds: {directory}")
    spec = importlib.util.spec_from_file_location("checked_artifacts", ".github/lean/artifacts.py")
    artifacts = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(artifacts)
    # Original member/archive digests, path checks, shared-base identity and
    # exact 279-module coverage remain mandatory.
    producer = {key: origin[key] for key in ("commit", "run_id")}
    artifacts.restore(Path("artifacts/base"), "", origin=producer)
    artifacts.restore_native(Path("artifacts/native"), origin=producer)
    checked_origin(event, env)
    record = {
        "current_commit": env["GITHUB_SHA"],
        "current_run_id": env["GITHUB_RUN_ID"],
        "source_head": SOURCE_HEAD,
        "artifact_origin": origin,
        "native_compilation_attempts": [1, 2],
        "source_and_toolchain_unchanged": True,
        "final_build_axiom_audit_and_replay": "must run in the current job",
    }
    Path(".ci-plan/recovery-origin.json").write_text(json.dumps(record, indent=2) + "\n")
    print("Restored the exact 279-certificate set from public run 39069868966.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["plan", "restore"])
    args = parser.parse_args()
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    if args.command == "restore":
        restore(event, os.environ)
        return
    enabled = eligible(event, os.environ)
    if enabled:
        checked_origin(event, os.environ)
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"recovery={'true' if enabled else 'false'}\n")
        output.write(f"artifact-run-id={ORIGIN['run_id'] if enabled else os.environ['GITHUB_RUN_ID']}\n")
    print("Pinned audit-helper recovery selected." if enabled else "Clean full verification selected.")


if __name__ == "__main__":
    main()
