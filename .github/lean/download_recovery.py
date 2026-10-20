#!/usr/bin/env python3
"""Download the pinned recovery artifacts in paced, sequential CLI batches."""
import importlib.util
import json
import os
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

BATCH_SIZE = 20


def download_batches(names, destination, run_id, repository):
    if len(names) != 279 or len(set(names)) != 279:
        raise SystemExit("Recovery requires exactly 279 distinct artifact names.")
    if destination.exists():
        raise SystemExit("Recovery download destination must not already exist.")
    destination.mkdir(parents=True)
    batches = [names[i:i + BATCH_SIZE] for i in range(0, len(names), BATCH_SIZE)]
    for number, batch in enumerate(batches, 1):
        print(f"Downloading recovery batch {number}/{len(batches)} "
              f"({len(batch)} artifacts, sequential downloads).", flush=True)
        for attempt in range(3):
            # Retries never mix a partially downloaded batch with its replacement.
            with tempfile.TemporaryDirectory(prefix=".recovery-", dir=destination.parent) as tmp:
                command = ["gh", "run", "download", run_id, "--repo", repository,
                           "--dir", tmp]
                for name in batch:
                    command.extend(["--name", name])
                result = subprocess.run(command, check=False)
                if result.returncode == 0:
                    entries = list(Path(tmp).iterdir())
                    if {p.name for p in entries} != set(batch) or any(
                        not p.is_dir() or p.is_symlink() for p in entries
                    ):
                        raise SystemExit("Downloaded artifact directories do not match this batch.")
                    for entry in entries:
                        shutil.move(str(entry), destination / entry.name)
                    break
            if attempt == 2:
                raise SystemExit("Recovery download failed after three attempts; stopping.")
            delay = 60 * (attempt + 1)
            print(f"Download failed; waiting {delay} seconds before retrying this batch.",
                  flush=True)
            time.sleep(delay)
        if number != len(batches):
            time.sleep(10)
    if {p.name for p in destination.iterdir()} != set(names):
        raise SystemExit("Recovery download does not contain the exact planned artifact set.")


def main():
    spec = importlib.util.spec_from_file_location("checked_recovery", ".github/lean/recovery.py")
    recovery = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(recovery)
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    origin = recovery.checked_origin(event, os.environ)
    modules = json.loads(Path(".ci-plan/native.json").read_text())
    names = ["native-" + module for module in sorted(modules)]
    # gh follows all REST pagination and downloads named artifacts sequentially.
    # The subsequent restore still verifies every artifact's origin and digests.
    download_batches(names, Path("artifacts/native"), origin["run_id"], recovery.REPOSITORY)


if __name__ == "__main__":
    main()
