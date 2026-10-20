#!/usr/bin/env python3
"""Pack/restore same-run build outputs only. Never extract Lean source files."""
import argparse, hashlib, json, os, subprocess, tarfile, tempfile
from pathlib import Path, PurePosixPath

PROJECT = Path("lean")
BUILD = PROJECT / ".lake/build"

def sha(p):
    h = hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda: f.read(1048576), b""): h.update(b)
    return h.hexdigest()

def identity():
    return {"commit": os.environ["GITHUB_SHA"], "run_id": os.environ["GITHUB_RUN_ID"],
            "source_manifest_sha256": sha(Path(".github/lean/source-sha256.json")),
            "toolchain": (PROJECT / "lean-toolchain").read_text().strip()}

def module_file(path, module):
    return ("/" + module.replace(".", "/") + ".") in path.as_posix()

def pack(dest, module):
    dest.mkdir(parents=True, exist_ok=True)
    files = sorted(p for p in BUILD.rglob("*") if p.is_file())
    if module: files = [p for p in files if module_file(p, module)]
    if not files: raise SystemExit("No build files to pack")
    if module and not any(p.name.endswith(".olean") for p in files):
        raise SystemExit("Native module has no .olean output")
    entries = {p.relative_to(PROJECT).as_posix(): sha(p) for p in files}
    if not module:
        native = json.loads(Path(".ci-plan/native.json").read_text())
        if any(module_file(Path(p), m) for p in entries for m in native):
            raise SystemExit("Shared base unexpectedly contains native certificate outputs")
    archive = dest / "outputs.tar.zst"
    with tempfile.NamedTemporaryFile(mode="w", delete=True) as listing:
        listing.write("\n".join(entries) + "\n"); listing.flush()
        tar = subprocess.Popen(["tar", "-C", str(PROJECT), "-cf", "-", "-T", listing.name],
                               stdout=subprocess.PIPE, env={**os.environ, "COPYFILE_DISABLE": "1"})
        try:
            subprocess.run(["zstd", "-T2", "-3", "-o", str(archive)], stdin=tar.stdout, check=True)
        finally:
            tar.stdout.close()
        if tar.wait() != 0: raise SystemExit("tar failed")
    base = sha(Path("artifacts/base/metadata.json")) if module else None
    meta = {**identity(), "module": module, "files": entries, "archive_sha256": sha(archive),
            "base_metadata_sha256": base, "produced_attempt": os.environ.get("GITHUB_RUN_ATTEMPT", "")}
    (dest / "metadata.json").write_text(json.dumps(meta, sort_keys=True, indent=2) + "\n")

def restore(src, expected_module, *, origin=None):
    meta = json.loads((src / "metadata.json").read_text())
    # Normal callers remain bound to this run. Recovery can replace only the
    # producer commit/run; current source-manifest and toolchain checks remain.
    expected = identity()
    if origin is not None:
        if set(origin) != {"commit", "run_id"} or not all(origin.values()):
            raise SystemExit("Recovery origin must specify exactly commit and run_id")
        expected.update(origin)
    for key, val in expected.items():
        if meta.get(key) != val: raise SystemExit(f"Artifact identity mismatch: {src}: {key}")
    if meta["module"] != expected_module: raise SystemExit(f"Wrong artifact module: {src}")
    if expected_module and meta["base_metadata_sha256"] != sha(Path("artifacts/base/metadata.json")):
        raise SystemExit("Native artifact used a different shared base")
    archive = src / "outputs.tar.zst"
    if sha(archive) != meta["archive_sha256"]: raise SystemExit("Artifact digest mismatch")
    seen = set()
    proc = subprocess.Popen(["zstd", "-dc", str(archive)], stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=proc.stdout, mode="r|") as tf:
            for member in tf:
                name = PurePosixPath(member.name)
                if (not member.isfile() or name.is_absolute() or ".." in name.parts or
                    name.parts[:2] != (".lake", "build") or str(name) not in meta["files"]):
                    raise SystemExit(f"Invalid build artifact member: {member.name}")
                if str(name) in seen: raise SystemExit("Duplicate artifact member")
                if expected_module and not module_file(name, expected_module):
                    raise SystemExit("Native artifact contains another module")
                seen.add(str(name))
                dest = PROJECT / str(name)
                content = tf.extractfile(member)
                dest.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(dir=dest.parent, delete=False) as temp:
                    tmp = Path(temp.name)
                    while data := content.read(1048576): temp.write(data)
                if sha(tmp) != meta["files"][str(name)]:
                    tmp.unlink(); raise SystemExit("Member digest mismatch")
                if dest.exists() and sha(dest) != sha(tmp):
                    tmp.unlink(); raise SystemExit(f"Conflicting build output: {dest}")
                tmp.replace(dest)
        if proc.wait() != 0: raise SystemExit("zstd failed")
    finally:
        proc.stdout.close()
        if proc.poll() is None: proc.kill()
    if seen != set(meta["files"]): raise SystemExit("Missing artifact members")
    print(f"Restored {len(seen)} checked build files from {src}")

def restore_native(directory, *, origin=None):
    expected = set(json.loads(Path(".ci-plan/native.json").read_text()))
    dirs = sorted(directory.glob("native-*"))
    seen = set()
    for d in dirs:
        m = json.loads((d / "metadata.json").read_text())["module"]
        if m not in expected or m in seen: raise SystemExit(f"Unexpected/duplicate native module: {m}")
        restore(d, m, origin=origin); seen.add(m)
    if seen != expected: raise SystemExit(f"Missing native modules: {sorted(expected-seen)}")
    print(f"Restored all {len(seen)} native modules from the validated origin")

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("command", choices=["pack", "restore", "restore-native"])
    ap.add_argument("directory", type=Path)
    ap.add_argument("--module", default="")
    a = ap.parse_args()
    if a.command == "pack": pack(a.directory, a.module)
    elif a.command == "restore": restore(a.directory, a.module)
    else: restore_native(a.directory)

if __name__ == "__main__": main()
