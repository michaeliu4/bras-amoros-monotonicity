#!/usr/bin/env python3
"""Plan the fixed published proof and enforce its exact source manifest."""
import argparse, hashlib, json, os, re
from pathlib import Path

TARGETS = ["Results.Genus.Native.Main", "Results.Genus.Native.Coverage",
           "Results.Genus.Native.KnownAsymptotic"]
UPSTREAM = "5b96214946ee52bb6570561ab6e019970809cdd8"
TOOLCHAIN = "leanprover/lean4:v4.32.1"

def strip_lean(src: str) -> str:
    """Blank out nested /- -/ comments, -- line comments and string literals."""
    out, i, n, depth, in_str = [], 0, len(src), 0, False
    while i < n:
        c, d = src[i], src[i + 1] if i + 1 < n else ""
        if depth:
            if c == "/" and d == "-":
                depth += 1; out.append("  "); i += 2
            elif c == "-" and d == "/":
                depth -= 1; out.append("  "); i += 2
            else:
                out.append("\n" if c == "\n" else " "); i += 1
        elif in_str:
            if c == "\\" and d:
                out.append("  "); i += 2
            elif c == '"':
                in_str = False; out.append(" "); i += 1
            else:
                out.append("\n" if c == "\n" else " "); i += 1
        elif c == "/" and d == "-":
            depth = 1; out.append("  "); i += 2
        elif c == "-" and d == "-":
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
        elif c == '"':
            in_str = True; out.append(" "); i += 1
        else:
            out.append(c); i += 1
    return "".join(out)



def sources(project):
    paths = []
    for directory, dirs, files in os.walk(project):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        paths.extend(Path(directory) / n for n in files if n.endswith(".lean"))
    paths += [project / n for n in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    return {p.relative_to(project).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(paths)}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--project", type=Path, default=Path("lean"))
    ap.add_argument("--seal", action="store_true", help="Packaging only: write the reviewed source manifest")
    a = ap.parse_args()
    manifest_path = Path(".github/lean/source-sha256.json")
    hashes = sources(a.project)
    expected = {"upstream_commit": UPSTREAM, "files": hashes}
    if a.seal:
        manifest_path.write_text(json.dumps(expected, sort_keys=True, indent=2) + "\n")
        print(f"Sealed {len(hashes)} source/configuration files; this is not build evidence.")
        return
    if json.loads(manifest_path.read_text()) != expected:
        raise SystemExit("Published source manifest mismatch (missing, extra or changed source/config).")
    if (a.project / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise SystemExit("Unexpected Lean toolchain")
    graph, texts = {}, {}
    def visit(mod):
        if mod in graph:
            return
        p = a.project / (mod.replace(".", "/") + ".lean")
        if not p.is_file():
            raise SystemExit(f"Missing project import: {mod}")
        s = strip_lean(p.read_text())
        texts[mod] = s
        imports = [m for line in re.findall(r"^import\s+([^\n]+)", s, re.M) for m in line.split()]
        graph[mod] = imports
        for m in imports:
            if m.startswith("Results."):
                visit(m)
    for m in TARGETS:
        visit(m)
    native, axiom_names = {}, []
    banned = re.compile(r"\b(sorry|admit|axiom|opaque|unsafe|implemented_by|extern|ofReduceBool|ofReduceNat|trustCompiler)\b")
    for mod, s in sorted(texts.items()):
        if banned.search(s):
            raise SystemExit(f"Forbidden source construct in {mod}: {banned.search(s).group()}")
        count = len(re.findall(r"\bnative_decide\b", s))
        if not count:
            continue
        namespaces = re.findall(r"^namespace\s+([\w.]+)\s*$", s, re.M)
        thms = re.findall(r"^theorem\s+([\w]+)\s*:", s, re.M)
        if count != 1 or len(namespaces) != 1 or len(thms) != 1:
            raise SystemExit(f"Native source needs explicit review: {mod}")
        theorem = namespaces[0] + "." + thms[0]
        native[mod] = theorem
        axiom_names.append(theorem + "._native.native_decide.ax_1_1")
    cap4 = sorted(m for m in native if ".ArrayNative.Cap4." in m)
    other = sorted(set(native) - set(cap4))
    if len(native) != 279 or len(cap4) != 224 or len(other) != 55:
        raise SystemExit(f"Unexpected native module counts: {len(native)}, {len(cap4)}, {len(other)}")
    base = sorted({i for m in native for i in graph[m] if i.startswith("Results.")})
    def no_native(m, seen):
        if m in seen: return
        seen.add(m)
        if m in native: raise SystemExit(f"Native dependency in shared base: {m}")
        for i in graph[m]:
            if i.startswith("Results."): no_native(i, seen)
    for m in base:
        no_native(m, set())
    out = Path(".ci-plan")
    out.mkdir(exist_ok=True)
    (out / "targets.txt").write_text("\n".join(TARGETS) + "\n")
    (out / "base-roots.txt").write_text("\n".join(base) + "\n")
    (out / "closure.txt").write_text("\n".join(sorted(graph)) + "\n")
    (out / "native.json").write_text(json.dumps(native, sort_keys=True, indent=2) + "\n")
    (out / "native-axioms.json").write_text(json.dumps(sorted(axiom_names), indent=2) + "\n")
    external = sorted({i for imps in graph.values() for i in imps if i.startswith("Mathlib.")})
    (out / "mathlib-roots.txt").write_text("\n".join(external) + "\n")
    matrix = lambda ms: json.dumps({"include": [{"module": m} for m in ms]}, separators=(",", ":"))
    if os.getenv("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as f:
            f.write("cap4=" + matrix(cap4) + "\nother=" + matrix(other) + "\n")
    template = Path(".github/lean/AxiomAudit.lean.in").read_text()
    names = "#[" + ", ".join("`" + n for n in sorted(axiom_names)) + "]"
    triples = "#[" + ", ".join(
        "(`" + mod + ", `" + thm + ", `" + thm + "._native.native_decide.ax_1_1)"
        for mod, thm in sorted(native.items())) + "]"
    audit = template.replace("@NATIVE_AXIOMS@", names).replace("@NATIVE_TRIPLES@", triples)
    (out / "AxiomAudit.lean").write_text(audit)
    print(f"Source manifest matched; {len(graph)} project modules; {len(cap4)} cap4 and {len(other)} other native certificates.")
    print("Allowed generated axioms: exact 279 names; standard axioms: propext, Classical.choice, Quot.sound.")

if __name__ == "__main__":
    main()

