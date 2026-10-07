#!/usr/bin/env python3
"""Build the manuscript with pinned Tectonic; no repository-local dependencies."""
import argparse, hashlib, json, os, pathlib, shutil, subprocess
p=argparse.ArgumentParser();p.add_argument('--tectonic',default='tectonic');p.add_argument('--cache-dir');p.add_argument('--only-cached',action='store_true');a=p.parse_args()
r=pathlib.Path(__file__).resolve().parent; lock=json.loads((r/'tex_environment.json').read_text());out=r/'build';out.mkdir(exist_ok=True)
exe=shutil.which(a.tectonic)
if not exe: raise SystemExit('Tectonic 0.17.0 required; pass --tectonic with its installed path.')
env=os.environ.copy();env['SOURCE_DATE_EPOCH']='0';env['TECTONIC_UNTRUSTED_MODE']='1'
if a.cache_dir:env['TECTONIC_CACHE_DIR']=str(pathlib.Path(a.cache_dir).resolve())
v=subprocess.check_output([exe,'--version'],text=True).strip()
if v!=lock['engine']:raise SystemExit('Unexpected Tectonic version: '+v)
aud=out/'bundle-audit';aud.mkdir(exist_ok=True)
(aud/'Tectonic.toml').write_text('[doc]\nname = "bras-amoros"\nbundle = '+json.dumps(lock['bundle_url'])+'\n[[output]]\nname = "manuscript"\ntype = "pdf"\n')
cmd=[exe,'-X','bundle','cat']+(['--only-cached'] if a.only_cached else [])+['SHA256SUM']
bundle=subprocess.check_output(cmd,cwd=aud,env=env,text=True).strip()
if bundle!=lock['bundle_sha256']:raise SystemExit('TeX bundle identity mismatch')
cmd=[exe,'-X','compile','--bundle',lock['bundle_url'],'--untrusted','--keep-logs','--keep-intermediates','--outdir',str(out)]+(['--only-cached'] if a.only_cached else [])+['manuscript.tex']
res=subprocess.run(cmd,cwd=r,env=env,capture_output=True,text=True)
(out/'command.log').write_text(res.stdout+'\n'+res.stderr)
if res.returncode:raise SystemExit(res.stderr)
log=(out/'manuscript.log').read_text();bad=[s for s in log.splitlines() if any(k in s for k in ['undefined references','undefined on input','multiply defined','Overfull','Missing character:'])]
record={'engine':v,'bundle_sha256':bundle,'only_cached':a.only_cached,'command':cmd,'source_sha256':hashlib.sha256((r/'manuscript.tex').read_bytes()).hexdigest(),'pdf_sha256':hashlib.sha256((out/'manuscript.pdf').read_bytes()).hexdigest(),'warnings_requiring_review':bad}
(out/'build_record.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
if bad:raise SystemExit('Inspect TeX warnings')
