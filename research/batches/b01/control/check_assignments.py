#!/usr/bin/env python3
"""Validate exclusive ownership and pinned statements; optionally check a worker diff."""
import argparse, hashlib, json, subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--worker')
p.add_argument('--against',help='Coordinator seed commit, for worker changed-path audit')
a=p.parse_args()
m=json.loads((Path(__file__).parent/'assignments.json').read_text())
seen={}; decls={}; ids=set(); failures=[]
for w in m['workers']:
    wid=w['worker_id']
    if wid in ids: failures.append(f'duplicate worker {wid}')
    ids.add(wid)
    for g in w['reserved_sequence_groups']:
        if g in seen: failures.append(f'duplicate group {g}: {seen[g]} and {wid}')
        seen[g]=wid
    for t in w['targets']:
        if t['id'] in m['excluded']: failures.append(f'excluded target {t["id"]}')
        if t['id'] not in w['reserved_sequence_groups']: failures.append(f'unreserved target {t["id"]}')
        for d in t['declarations']:
            if d in decls: failures.append(f'duplicate declaration {d}')
            decls[d]=wid
        data=subprocess.check_output(['git','show',m['source_commit']+':'+t['source_file']],cwd=a.repo)
        if hashlib.sha256(data).hexdigest()!=t['source_sha256']: failures.append(f'baseline hash mismatch {t["id"]}')
        if a.worker==wid:
            if hashlib.sha256((a.repo/t['source_file']).read_bytes()).hexdigest()!=t['source_sha256']:
                failures.append(f'working source mismatch {t["id"]}')
if a.worker and a.worker not in ids: failures.append('unknown worker')
if a.against:
    if not a.worker: p.error('--against requires --worker')
    committed=subprocess.check_output(['git','diff','--name-only',a.against],cwd=a.repo,text=True).splitlines()
    untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=a.repo,text=True).splitlines()
    allowed=f'research/batches/b01/workers/{a.worker}/'
    failures.extend(f'out-of-scope edit: {f}' for f in set(committed+untracked) if not f.startswith(allowed))
if failures: raise SystemExit('\n'.join(failures))
print(f'PASS: {len(ids)} distinct workers, {len(decls)} declarations, {len(seen)} reserved sequence IDs; pinned hashes match.')
print('This checks explicit assignments and file scope; it cannot detect unknown mathematical equivalences or establish novelty.')
