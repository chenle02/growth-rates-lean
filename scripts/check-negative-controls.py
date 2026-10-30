#!/usr/bin/env python3
"""Exact altered-contract regression checks, not counterexample certificates.

The paired positive interface is GrowthRates.Solution (all 26 original slots).
The historical mutations deliberately misuse that interface and must fail only
with elaborated type/application mismatches, never setup or missing names.
Rejection of an attempted proof does not imply the mutated statement is false.
"""
from pathlib import Path
import subprocess,tempfile,json,re,sys,hashlib
root=Path(__file__).resolve().parents[1];out=Path(sys.argv[1]).resolve();out.mkdir(parents=True,exist_ok=False)
expected={'NegFeketeNoSubadditivity','NegFeketeSupremum','NegJointLimitNoAntitone','NegLogDefectNoMonotone','NegLogDefectUncorrectedRate','NegLogErrorNoLogTerm','NegLowerBoundNoLogTerm','NegRealOrderBelowTwo'}
files=sorted((root/'GrowthRatesTest').glob('Neg*.lean.disabled'));assert {f.name.removesuffix('.lean.disabled') for f in files}==expected
contracts=json.loads((root/'verification/contract-controls.json').read_text());assert set(contracts)=={str(f.relative_to(root)) for f in files}
rows=[]
for f in files:
 with tempfile.TemporaryDirectory(prefix='contract-controls-',dir=root/'.lake') as tmp:
  target=Path(tmp)/f.name.removesuffix('.disabled');target.write_bytes(f.read_bytes())
  run=subprocess.run(['lake','env','lean',str(target)],cwd=root,capture_output=True,text=True,timeout=120)
 text=run.stdout+run.stderr;(out/(f.stem+'.log')).write_text(text)
 headers=re.findall(r'(?m)^.*?:\d+:\d+: error(?:\([^)]*\))?: ([^\n]+)',text)
 allowed=('Application type mismatch','Type mismatch','application type mismatch','type mismatch','Insufficient number of fields for')
 contract=contracts[str(f.relative_to(root))]
 ok=run.returncode==1 and bool(headers) and headers==contract['errors'] and hashlib.sha256(f.read_bytes()).hexdigest()==contract['sha256'] and all(x.startswith(allowed) for x in headers)
 rows.append({'source':str(f.relative_to(root)),'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'exit':run.returncode,'errors':headers,'passed':ok,'scope':'Altered API rejection, not a proof that the altered theorem is false.'})
(out/'RESULT.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows));raise SystemExit(0 if all(r['passed'] for r in rows) else 1)
