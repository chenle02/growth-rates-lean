#!/usr/bin/env python3
"""Compile genuine positive and forbidden transitive-axiom fixtures separately."""
from pathlib import Path
import tempfile,subprocess,json,os,sys,importlib.util
root=Path(__file__).resolve().parents[1];out=Path(sys.argv[1]).resolve();out.mkdir(parents=True,exist_ok=False)
spec=importlib.util.spec_from_file_location('reader',root/'scripts/audit-owned.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
source='''module
public section
namespace GrowthRatesFixture
axiom forbidden : False
theorem positive : True := True.intro
theorem escaped : False := forbidden
end GrowthRatesFixture
'''
(out/'GrowthRatesFixture.lean').write_text(source)
config={'root_module':'GrowthRatesFixture','contracts':[]};(out/'scope.json').write_text(json.dumps(config))
env=dict(os.environ);run=subprocess.run(['lake','env','lean','-R',str(out),'-o',str(out/'GrowthRatesFixture.olean'),str(out/'GrowthRatesFixture.lean')],cwd=root,text=True,capture_output=True);(out/'compile.log').write_text(run.stdout+run.stderr);assert run.returncode==0
paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip();env['LEAN_PATH']=str(out)+os.pathsep+paths
with (out/'audit.log').open('w') as stdout,(out/'audit.err').open('w') as stderr:
 run=subprocess.run(['lean','--run',str(root/'verification/OwnedAudit.lean'),str(out/'scope.json')],cwd=root,env=env,stdout=stdout,stderr=stderr)
assert run.returncode==0 and not (out/'audit.err').read_bytes()
records={}
for line in (out/'audit.log').read_text().splitlines():
 if line.startswith('OWNED-DECL '):d=m.read_json(line[11:]);records[d['name']]=d
scope={'owned_modules':['GrowthRatesFixture']}
def isolated(row):return 'OWNED-DECL '+json.dumps(row)+'\nOWNED-IMPORTS ["GrowthRatesFixture"]\nOWNED-DONE 1\n'
m.parse(isolated(records['GrowthRatesFixture.positive']),scope)
assert records['GrowthRatesFixture.escaped']['axioms']==['GrowthRatesFixture.forbidden']
try:m.parse(isolated(records['GrowthRatesFixture.escaped']),scope)
except RuntimeError as exc:assert 'forbidden or malformed axioms' in str(exc)
else:raise AssertionError('Accepted actual forbidden-axiom theorem')
(out/'RESULT.json').write_text(json.dumps({'passed':True,'positive_compiled':True,'forbidden_transitive_axiom_rejected':True,'scope':'Actual compiled fixture identities; isolated positive/escaped theorem rows checked separately. Full original fixture transcript is retained.'},indent=2)+'\n');print('actual compiled positive / forbidden-transitive-axiom fixture: PASS')
