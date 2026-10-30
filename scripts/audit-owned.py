#!/usr/bin/env python3
"""Complete module-owned identities, bound roster and source/dependency guards.

Raw expressions and available bodies are retained without truncation. Imported
compiled dependencies and the compiler remain trusted. This is not a prose or
literature-correspondence checker.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,copy,re
ROOT=Path(__file__).resolve().parents[1]
ALLOWED={'propext','Quot.sound','Classical.choice'}
def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def read_json(s):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(s,object_pairs_hook=pairs)
def git(*args,cwd=ROOT):return subprocess.check_output(['git',*args],cwd=cwd,text=True).strip()
def dependencies():
 rows=[]
 for p in read_json((ROOT/'lake-manifest.json').read_text())['packages']:
  need(p['type']=='git','unsupported dependency kind')
  path=ROOT/'.lake/packages'/p['name'];need(path.is_dir(),'missing dependency '+p['name'])
  head=git('rev-parse','HEAD',cwd=path);need(head==p['rev'],'wrong dependency revision '+p['name'])
  need(Path(git('rev-parse','--show-toplevel',cwd=path)).resolve()==path.resolve(),'wrong dependency Git root')
  need(not git('status','--porcelain','--untracked-files=normal',cwd=path),'dirty dependency '+p['name'])
  need(not (path/'.lake/build/lib/lean/GrowthRates').exists() and not (path/'.lake/build/lib/lean/GrowthRates.olean').exists(),'owned namespace shadowed')
  rows.append({'name':p['name'],'rev':head,'clean':True})
 return rows
FIELDS={'name','module','kind','level_params','unsafe','axioms','returns_prop','type_repr','body_repr','definition_body_repr'}
def parse(raw,scope,roster=None):
 rows={};imports=[];done=[]
 for line in raw.splitlines():
  if line.startswith('OWNED-DECL '):
   d=read_json(line[11:]);need(set(d)==FIELDS,'row schema');n=d['name'];need(type(n) is str and n not in rows,'duplicate or invalid name');rows[n]=d
   need(d['module'] in scope['owned_modules'],'unknown owner')
   need(type(d['unsafe']) is bool and not d['unsafe'],'unsafe declaration')
   need(type(d['returns_prop']) is bool,'invalid proposition flag')
   need(type(d['level_params']) is list and all(type(x) is str for x in d['level_params']),'invalid universe parameters')
   need(type(d['axioms']) is list and all(type(x) is str for x in d['axioms']) and len(d['axioms'])==len(set(d['axioms'])) and set(d['axioms'])<=ALLOWED,'forbidden or malformed axioms')
   need(d['kind'] in ['theorem','definition','inductive','constructor','recursor'],'forbidden kind')
   need(type(d['type_repr']) is str and bool(d['type_repr']),'missing type')
   need(type(d['body_repr']) is str and (d['kind'] not in ['theorem','definition'] or bool(d['body_repr'])),'missing available body')
   need(type(d['definition_body_repr']) is str,'invalid definition body')
  elif line.startswith('OWNED-IMPORTS '):imports.append(read_json(line[14:]))
  elif line.startswith('OWNED-DONE '):done.append(int(line[11:]))
  else:need(not line.strip(),'unexpected output')
 need(done==[len(rows)] and bool(rows),'incomplete count')
 need(len(imports)==1 and set(scope['owned_modules'])<=set(imports[0]),'incomplete imports')
 actual={n:{'module':d['module'],'kind':d['kind']} for n,d in rows.items()}
 if roster is not None:need(actual==roster,'owned roster drift')
 return rows,actual

def main():
 p=argparse.ArgumentParser();p.add_argument('out');p.add_argument('--discover',action='store_true');args=p.parse_args()
 out=Path(args.out).resolve();out.mkdir(parents=True,exist_ok=False)
 scope=read_json((ROOT/'verification/scope.json').read_text());before=dependencies()
 actualmods={str(f.relative_to(ROOT)).removesuffix('.lean').replace('/','.') for f in (ROOT/'GrowthRates').glob('*.lean')}
 need(actualmods==set(scope['owned_modules'])|{'GrowthRates.Challenge','GrowthRates.Solution','GrowthRates.Axioms'},'unregistered source module')
 cfg=read_json((ROOT/'comparator.json').read_text())
 need({n.replace('GrowthRatesAudit.','',1) for n in cfg['theorem_names']}=={n for n,c in scope['claims'].items() if c['status']=='reusable'},'comparator/reusable scope drift')
 need(cfg['definition_names']==[] and cfg['enable_nanoda'] is True and set(cfg['permitted_axioms'])==ALLOWED,'comparator policy drift')
 # A deliberate finite source surface, independently matched against the live environment.
 paths=[ROOT/'GrowthRates.lean',*sorted((ROOT/'GrowthRates').glob('*.lean'))]
 for f in paths:
  if f.name=='Challenge.lean':continue
  text=re.sub(r'/\-.*?\-/|--[^\n]*','',f.read_text(),flags=re.S)
  need(not re.search(r'\b(sorry|admit|axiom|opaque|native_decide)\b',text),'forbidden source escape '+f.name)
 sources={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in paths}
 with (out/'stdout.log').open('w') as stdout,(out/'stderr.log').open('w') as stderr:
  r=subprocess.run(['lake','env','lean','--run','verification/OwnedAudit.lean','verification/scope.json'],cwd=ROOT,stdout=stdout,stderr=stderr,timeout=600)
 need(r.returncode==0 and not (out/'stderr.log').read_bytes(),'owned inspector failed')
 rosterpath=ROOT/'verification/owned-declarations.json'
 roster=None if args.discover else read_json(rosterpath.read_text())
 raw=(out/'stdout.log').read_text();rows,actual=parse(raw,scope,roster)
 for n,c in scope['claims'].items():need(n in actual and actual[n]=={k:c[k] for k in ['module','kind']},'missing or mismatched named claim '+n)
 if args.discover:rosterpath.write_text(json.dumps(actual,indent=2,sort_keys=True)+'\n')
 need(before==dependencies(),'dependency changed during audit')
 need(all(hashlib.sha256((ROOT/k).read_bytes()).hexdigest()==v for k,v in sources.items()),'source changed during audit')
 result={'passed':True,'owned_declarations':len(rows),'raw_bytes':(out/'stdout.log').stat().st_size,'raw_sha256':hashlib.sha256((out/'stdout.log').read_bytes()).hexdigest(),'sources':sources,'dependencies':before,'trust':scope['trust']}
 (out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
