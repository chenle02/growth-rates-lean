#!/usr/bin/env python3
"""Synthetic schema mutations, after acceptance of the real full transcript."""
import importlib.util,pathlib,json,copy,sys,hashlib
root=pathlib.Path(__file__).resolve().parents[1];spec=importlib.util.spec_from_file_location('reader',root/'scripts/audit-owned.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
scope=m.read_json((root/'verification/scope.json').read_text());roster=m.read_json((root/'verification/owned-declarations.json').read_text());raw=pathlib.Path(sys.argv[1]).read_text();actual,_=m.parse(raw,scope,roster)
rows=list(actual.values());imports=scope['owned_modules'];controls=[]
for d in rows:
 d['type_repr']='synthetic type';d['body_repr']='synthetic body' if d['kind'] in ['theorem','definition','recursor'] else '';d['definition_body_repr']=d['body_repr'] if d['kind']=='definition' else ''
def render(rs,done=None,extra=''):
 return '\n'.join(['OWNED-DECL '+json.dumps(r) for r in rs]+['OWNED-IMPORTS '+json.dumps(imports),'OWNED-DONE '+str(len(rs) if done is None else done)])+'\n'+extra
def reject(label,text):
 try:m.parse(text,scope,roster)
 except (RuntimeError,ValueError,TypeError,KeyError):controls.append({'control':label,'rejected':True})
 else:raise AssertionError('Accepted '+label)
base=render(rows);m.parse(base,scope,roster)
reject('duplicate row',render(rows+[rows[0]]));reject('missing row',render(rows[1:]));reject('wrong count',render(rows,0));reject('missing end','\n'.join(base.splitlines()[:-1])+'\n');reject('extra output',base+'unexpected\n');reject('duplicate JSON key',base.replace('"unsafe": false','"unsafe": false, "unsafe": false',1))
i=next(i for i,d in enumerate(rows) if d['kind']=='theorem')
for key,value in [('axioms',['sorryAx']),('axioms',['External.forbidden']),('axioms',['propext','propext']),('unsafe',True),('unsafe',0),('kind','axiom'),('module','Mathlib'),('returns_prop',1),('type_repr',''),('body_repr',''),('type_repr',{}),('level_params','bad')]:
 rs=copy.deepcopy(rows);rs[i][key]=value;reject(key+'='+str(value),render(rs))
result={'passed':True,'synthetic_mutations':len(controls),'real_transcript_sha256':hashlib.sha256(raw.encode()).hexdigest(),'controls':controls,'scope':'Parser/schema tests; genuine compiled forbidden-axiom fixture is separate.'}
with pathlib.Path(sys.argv[2]).open('x') as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(result))
