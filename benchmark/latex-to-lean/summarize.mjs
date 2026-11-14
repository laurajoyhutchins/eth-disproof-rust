#!/usr/bin/env node
// Fail-closed, parser-only coverage importer. Never infer proof from exit=0.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
const [evidenceDir,casesDir,outputFile,selected='all']=process.argv.slice(2);
if(!evidenceDir||!casesDir||!outputFile)throw Error('usage: summarize.mjs EVIDENCE_DIR CASES_DIR OUTPUT_JSON [all|E01,G01]');
const hash=p=>crypto.createHash('sha256').update(fs.readFileSync(p)).digest('hex');
const read=(id,ext)=>fs.readFileSync(path.join(evidenceDir,id+'.'+ext),'utf8');
const upstream=fs.readFileSync(path.join(evidenceDir,'sha.txt'),'utf8').trim();
if(upstream!=='134da59ae02e9fffc011a5ea89acf4320268d220')throw Error('wrong upstream revision');
const all=fs.readdirSync(casesDir).filter(x=>/^[ERGX]\d\d\.tex$/.test(x)).map(x=>x.slice(0,3)).sort();
if(all.length!==32||new Set(all).size!==32)throw Error('expected 32 corpus fixtures');
const ids=selected==='all'?all:selected.split(',').sort();
if(!ids.length||new Set(ids).size!==ids.length||ids.some(x=>!all.includes(x)))throw Error('bad case selection');
const records=[];
for(const id of ids){
 const stdout=read(id,'stdout'),stderr=read(id,'stderr');
 const exitRaw=read(id,'exit').trim();
 if(!/^\d+$/.test(exitRaw))throw Error(id+' invalid exit status');
 const exit=Number(exitRaw);
 const matches=[...stdout.matchAll(/\bresults:\s*(\d+) compiled,\s*(\d+) failed,\s*(\d+) prose \(of (\d+)\)/g)];
 if(matches.length!==1)throw Error(id+' expected one results counter');
 const [compiled,failed,prose,total]=matches[0].slice(1).map(Number);
 if(compiled+failed+prose!==total||total===0)throw Error(id+' inconsistent totals');
 const claims=[...stdout.matchAll(/\binfo: claim\s+\d+:\s+(.+)$/gm)].map(x=>x[1]);
 if(claims.length!==compiled)throw Error(id+' claims/compiled count mismatch');
 const warnings=stdout.split('\n').filter(s=>/\bwarning:/.test(s));
 const gap=warnings.some(s=>/not checked|partly checked|follows a sentence that Leanify does not read/.test(s));
 const status=exit!==0?'execution_error':failed>0?'parse_failure':compiled===total&&!gap?'statement_compiled':'unsupported_or_partial';
 records.push({id,source_sha256:hash(path.join(casesDir,id+'.tex')),stdout_sha256:hash(path.join(evidenceDir,id+'.stdout')),stderr_sha256:hash(path.join(evidenceDir,id+'.stderr')),exit_code:exit,compiled,failed,prose,total,status,claims,warnings,proof_status:'not_run',refutation_status:'not_run',semantic_equivalence:'not_audited'});
}
const strata=Object.fromEntries('ERGX'.split('').map(c=>[c,{attempted:0,compiled:0,unsupported:0,errors:0}]));
for(const r of records){let x=strata[r.id[0]];x.attempted++;if(r.status==='statement_compiled')x.compiled++;else if(r.status==='unsupported_or_partial')x.unsupported++;else x.errors++;}
const result={schema_version:2,upstream_commit:upstream,phase:'check --claims',interpretation:'Statement parsing only; no proof, refutation, or semantic equivalence credit',strata,records};
fs.mkdirSync(path.dirname(outputFile),{recursive:true});fs.writeFileSync(outputFile,JSON.stringify(result,null,2)+'\n');
console.log(JSON.stringify(strata,null,2));
