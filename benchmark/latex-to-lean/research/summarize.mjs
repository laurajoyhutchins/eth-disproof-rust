#!/usr/bin/env node
// Check-only compiler evidence, never proof or faithfulness credit.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
const [root,evidence,dest]=process.argv.slice(2);
if(!root||!evidence||!dest)throw Error('usage: summarize.mjs SUITE EVIDENCE OUTPUT');
const m=JSON.parse(fs.readFileSync(path.join(root,'manifest.json')));
if(m.schema_version!==1||m.cases.length!==12||new Set(m.cases.map(c=>c.id)).size!==12)throw Error('invalid manifest');
const vendor=fs.readFileSync(path.join(evidence,'vendor.sha'),'utf8').trim();
if(vendor!==m.upstream_commit)throw Error('untrusted vendor revision');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const records=[];
for(const c of m.cases){
 const source=fs.readFileSync(path.join(root,'cases',c.id+'.tex'));
 const stdout=fs.readFileSync(path.join(evidence,c.id+'.stdout'),'utf8');
 const stderr=fs.readFileSync(path.join(evidence,c.id+'.stderr'),'utf8');
 const raw=fs.readFileSync(path.join(evidence,c.id+'.exit'),'utf8').trim();
 if(!/^[0-9]+$/.test(raw))throw Error('bad exit receipt for '+c.id);
 const exit_code=Number(raw);
 const counts=[...stdout.matchAll(/\bresults:\s*(\d+) compiled,\s*(\d+) failed,\s*(\d+) prose \(of (\d+)\)/g)];
 const claims=[...stdout.matchAll(/\binfo: claim \d+:\s*(.+)$/gm)].map(x=>x[1]);
 const countLine=[...stdout.matchAll(/\b(\d+) definitions,\s*(\d+) claims\b/g)];
 const warnings=stdout.split('\n').filter(x=>/\bwarning:/.test(x));
 let status='tool_error',result=null;
 if(counts.length===1){
  const [compiled,failed,prose,total]=counts[0].slice(1).map(Number);
  if(total!==compiled+failed+prose||!total||countLine.length!==1)throw Error('inconsistent sentence counts for '+c.id);
  const [definitions,declaredClaims]=countLine[0].slice(1).map(Number);
  if(claims.length!==declaredClaims || (compiled===0 && declaredClaims>0))throw Error('inconsistent claim counts for '+c.id);
  result={compiled,failed,prose,total,definitions,declaredClaims};
  if(exit_code===124||exit_code===137)status='timeout_or_signal';
  else if(failed>0)status='diagnosed_failure';
  else if(exit_code!==0)status='tool_error';
  else if(compiled===total&&!warnings.some(w=>/partly checked|not checked/i.test(w)))status='statement_compiled';
  else status='unread_or_partial';
 }else if(exit_code<124)throw Error('missing results for '+c.id);
 records.push({id:c.id,category:c.category,source_sha256:sha(source),stdout_sha256:sha(stdout),stderr_sha256:sha(stderr),exit_code,status,counts:result,claims,warnings,proof_status:'not_run',semantic_equivalence:'not_checked'});
}
const aggregate={};
for(const c of m.cases){
 const a=aggregate[c.category]??={attempted:0,compiled:0,diagnosed:0,unread:0,tool_errors:0};
 const r=records.find(r=>r.id===c.id);a.attempted++;
 if(r.status==='statement_compiled')a.compiled++;else if(r.status==='diagnosed_failure')a.diagnosed++;
 else if(r.status==='unread_or_partial')a.unread++;else a.tool_errors++;
}
const report={schema_version:1,upstream_commit:vendor,phase:'statement_compilation_only',vendor_proofs:0,model_tokens:0,aggregate,records};
fs.writeFileSync(dest,JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(aggregate,null,2));
