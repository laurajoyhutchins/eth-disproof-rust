#!/usr/bin/env node
// Check-only compiler evidence, never proof or faithfulness credit.
import fs from 'node:fs';
import path from 'node:path';
import {sha256,classifyLeanify,LEANIFY_COMMIT} from '../unified/contract.mjs';
const [root,evidence,dest]=process.argv.slice(2);
if(!root||!evidence||!dest)throw Error('usage: summarize.mjs SUITE EVIDENCE OUTPUT');
const m=JSON.parse(fs.readFileSync(path.join(root,'manifest.json')));
if(m.schema_version!==1||m.cases.length!==12||new Set(m.cases.map(c=>c.id)).size!==12)throw Error('invalid manifest');
const vendor=fs.readFileSync(path.join(evidence,'vendor.sha'),'utf8').trim();
if(vendor!==m.upstream_commit||vendor!==LEANIFY_COMMIT)throw Error('untrusted vendor revision');
const records=[];
for(const c of m.cases){
 const source=fs.readFileSync(path.join(root,'cases',c.id+'.tex'));
 const stdout=fs.readFileSync(path.join(evidence,c.id+'.stdout'),'utf8');
 const stderr=fs.readFileSync(path.join(evidence,c.id+'.stderr'),'utf8');
 const raw=fs.readFileSync(path.join(evidence,c.id+'.exit'),'utf8').trim();
 if(!/^[0-9]+$/.test(raw))throw Error('bad exit receipt for '+c.id);
 const exit_code=Number(raw);
 const classified=classifyLeanify({stdout,stderr,exitCode:exit_code,
   timedOut:exit_code===124||exit_code===137});
 if(classified.status==='tool_error'&&exit_code<124)
   throw Error('untrustworthy native result counters for '+c.id);
 const counts=classified.counts;
 const result=counts ? {compiled:counts.compiled,failed:counts.failed,prose:counts.prose,
   total:counts.total,definitions:counts.definitions,declaredClaims:counts.claimsDeclared} : null;
 const claims=classified.claims??[];
 const warnings=classified.diagnostics;
 const status=({
   parsed:'statement_compiled',
   diagnosed_failure:'diagnosed_failure',
   unsupported_or_partial:'unread_or_partial',
   timeout:'timeout_or_signal',
   tool_error:'tool_error'
 })[classified.status];
 records.push({id:c.id,category:c.category,source_sha256:sha256(source),stdout_sha256:sha256(stdout),stderr_sha256:sha256(stderr),exit_code,status,counts:result,claims,warnings,proof_status:'not_run',semantic_equivalence:'not_checked'});
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
