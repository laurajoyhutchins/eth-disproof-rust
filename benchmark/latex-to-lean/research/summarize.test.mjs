import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
const root=path.dirname(new URL(import.meta.url).pathname);
const target=path.join(root,'summarize.mjs');
const manifest=JSON.parse(fs.readFileSync(path.join(root,'manifest.json'),'utf8'));
function fixture(){
 const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'latex-lean-research-'));
 const suite=path.join(tmp,'suite'),evidence=path.join(tmp,'evidence'),cases=path.join(suite,'cases');
 fs.mkdirSync(cases,{recursive:true});fs.mkdirSync(evidence,{recursive:true});
 fs.writeFileSync(path.join(suite,'manifest.json'),JSON.stringify(manifest));
 fs.writeFileSync(path.join(evidence,'vendor.sha'),manifest.upstream_commit+'\n');
 for(const x of manifest.cases){
  fs.writeFileSync(path.join(cases,x.id+'.tex'),'synthetic source '+x.id);
  fs.writeFileSync(path.join(evidence,x.id+'.stdout'),'info: claim 0: forall x, x=x\nresults: 1 compiled, 0 failed, 0 prose (of 1)\n');
  fs.writeFileSync(path.join(evidence,x.id+'.stderr'),'');
  fs.writeFileSync(path.join(evidence,x.id+'.exit'),'0\n');
 }
 return {tmp,suite,evidence,output:path.join(tmp,'report.json')};
}
function run(f){
 return spawnSync(process.execPath,[target,f.suite,f.evidence,f.output],{encoding:'utf8'});
}
test('all twelve receipts are required; they never create proof credit',t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.tmp,{recursive:true,force:true}));
 const r=run(f);assert.equal(r.status,0,r.stderr);
 const j=JSON.parse(fs.readFileSync(f.output));assert.equal(j.records.length,12);
 assert.equal(j.vendor_proofs,0);assert.equal(j.model_tokens,0);
 assert.ok(j.records.every(x=>x.proof_status==='not_run'&&x.semantic_equivalence==='not_checked'));
});
test('missing evidence refuses to score',t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.tmp,{recursive:true,force:true}));
 fs.rmSync(path.join(f.evidence,'RG01.stdout'));
 assert.notEqual(run(f).status,0);
});
test('compiler exit zero with one unread theorem earns no coverage',t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.tmp,{recursive:true,force:true}));
 fs.writeFileSync(path.join(f.evidence,'RG01.stdout'),'results: 0 compiled, 0 failed, 1 prose (of 1)\n');
 assert.equal(run(f).status,0);
 assert.equal(JSON.parse(fs.readFileSync(f.output)).records[0].status,'unread_or_partial');
});
test('forged compiled count without emitted claim fails closed',t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.tmp,{recursive:true,force:true}));
 fs.writeFileSync(path.join(f.evidence,'RG01.stdout'),'results: 1 compiled, 0 failed, 0 prose (of 1)\n');
 assert.notEqual(run(f).status,0);
});
test('incorrect upstream revision refuses to score',t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.tmp,{recursive:true,force:true}));
 fs.writeFileSync(path.join(f.evidence,'vendor.sha'),'main\n');
 assert.notEqual(run(f).status,0);
});
test('diagnostic rejections cannot count as compiled',t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.tmp,{recursive:true,force:true}));
 fs.writeFileSync(path.join(f.evidence,'RG01.stdout'),'warning: cannot parse\nresults: 0 compiled, 1 failed, 0 prose (of 1)\n');
 fs.writeFileSync(path.join(f.evidence,'RG01.exit'),'1\n');
 assert.equal(run(f).status,0);
 const r=JSON.parse(fs.readFileSync(f.output)).records[0];
 assert.equal(r.status,'diagnosed_failure');
});
