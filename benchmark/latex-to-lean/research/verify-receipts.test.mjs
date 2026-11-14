import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import crypto from 'node:crypto';
import {spawnSync} from 'node:child_process';

const dir = path.dirname(new URL(import.meta.url).pathname);
const executable = path.join(dir,'verify-receipts.mjs');
const ids = 'RG01 RG02 RG03 RG04 RS01 RS02 RS03 RS04 RC01 RC02 RC03 RC04'.split(' ');
const claims = {
 RG01:['rg01_claim0_exact','rg01_claim1_exact'],RG03:['rg03_exact_statement'],
 RS02:['rs02_reconstruction_first_exact','rs02_reconstruction_second_exact'],
 RS03:['rs03_claim0_exact','rs03_claim1_exact'],
 RS04:['rs04_claim0_exact','rs04_claim1_exact'],
 RC01:['rc01_exact_statement'],RC02:['rc02_exact_statement'],
 RC03:['rc03_exact_statement']
};
const additional = 'rg01_u_denotation rg01_v_denotation rs03_even_denotation rs03_odd_denotation rs04_even_denotation rs04_odd_denotation rg03_proof rs02_first_proof rs02_second_proof'.split(' ');
const sha = s => crypto.createHash('sha256').update(s).digest('hex');
const axiom = name => "'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n";
const mkdir = p => fs.mkdirSync(p,{recursive:true});

function fixture() {
 const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'research-audits-'));
 const suite=path.join(tmp,'suite'), evidence=path.join(tmp,'evidence');
 mkdir(path.join(suite,'cases'));
 mkdir(path.join(evidence,'generated'));
 mkdir(path.join(evidence,'audit'));
 const manifest={schema_version:1,upstream_commit:'a'.repeat(40),cases:[]};
 const parsed={upstream_commit:manifest.upstream_commit,records:[]};
 for(const id of ids) {
   const category=id.startsWith('RG')?'group_actions':id.startsWith('RS')?
      'spectral_decomposition':'combinatorial_counting';
   const tex='source '+id+'\n', checksum=sha(tex);
   fs.writeFileSync(path.join(suite,'cases',id+'.tex'),tex);
   manifest.cases.push({id,category});
   parsed.records.push({id,category,source_sha256:checksum,
     status:claims[id]?'statement_compiled':'diagnosed_failure',
     claims:claims[id]||[]});
   if (claims[id]) {
      fs.writeFileSync(path.join(evidence,'generated',id+'.sha256'),checksum+'  Research'+id+'/article.tex\n');
      for(const suffix of ['Article','Compiled'])
       fs.writeFileSync(path.join(evidence,'generated',id+'.'+suffix+'.lean'),'Research'+id+'\n');
      fs.writeFileSync(path.join(evidence,'audit',id+'.stdout'),
       axiom('Research'+id+'.Audit.built')+
       'The kernel evaluated the compiler on Research'+id+'/article.tex\n');
   }
 }
 fs.writeFileSync(path.join(suite,'manifest.json'),JSON.stringify(manifest));
 fs.writeFileSync(path.join(evidence,'summary.json'),JSON.stringify(parsed));
 const expected=Object.values(claims).flat().concat(additional).map(n=>'ResearchGenerated.'+n);
 fs.writeFileSync(path.join(evidence,'generated','Semantics.stdout'),expected.map(axiom).join(''));
 return {tmp,suite,evidence,output:path.join(tmp,'report.json')};
}
const invoke = f => spawnSync(process.execPath,
  [executable,f.suite,f.evidence,f.output],{encoding:'utf8'});

test('all twelve correspondences and eight audits accepted with complete receipts',t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.tmp,{recursive:true,force:true}));
 const r=invoke(f);assert.equal(r.status,0,r.stderr);
 const result=JSON.parse(fs.readFileSync(f.output));
 assert.equal(result.generated_claims_verified,12);
 assert.equal(result.source_compilation_audits,8);
 assert.equal(result.vendor_produced_mathematical_proofs,0);
});
for (const [description,breakReceipt] of [
 ['missing compiler audit',f=>fs.rmSync(path.join(f.evidence,'audit','RG03.stdout'))],
 ['tampered source',f=>fs.writeFileSync(path.join(f.suite,'cases','RG03.tex'),'tampered')],
 ['tampered generated source hash',f=>fs.writeFileSync(path.join(f.evidence,'generated','RG03.sha256'),'f'.repeat(64)+'  path\n')],
 ['unexpected axiom',f=>{
    const p=path.join(f.evidence,'generated','Semantics.stdout');
    fs.writeFileSync(p,fs.readFileSync(p,'utf8').replace('Quot.sound','injected.customAxiom'));
 }],
 ['missing equivalence proof receipt',f=>{
    const p=path.join(f.evidence,'generated','Semantics.stdout');
    fs.writeFileSync(p,fs.readFileSync(p,'utf8').replace(/^'ResearchGenerated.rc01_exact_statement'.*\n/m,''));
 }]
]) test('fails closed on '+description,t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.tmp,{recursive:true,force:true}));
 breakReceipt(f);
 assert.notEqual(invoke(f).status,0);
});
