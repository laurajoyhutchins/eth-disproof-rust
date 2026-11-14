#!/usr/bin/env node
// Fail-closed evidence join. Call only after Lean and all Leanify audits exit 0.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';

const [root,evidence,out] = process.argv.slice(2);
if (!root || !evidence || !out) throw Error('usage: verify-receipts.mjs SUITE EVIDENCE OUTPUT');
const read = p => fs.readFileSync(path.join(evidence,p),'utf8');
const digest = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const manifest = JSON.parse(fs.readFileSync(path.join(root,'manifest.json'),'utf8'));
const parser = JSON.parse(read('summary.json'));
if (manifest.cases.length !== 12 || parser.records.length !== 12 ||
    manifest.upstream_commit !== parser.upstream_commit) throw Error('invalid corpus or upstream identity');

const claims = {
 RG01:['rg01_claim0_exact','rg01_claim1_exact'],
 RG03:['rg03_exact_statement'],
 RS02:['rs02_reconstruction_first_exact','rs02_reconstruction_second_exact'],
 RS03:['rs03_claim0_exact','rs03_claim1_exact'],
 RS04:['rs04_claim0_exact','rs04_claim1_exact'],
 RC01:['rc01_exact_statement'],
 RC02:['rc02_exact_statement'],
 RC03:['rc03_exact_statement']
};
const denotations = ['rg01_u_denotation','rg01_v_denotation','rs03_even_denotation',
 'rs03_odd_denotation','rs04_even_denotation','rs04_odd_denotation'];
const proofChecks = ['rg03_proof','rs02_first_proof','rs02_second_proof'];
const whitelist = new Set(['propext','Classical.choice','Quot.sound']);
const expectedNames = Object.values(claims).flat().concat(denotations,proofChecks);
if (expectedNames.length !== 21) throw Error('incorrect theorem roster');
function auditAxioms(stdout) {
 if (stdout.includes('sorryAx')) throw Error('sorryAx in proof record');
 const receipts = new Map();
 const rx = /^'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$/gm;
 for (const m of stdout.matchAll(rx)) {
   const name = m[1], axioms = m[3] ? m[3].split(',').map(x=>x.trim()) : [];
   if (receipts.has(name)) throw Error('duplicate proof record: '+name);
   if (axioms.some(a=>!whitelist.has(a))) throw Error('unexpected axiom in '+name);
   receipts.set(name,axioms);
 }
 return receipts;
}
const semantics = auditAxioms(read('generated/Semantics.stdout'));
if (semantics.size !== expectedNames.length ||
  expectedNames.some(n=>!semantics.has('ResearchGenerated.'+n)))
 throw Error('missing, duplicated or unexpected source-equivalence proof');

const byId = new Map(parser.records.map(r=>[r.id,r]));
if (byId.size !== manifest.cases.length) throw Error('duplicate case receipts');
const verified = [];
for (const c of manifest.cases) {
 const r = byId.get(c.id);
 if (!r || r.category !== c.category) throw Error('wrong case identity '+c.id);
 const source = fs.readFileSync(path.join(root,'cases',c.id+'.tex'));
 if (digest(source) !== r.source_sha256) throw Error('original source modified: '+c.id);
 if (r.status !== 'statement_compiled') {
   if (claims[c.id]) throw Error('expected compiled case was refused: '+c.id);
   verified.push({id:c.id,status:'unsupported',source_sha256:r.source_sha256,
     semantic_claims_verified:0,audit_verified:false});
   continue;
 }
 const expected = claims[c.id];
 if (!expected || expected.length !== r.claims.length) throw Error('claim count changed: '+c.id);
 const genSourceHash = read('generated/'+c.id+'.sha256').trim().split(/\s+/)[0];
 if (genSourceHash !== r.source_sha256) throw Error('generated source identity differs: '+c.id);
 for (const suffix of ['Article','Compiled']) {
   if (!read('generated/'+c.id+'.'+suffix+'.lean').includes('Research'+c.id))
     throw Error('wrong generated module: '+c.id);
 }
 const stdout = read('audit/'+c.id+'.stdout');
 const proof = auditAxioms(stdout), auditName='Research'+c.id+'.Audit.built';
 if (proof.size !== 1 || !proof.has(auditName) ||
     !stdout.includes('The kernel evaluated the compiler on Research'+c.id+'/article.tex'))
   throw Error('missing kernel audit: '+c.id);
 verified.push({id:c.id,status:'kernel_source_correspondence',
   source_sha256:r.source_sha256,semantic_claims_verified:expected.length,
   semantic_theorems:expected.map(n=>'ResearchGenerated.'+n),
   audit_verified:true,audit_theorem:auditName});
}
const accepted = verified.filter(x=>x.audit_verified);
const claimCount = accepted.reduce((s,x)=>s+x.semantic_claims_verified,0);
if (accepted.length !== 8 || claimCount !== 12) throw Error('unexpected acceptance totals');
const report={schema_version:2,upstream_commit:manifest.upstream_commit,
  semantics:'Lean CI kernel-checked generated source correspondences (not tool-produced proofs)',
  parsed_cases:12,accepted_cases:8,generated_claims_verified:claimCount,
  source_compilation_audits:8,function_denotations_verified:denotations.length,
  separately_proved_generated_claims:proofChecks.length,
  independently_proved_gold_theorems:11,model_tokens:0,
  vendor_produced_mathematical_proofs:0,verified};
fs.writeFileSync(out,JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({accepted_cases:accepted.length,claims:claimCount,audits:8},null,2));
