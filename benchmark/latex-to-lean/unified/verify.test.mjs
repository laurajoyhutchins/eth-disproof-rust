import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import {spawnSync} from "node:child_process";
import {receipt,sha256,validateSource,LEANIFY_COMMIT} from "./contract.mjs";

const binary="a".repeat(64);
function fixture(){
 const root=fs.mkdtempSync(path.join(os.tmpdir(),"latex-receipts-"));
 const sources=path.join(root,"sources"),runs=path.join(root,"runs");
 fs.mkdirSync(sources);fs.mkdirSync(runs);
 for(const id of ["A01","B99"]){
  const bytes=Buffer.from("\\begin{theorem} $x=x$ \\end{theorem}\n"+id);
  fs.writeFileSync(path.join(sources,id+".tex"),bytes);
  const dir=path.join(runs,id);fs.mkdirSync(dir);
  const logs={};
  for(const name of ["leanify.stdout","leanify.stderr","structural.stdout","structural.stderr"]){
    const data=name==="leanify.stdout"?"0 definitions, 1 claims\ninfo: claim 0: x=x\nresults: 1 compiled, 0 failed, 0 prose (of 1)":"";
    fs.writeFileSync(path.join(dir,name),data);
    logs[name.replace(".","_")+"_sha256"]=sha256(Buffer.from(data));
  }
  const report=receipt({
    source:validateSource(bytes),
    observations:[{backend:"leanify",status:"parsed",claim_count:1},
      {backend:"structural",status:"diagnosed_failure",claim_count:0}],
    tools:{leanify:{commit:LEANIFY_COMMIT},structural:{binary_sha256:binary}},
    generated:{},logs
  });
  fs.writeFileSync(path.join(dir,"receipt.json"),JSON.stringify(report));
 }
 const output=path.join(root,"summary.json");
 return {root,sources,runs,output};
}
function run(f,flags=[]){
 return spawnSync(process.execPath,[path.join(import.meta.dirname,"verify.mjs"),f.sources,f.runs,f.output,...flags],{encoding:"utf8"});
}
test("verifies independent source and log hashes for arbitrary IDs",t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.root,{recursive:true,force:true}));
 const x=run(f,["--require-coverage"]);assert.equal(x.status,0,x.stderr);
 const r=JSON.parse(fs.readFileSync(f.output));
 assert.equal(r.counts.covered,2);assert.equal(r.counts.leanify,2);
 assert.equal(r.counts.unverified,2);
});
test("source tampering is never scored",t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.root,{recursive:true,force:true}));
 fs.appendFileSync(path.join(f.sources,"A01.tex")," ");
 assert.notEqual(run(f).status,0);
});
test("forged kernel verification is rejected",t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.root,{recursive:true,force:true}));
 const file=path.join(f.runs,"B99","receipt.json"),r=JSON.parse(fs.readFileSync(file));
 r.verification.proof_completed=true;fs.writeFileSync(file,JSON.stringify(r));
 assert.notEqual(run(f).status,0);
});
test("tampered output logs are rejected",t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.root,{recursive:true,force:true}));
 fs.appendFileSync(path.join(f.runs,"B99","leanify.stdout"),"new output");
 assert.notEqual(run(f).status,0);
});
test("fabricated backend selection is rejected",t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.root,{recursive:true,force:true}));
 const file=path.join(f.runs,"A01","receipt.json"),r=JSON.parse(fs.readFileSync(file));
 r.selection.status="proof_completed";fs.writeFileSync(file,JSON.stringify(r));
 assert.notEqual(run(f).status,0);
});
test("missing receipt cannot be silently skipped",t=>{
 const f=fixture();t.after(()=>fs.rmSync(f.root,{recursive:true,force:true}));
 fs.rmSync(path.join(f.runs,"A01","receipt.json"));
 assert.notEqual(run(f).status,0);
});
