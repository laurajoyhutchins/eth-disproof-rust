import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import {fileURLToPath} from "node:url";
import {validateCorpus} from "./validate.mjs";
const source=path.dirname(fileURLToPath(import.meta.url));
test("corpus locks twelve cases in three independent source families",()=>{
 const v=validateCorpus(source);
 assert.equal(v.count,12);
 assert.deepEqual(v.source_groups,{dlmf:3,nicholson:2,openstax:7});
 assert.deepEqual(v.cohorts,{overlap_discovery:7,author_holdout:5});
});
test("tampering with one source byte cannot inherit a locked author identity",t=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),"external-lock-"));
 t.after(()=>fs.rmSync(dir,{recursive:true,force:true}));
 fs.cpSync(source,dir,{recursive:true});
 const input=path.join(dir,"cases","O01.tex");
 fs.appendFileSync(input," \n");
 assert.throws(()=>validateCorpus(dir),/locked source changed/);
});
test("a missing or silently inserted case cannot inherit existing coverage",t=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),"external-cases-"));
 t.after(()=>fs.rmSync(dir,{recursive:true,force:true}));
 fs.cpSync(source,dir,{recursive:true});
 fs.writeFileSync(path.join(dir,"cases","X99.tex"),"unexpected");
 assert.throws(()=>validateCorpus(dir),/manifest\/locked corpus mismatch/);
});
test("author-held-out families are not assigned discovery labels",t=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),"external-groups-"));
 t.after(()=>fs.rmSync(dir,{recursive:true,force:true}));
 fs.cpSync(source,dir,{recursive:true});
 const p=path.join(dir,"manifest.json");
 const r=JSON.parse(fs.readFileSync(p,"utf8"));
 r.cases.find(x=>x.id==="D01").cohort="overlap_discovery";
 fs.writeFileSync(p,JSON.stringify(r));
 assert.throws(()=>validateCorpus(dir),/invalid author holdout split/);
});
