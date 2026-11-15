import test from "node:test";
import assert from "node:assert/strict";
import {Buffer} from "node:buffer";
import {validateSource,classifyLeanify,classifyStructural,select,receipt} from "./contract.mjs";

const compiled=(claims=1,sentences=1)=>({
 stdout:[...Array.from({length:claims},(_,i)=>"info: claim "+i+": forall x, x = x"),
  "0 definitions, "+claims+" claims",
  "results: "+sentences+" compiled, 0 failed, 0 prose (of "+sentences+")"].join("\n"),
 stderr:"",exitCode:0
});
const unsupported={stdout:"0 definitions, 0 claims\nresults: 0 compiled, 0 failed, 1 prose (of 1)",
 stderr:"",exitCode:0};
const structural=(ns="StructAbcd")=>({exitCode:0,stderr:"",outputText:
 "import Mathlib.Basic.Real.Basic\nimport Mathlib.LinearAlgebra.Matrix.Notation\n"+
 "import Mathlib.Data.Fintype.BigOperators\nopen scoped Matrix\nnamespace "+ns+
 "\ndef claim : Prop := (1=1)\nend "+ns+"\n"});

test("source identity is exact raw-byte SHA-256, accepts original LaTeX theorem",()=>{
 const b=Buffer.from("\\documentclass{article}\\newtheorem{theorem}{Theorem}\\begin{theorem} $1=1$ \\end{theorem}\n");
 const x=validateSource(b);
 assert.match(x.sha256,/^[a-f0-9]{64}$/);assert.equal(x.bytes,b.length);
 assert.notEqual(validateSource(Buffer.concat([b,Buffer.from(" ")])).sha256,x.sha256);
});
test("reject dynamic or unpinned TeX inputs and invalid encoding",()=>{
 for(const x of ["\\input{secret}","\\catcode=0","\\newcommand{\\x}{1}","\\include{other}"])
  assert.throws(()=>validateSource(Buffer.from(x)),/dynamic TeX/);
 assert.throws(()=>validateSource(Buffer.from([0xff,0xfe])));
 assert.throws(()=>validateSource(Buffer.alloc(1_000_001)));
});
test("one sentence may emit multiple claims",()=>{
 for(const n of [1,2,3,5,12]){
  const r=classifyLeanify(compiled(n));
  assert.equal(r.status,"parsed");assert.equal(r.claim_count,n);
 }
});
test("zero exit without translated claims is unsupported",()=>{
 const r=classifyLeanify(unsupported);
 assert.equal(r.status,"unsupported_or_partial");assert.equal(r.claim_count,0);
});
test("diagnostic rejection is not a tool crash or mathematical proof",()=>{
 const r=classifyLeanify({stdout:"warning: ambiguous notation\n0 definitions, 0 claims\nresults: 0 compiled, 1 failed, 0 prose (of 1)",
  stderr:"",exitCode:1});
 assert.equal(r.status,"diagnosed_failure");
});
test("counter mismatches or duplicate summaries fail closed",()=>{
 for(const x of [
  {stdout:"0 definitions, 1 claims\nresults: 1 compiled, 0 failed, 0 prose (of 1)",exitCode:0},
  {stdout:compiled().stdout+"\n"+compiled().stdout,exitCode:0},
  {stdout:"0 definitions, 1 claims\ninfo: claim 0: ok\nresults: 1 compiled, 2 failed, 0 prose (of 2)",exitCode:0}
 ]) assert.equal(classifyLeanify(x).status,"tool_error");
});
test("partial prose or warning never receives full coverage",()=>{
 const r=classifyLeanify({
  stdout:"warning: partly checked\ninfo: claim 0: example\n0 definitions, 1 claims\nresults: 1 compiled, 0 failed, 1 prose (of 2)",
  exitCode:0});
 assert.equal(r.status,"unsupported_or_partial");
});
test("structural result needs generated Lean, not merely exit zero",()=>{
 assert.equal(classifyStructural({...structural(),outputText:null},"StructAbcd").status,"tool_error");
 assert.equal(classifyStructural(structural(),"StructAbcd").status,"parsed");
 assert.equal(classifyStructural(structural(),"StructOther").status,"tool_error");
});
test("typability errors refuse without altering propositions",()=>{
 const r=classifyStructural({exitCode:1,stderr:"types: expected vector dimension 3, got 2"},"StructAbcd");
 assert.equal(r.status,"diagnosed_failure");assert.equal(r.claim_count,0);
});
test("a singleton accepted backend stays unverified",()=>{
 const observations=[classifyLeanify(compiled()),classifyStructural({exitCode:1,stderr:"theorem: unsupported grammar"},"N")];
 const result=receipt({source:validateSource(Buffer.from("$1=1$")),observations,tools:{},generated:{},logs:{}});
 assert.equal(result.selection.backend,"leanify");
 assert.equal(result.selection.status,"translation_requires_kernel_review");
 assert.equal(result.verification.semantic_equivalence,false);
 assert.equal(result.verification.kernel_checked,false);
 assert.equal(result.verification.proof_completed,false);
});
test("two translated claims are never silently chosen",()=>{
 const x=select([classifyLeanify(compiled()),classifyStructural(structural(),"StructAbcd")]);
 assert.equal(x.status,"conflict_requires_equivalence");assert.equal(x.backend,null);
});
test("failed tool blocks selection even when another parser succeeds",()=>{
 const x=select([classifyLeanify(compiled()),{backend:"structural",status:"tool_error"}]);
 assert.equal(x.status,"incomplete");assert.equal(x.backend,null);
});
test("broad claim-count and source-size tests independent of original cases",()=>{
 for(let n=1;n<=25;n++){
  const source=Buffer.from("$"+n+"="+n+"$");
  assert.match(validateSource(source).sha256,/^[a-f0-9]{64}$/);
  assert.equal(classifyLeanify(compiled(n)).claim_count,n);
 }
});
