import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import {sha256,validateSource,receipt,LEANIFY_COMMIT} from "./contract.mjs";
import {prepareSemanticCase,makeProbes,runSemanticCase} from "./semantic.mjs";

function fixture(t,{claims=1,left="∀ n : Nat, n = n",right="∀ m : Nat, m = m"}={}) {
  const root=fs.mkdtempSync(path.join(os.tmpdir(),"semantic-test-"));
  t.after(()=>fs.rmSync(root,{recursive:true,force:true}));
  const source=Buffer.from("\\begin{theorem} $x=x$ \\end{theorem}");
  const sourceFile=path.join(root,"input.tex");
  fs.writeFileSync(sourceFile,source);
  const id=validateSource(source);
  const leftNS="Unified"+id.sha256.slice(0,20);
  const rightNS="Struct"+id.sha256.slice(0,16);
  const article=Buffer.from("import "+leftNS+".Compiled\nnamespace "+leftNS+
    "\ndef claim0 : Prop := "+left+"\nend "+leftNS+"\n");
  const compiled=Buffer.from("import Mathlib.Basic.Real.Basic\n");
  const structural=Buffer.from("import Mathlib.Basic.Real.Basic\nnamespace "+rightNS+
    "\ndef claim : Prop := "+right+"\nend "+rightNS+"\n");
  fs.mkdirSync(path.join(root,leftNS));
  fs.writeFileSync(path.join(root,leftNS,"Article.lean"),article);
  fs.writeFileSync(path.join(root,leftNS,"Compiled.lean"),compiled);
  fs.writeFileSync(path.join(root,rightNS+".lean"),structural);
  const r=receipt({source:id,observations:[
    {backend:"leanify",status:"parsed",claim_count:claims},
    {backend:"structural",status:"parsed",claim_count:1}],
    tools:{leanify:{commit:LEANIFY_COMMIT}},generated:{
      leanify:{namespace:leftNS,modules:{
        "Article.lean":{name:leftNS+"/Article.lean",sha256:sha256(article)},
        "Compiled.lean":{name:leftNS+"/Compiled.lean",sha256:sha256(compiled)}
      }},structural:{name:rightNS+".lean",sha256:sha256(structural)}
    },logs:{}});
  fs.writeFileSync(path.join(root,"receipt.json"),JSON.stringify(r));
  return {root,sourceFile,source,leftNS,rightNS};
}
test("probes use actual declarations with one common Lean elaboration environment",t=>{
  const f=fixture(t), prepared=prepareSemanticCase(f.source,f.root);
  assert.equal(prepared.status,"ready");
  const {typed,proof}=makeProbes(prepared);
  assert.match(typed,new RegExp("import "+f.leftNS+"\\.Article"));
  assert.match(typed,new RegExp("private def left : Prop := "+f.leftNS+"\\.claim0"));
  assert.match(typed,new RegExp("private def right : Prop := "+f.rightNS+"\\.claim"));
  assert.match(proof,/definitional_equivalence : left ↔ right := by rfl/);
  assert.ok(!proof.includes("sorry"));
});
test("corrupted source, selected backend or module hashes reject comparison",t=>{
  const f=fixture(t);
  assert.throws(()=>prepareSemanticCase(Buffer.from("other"),f.root),/identity mismatch/);
  const recFile=path.join(f.root,"receipt.json");
  const rec=JSON.parse(fs.readFileSync(recFile,"utf8"));
  rec.selection.backend="leanify";
  fs.writeFileSync(recFile,JSON.stringify(rec));
  assert.throws(()=>prepareSemanticCase(f.source,f.root),/backend selection/);
  rec.selection.backend=null;
  fs.writeFileSync(recFile,JSON.stringify(rec));
  fs.appendFileSync(path.join(f.root,f.leftNS,"Article.lean"),"\n-- changed");
  assert.throws(()=>prepareSemanticCase(f.source,f.root),/hash mismatch/);
});
test("multiple claims are not paired by position or guessed",t=>{
  const f=fixture(t,{claims:2});
  assert.equal(prepareSemanticCase(f.source,f.root).status,"unresolved_pairing");
});
test("identical proposition shape does not imply source faithfulness",t=>{
  const f=fixture(t);
  const fake=(command,args)=>{
    if(command==="git")return {exit_code:0,stdout:LEANIFY_COMMIT+"\n",stderr:""};
    if(args.includes("--version"))return {exit_code:0,stdout:"Lean 4.34.0\n",stderr:""};
    return {exit_code:0,stdout:"",stderr:""};
  };
  const record=runSemanticCase({sourceFile:f.sourceFile,caseDir:f.root,
    leanifyDir:path.join(f.root,"vendor"),executeCommand:fake});
  assert.equal(record.status,"definitionally_equivalent");
  assert.equal(record.checks.kernel_checked,true);
  assert.equal(record.semantic_faithfulness,"not_assessed");
  assert.equal(record.proof_completion,"not_assessed");
});
test("negative proof attempt is unresolved, never evidence of conflict",t=>{
  const f=fixture(t,{right:"∃ m : Nat, m = m"});
  const fake=(command,args)=>{
    if(command==="git")return {exit_code:0,stdout:LEANIFY_COMMIT+"\n",stderr:""};
    if(args.includes("--version"))return {exit_code:0,stdout:"Lean 4.34.0\n",stderr:""};
    if(args.at(-1)?.endsWith("Proof.lean"))return {exit_code:1,stdout:"",stderr:"unsolved goals"};
    return {exit_code:0,stdout:"",stderr:""};
  };
  const record=runSemanticCase({sourceFile:f.sourceFile,caseDir:f.root,
    leanifyDir:path.join(f.root,"vendor"),executeCommand:fake});
  assert.equal(record.status,"unresolved");
  assert.equal(record.checks.both_typed,true);
  assert.equal(record.checks.kernel_checked,false);
});
test("semantic report is append-only",t=>{
  const f=fixture(t,{claims:2});
  const args={sourceFile:f.sourceFile,caseDir:f.root,leanifyDir:f.root};
  runSemanticCase(args);
  assert.throws(()=>runSemanticCase(args),/EEXIST/);
});
