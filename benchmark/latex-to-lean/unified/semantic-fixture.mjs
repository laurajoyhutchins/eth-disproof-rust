#!/usr/bin/env node
// Independent, synthetic Lean fixtures. These do not measure LaTeX accuracy.
// Run inside the pinned Leanify Lake environment in deep CI.
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import {sha256,validateSource,receipt,LEANIFY_COMMIT} from "./contract.mjs";
import {runSemanticCase,verifySemanticCase} from "./semantic.mjs";

const vendor = path.resolve(process.argv[2] || "");
if (!process.argv[2] || !fs.existsSync(path.join(vendor,"lean-toolchain")))
  throw Error("usage: node semantic-fixture.mjs PATH_TO_PINNED_LEANIFY");
const dir = fs.mkdtempSync(path.join(os.tmpdir(), "semantic-fixtures-"));
const cases = [
  {name:"alpha",left:"∀ n : Nat, n = n",right:"∀ k : Nat, k = k",
    expected:"definitionally_equivalent"},
  {name:"quantifier",left:"∀ n : Nat, n = n",right:"∃ n : Nat, n = n",
    expected:"unresolved"},
  {name:"hypothesis",left:"∀ n : Nat, n = n",
    right:"∀ n : Nat, n = 0 → n = n",expected:"unresolved"},
  {name:"change-type",left:"∀ n : Nat, n = n",
    right:"∀ n : Int, n = n",expected:"unresolved"}
];
try {
  for (const item of cases) {
    const folder = path.join(dir,item.name);
    fs.mkdirSync(folder);
    const source = Buffer.from("\\begin{theorem}\\label{" + item.name + "}$n=n$\\end{theorem}");
    const sourceFile = path.join(folder,"source.tex");
    fs.writeFileSync(sourceFile,source);
    const id = validateSource(source);
    const ns = "Unified" + id.sha256.slice(0,20);
    const str = "Struct" + id.sha256.slice(0,16);
    const compiled = Buffer.from("import Mathlib.Basic.Real.Basic\n");
    const article = Buffer.from("import "+ns+".Compiled\nnamespace "+ns+
      "\ndef claim0 : Prop := "+item.left+"\nend "+ns+"\n");
    const structural = Buffer.from("import Mathlib.Basic.Real.Basic\nnamespace "+str+
      "\ndef claim : Prop := "+item.right+"\nend "+str+"\n");
    fs.mkdirSync(path.join(folder,ns));
    for (const [name,bytes] of Object.entries({"Article.lean":article,"Compiled.lean":compiled}))
      fs.writeFileSync(path.join(folder,ns,name),bytes);
    fs.writeFileSync(path.join(folder,str+".lean"),structural);
    const r = receipt({
      source:id,
      observations:[{backend:"leanify",status:"parsed",claim_count:1},
        {backend:"structural",status:"parsed",claim_count:1}],
      tools:{leanify:{commit:LEANIFY_COMMIT}}, logs:{},
      generated:{leanify:{namespace:ns,modules:{
        "Article.lean":{name:ns+"/Article.lean",sha256:sha256(article)},
        "Compiled.lean":{name:ns+"/Compiled.lean",sha256:sha256(compiled)}
      }},structural:{name:str+".lean",sha256:sha256(structural)}}});
    fs.writeFileSync(path.join(folder,"receipt.json"),JSON.stringify(r));
    const result = runSemanticCase({sourceFile,caseDir:folder,leanifyDir:vendor});
    const replay = verifySemanticCase(sourceFile, folder);
    if (replay.status !== result.status) throw Error("fixture evidence mismatch");
    console.log(item.name, result.status);
    if (result.status !== item.expected) {
      console.error("Expected", item.expected, "for", item.name);
      for (const name of ["build.stderr","elaboration.stderr","proof.stderr"]) {
        const f = path.join(folder,"semantic",name);
        if (fs.existsSync(f)) console.error(name,fs.readFileSync(f,"utf8"));
      }
      process.exitCode=1;
      break;
    }
    if (result.status === "definitionally_equivalent" && !result.checks.kernel_checked)
      throw Error("positive fixture lacked kernel check");
    if (result.status !== "definitionally_equivalent" && result.checks.kernel_checked)
      throw Error("negative fixture was granted proof credit");
  }
} finally {
  fs.rmSync(dir,{recursive:true,force:true});
}
