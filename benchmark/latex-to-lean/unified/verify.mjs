#!/usr/bin/env node
// Cross-backend receipt verifier. No fixed case IDs or mathematical truth labels.
import fs from "node:fs";
import path from "node:path";
import {sha256,select,validateSource,LEANIFY_COMMIT} from "./contract.mjs";

const [sourceDir,receiptDir,outputFile,...flags]=process.argv.slice(2);
if(!sourceDir||!receiptDir||!outputFile||flags.some(f=>f!=="--require-coverage"))
  throw Error("usage: node verify.mjs SOURCE_DIR RECEIPTS_DIR OUTPUT.json [--require-coverage]");
const requireCoverage=flags.includes("--require-coverage");
const files=fs.readdirSync(sourceDir).filter(x=>x.endsWith(".tex")).sort();
if(!files.length)throw Error("empty source corpus");
const results=[];
for(const file of files){
 const id=file.slice(0,-4);
 if(!/^[A-Za-z][A-Za-z0-9_-]*$/.test(id))throw Error("unsafe case name "+id);
 const folder=path.join(receiptDir,id);
 const record=JSON.parse(fs.readFileSync(path.join(folder,"receipt.json"),"utf8"));
 const source=validateSource(fs.readFileSync(path.join(sourceDir,file)));
 if(record.schema_version!==1||record.source.sha256!==source.sha256||
    record.source.bytes!==source.bytes)throw Error("source identity mismatch "+id);
 if(record.tools.leanify?.commit!==LEANIFY_COMMIT ||
    !/^[0-9a-f]{64}$/.test(record.tools.structural?.binary_sha256||""))
    throw Error("wrong tool identity "+id);
 if(!Array.isArray(record.observations)||record.observations.length!==2)
    throw Error("missing backend evidence "+id);
 const choice=select(record.observations);
 if(JSON.stringify(choice)!==JSON.stringify(record.selection))
    throw Error("forged backend selection "+id);
 if(record.verification?.kernel_checked!==false||
    record.verification?.semantic_equivalence!==false||
    record.verification?.proof_completed!==false)
    throw Error("parser output falsely asserts verification "+id);
 const logs=["leanify.stdout","leanify.stderr","structural.stdout","structural.stderr"];
 for(const name of logs){
  const key=name.replace(".","_")+"_sha256";
  const got=sha256(fs.readFileSync(path.join(folder,name)));
  if(record.logs[key]!==got)throw Error("log hash mismatch "+id+" "+name);
 }
 if(record.generated.structural){
  if(record.observations.find(x=>x.backend==="structural").status!=="parsed")
    throw Error("generated Lean without structural acceptance "+id);
  const gen=record.generated.structural;
  if(gen.name.includes("/")||gen.name.includes("\\")||!gen.name.endsWith(".lean"))
    throw Error("invalid generated pathname "+id);
  if(sha256(fs.readFileSync(path.join(folder,gen.name)))!==gen.sha256)
    throw Error("generated Lean hash mismatch "+id);
 }
 const parsed=record.observations.filter(x=>x.status==="parsed").map(x=>x.backend).sort();
 results.push({id,source_sha256:source.sha256,parsed_by:parsed,selection:choice.status,
   kernel_verified:false});
}
const counts={total:results.length,covered:results.filter(x=>x.parsed_by.length>0).length,
  leanify:results.filter(x=>x.parsed_by.includes("leanify")).length,
  structural:results.filter(x=>x.parsed_by.includes("structural")).length,
  conflicts:results.filter(x=>x.parsed_by.length===2).length,
  unverified:results.length};
const report={schema_version:1,phase:"statement_parsing_only",counts,results};
fs.writeFileSync(outputFile,JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(counts));
if(requireCoverage&&counts.covered!==counts.total)process.exitCode=2;
