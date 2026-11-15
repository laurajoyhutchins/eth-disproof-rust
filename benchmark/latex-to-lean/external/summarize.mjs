#!/usr/bin/env node
// Summarize actual receipts and semantic reports without oracle/truth leakage.
// Call unified/verify.mjs independently first for complete source/log hash checks.
import fs from "node:fs";
import path from "node:path";
import {validateCorpus} from "./validate.mjs";
import {validateSource,select} from "../unified/contract.mjs";
import {verifySemanticCase} from "../unified/semantic.mjs";

const [src,receiptRoot,dest]=process.argv.slice(2);
if (!src||!receiptRoot||!dest||process.argv.length!==5)
  throw Error("usage: node summarize.mjs EXTERNAL_DIR RECEIPTS_DIR REPORT.json");
const root=path.resolve(src);
validateCorpus(root);
const manifest=JSON.parse(fs.readFileSync(path.join(root,"manifest.json"),"utf8"));
const results=[];
for (const item of manifest.cases) {
  const source=path.join(root,"cases",item.id+".tex");
  const folder=path.join(receiptRoot,item.id);
  const r=JSON.parse(fs.readFileSync(path.join(folder,"receipt.json"),"utf8"));
  const original=validateSource(fs.readFileSync(source));
  if (r.source?.sha256!==original.sha256||r.source?.bytes!==original.bytes ||
      JSON.stringify(r.selection)!==JSON.stringify(select(r.observations)))
    throw Error("source identity or selection mismatch "+item.id);
  if (r.verification?.kernel_checked!==false||r.verification?.proof_completed!==false||
      r.verification?.semantic_equivalence!==false)
    throw Error("parser claimed proof completion "+item.id);
  const accepted=r.observations.filter(x=>x.status==="parsed").map(x=>x.backend).sort();
  const semantic=verifySemanticCase(source,folder);
  if (accepted.length===2 && !["definitionally_equivalent","unresolved",
      "unelaboratable","tool_error","unresolved_pairing"].includes(semantic.status))
    throw Error("missing overlapping comparison "+item.id);
  if (accepted.length!==2 && semantic.status!=="not_applicable")
    throw Error("non-overlap comparison invented "+item.id);
  results.push({id:item.id,source_group:item.source_group,cohort:item.cohort,
    source_sha256:original.sha256,parsed_by:accepted,semantic_comparison:semantic.status,
    source_faithfulness:"unassessed",proof_completion:"unassessed"});
}
const countsFor=rows=>({
 total:rows.length,
 covered:rows.filter(r=>r.parsed_by.length>0).length,
 overlap:rows.filter(r=>r.parsed_by.length===2).length,
 equivalent:rows.filter(r=>r.semantic_comparison==="definitionally_equivalent").length,
 comparison_unresolved:rows.filter(r=>r.semantic_comparison==="unresolved").length,
 source_faithfulness_assessed:0,proofs_completed:0
});
const summary={
 schema_version:1,phase:"external_source_translation_and_overlap",
 caveats:["Transcriptions are not original publisher TeX bytes",
   "Neither source fidelity nor proof completion follows from parsing or equivalence",
   "OpenStax used for overlap discovery; DLMF and Nicholson are untouched author holdouts"],
 totals:countsFor(results),by_cohort:{
   overlap_discovery:countsFor(results.filter(r=>r.cohort==="overlap_discovery")),
   author_holdout:countsFor(results.filter(r=>r.cohort==="author_holdout"))
 },
 by_author:Object.fromEntries(["openstax","dlmf","nicholson"].map(name=>
   [name,countsFor(results.filter(r=>r.source_group===name))])),
 results
};
fs.writeFileSync(dest,JSON.stringify(summary,null,2)+"\n",{flag:"wx"});
console.log(JSON.stringify(summary.by_cohort));
