import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import {fileURLToPath} from "node:url";
const root=path.dirname(fileURLToPath(import.meta.url));
const manifest=JSON.parse(fs.readFileSync(path.join(root,"manifest.json"),"utf8"));
const audit=JSON.parse(fs.readFileSync(path.join(root,"source-crosscheck.json"),"utf8"));
test("crosscheck covers each frozen source without claiming independent human audit",()=>{
 assert.equal(audit.schema_version,1);
 assert.match(audit.review_method,/not an independent human audit/);
 assert.equal(audit.source_faithfulness_credit,"not_assessed");
 assert.equal(audit.automatic_verification,false);
 assert.deepEqual(audit.findings.map(x=>x.id).sort(),manifest.cases.map(x=>x.id).sort());
 assert.ok(audit.findings.every(x=>x.equation_status==="formula_matches"));
});
test("domain specializations and the unformalized complex binomial are never silently broadened",()=>{
 const byId=Object.fromEntries(audit.findings.map(x=>[x.id,x]));
 assert.equal(byId.D02.domain_or_notation,"oracle_absent");
 assert.equal(byId.D03.domain_or_notation,"complex_matrix_specialization");
 for(const id of ["N01","N02"])
   assert.equal(byId[id].domain_or_notation,"real_matrix_specialization");
 assert.equal(byId.O07.domain_or_notation,"parentheses_normalized");
});
