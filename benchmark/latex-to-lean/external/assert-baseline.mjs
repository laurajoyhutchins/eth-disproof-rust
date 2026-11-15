#!/usr/bin/env node
// Freeze observed pipeline outcomes, not mathematical truth labels.
// A deliberate change to a frozen result requires an explicit baseline review.
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import {fileURLToPath} from "node:url";

const ownDir=path.dirname(fileURLToPath(import.meta.url));
const fields={
  research:["total","covered","leanify","structural","conflicts","unverified"],
  holdout:["total","covered","leanify","structural","conflicts","unverified"],
  external:["total","covered","leanify","structural","conflicts","unverified"],
  discovery:["total","covered","overlap","equivalent","normalized_equivalent","comparison_unresolved",
    "source_faithfulness_assessed","proofs_completed"],
  author_holdout:["total","covered","overlap","equivalent","normalized_equivalent","comparison_unresolved",
    "source_faithfulness_assessed","proofs_completed"],
  oracle:["total","generated_translations","reference_matches","no_definitional_match",
    "tool_errors","audited_source_faithfulness"]
};
const select=(row,keys)=>Object.fromEntries(keys.map(k=>[k,row?.[k]]));
const read=p=>JSON.parse(fs.readFileSync(p,"utf8"));

export function auditBaseline(reports,expected) {
  assert.equal(expected.schema_version,1,"unsupported frozen baseline");
  const sources=["research","holdout","external"];
  for(const key of sources) {
    const r=reports[key];
    assert.equal(r.schema_version,1,key+" schema changed");
    assert.equal(r.phase,"statement_parsing_only",key+" phase changed");
    assert.equal(r.results.length,r.counts.total,key+" total/result mismatch");
    assert.deepEqual(select(r.counts,fields[key]),expected[key],
      key+" differs from frozen parsing baseline");
    assert.ok(r.results.every(x=>x.kernel_verified===false),
      key+" wrongly granted kernel proof credit");
    assert.equal(new Set(r.results.map(x=>x.id)).size,r.results.length,
      key+" duplicate case identity");
  }
  const external=reports.externalSummary;
  assert.equal(external.schema_version,1,"external semantic schema changed");
  assert.equal(external.phase,"external_source_translation_and_overlap",
    "external semantic phase changed");
  assert.equal(external.results.length,reports.external.results.length,
    "semantic and parsing case counts differ");
  assert.deepEqual(select(external.by_cohort?.overlap_discovery,fields.discovery),
    expected.discovery,"overlap discovery baseline changed");
  assert.deepEqual(select(external.by_cohort?.author_holdout,fields.author_holdout),
    expected.author_holdout,"source-group held-out baseline changed");
  const extRows=new Map(external.results.map(x=>[x.id,x]));
  assert.equal(extRows.size,reports.external.results.length,"duplicated semantic case");
  for(const row of reports.external.results) {
    const translated=extRows.get(row.id);
    assert.ok(translated && translated.source_sha256===row.source_sha256,
      "semantic result not bound to original source "+row.id);
    assert.equal(translated.source_faithfulness,"unassessed",
      "source-faithfulness credit must be independently reviewed");
    assert.equal(translated.proof_completion,"unassessed",
      "backend parsing is not proof completion");
  }
  const oracle=reports.oracle;
  assert.equal(oracle.schema_version,1,"source oracle schema changed");
  assert.equal(oracle.status,"completed","source oracle did not finish");
  assert.equal(oracle.source_review,"pending","source review must not be invented");
  assert.equal(oracle.results.length,reports.external.results.length,
    "source oracle has missing cases");
  assert.deepEqual(select(oracle.totals,fields.oracle),expected.oracle,
    "typed source-reference results differ from frozen baseline");
  const oracleRows=new Map(oracle.results.map(x=>[x.id,x]));
  assert.equal(oracleRows.size,oracle.results.length,"duplicate source oracle case");
  for(const row of reports.external.results) {
    const oracleRow=oracleRows.get(row.id);
    assert.ok(oracleRow && oracleRow.source_sha256===row.source_sha256,
      "oracle evidence unbound to original source "+row.id);
    assert.equal(oracleRow.independent_text_review,"pending",
      "unreviewed oracle is not a human source audit");
  }
  return {status:"frozen_baseline_matched",source_cases:12,
    reference_matches:oracle.totals.reference_matches,
    reference_nonmatches:oracle.totals.no_definitional_match};
}
export function readReports(root) {
  return {
    research:read(path.join(root,"research-coverage.json")),
    holdout:read(path.join(root,"holdout-coverage.json")),
    external:read(path.join(root,"external-coverage.json")),
    externalSummary:read(path.join(root,"external-summary.json")),
    oracle:read(path.join(root,"external-oracle","summary.json"))
  };
}
if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  if(process.argv.length!==3)
    throw Error("usage: node assert-baseline.mjs EVIDENCE_ROOT");
  const expected=read(path.join(ownDir,"baseline.json"));
  console.log(JSON.stringify(auditBaseline(readReports(path.resolve(process.argv[2])),expected)));
}
