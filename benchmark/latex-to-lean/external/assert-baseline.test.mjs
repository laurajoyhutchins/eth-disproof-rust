import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import {fileURLToPath} from "node:url";
import {auditBaseline} from "./assert-baseline.mjs";

const baseDir=path.dirname(fileURLToPath(import.meta.url));
const expected=JSON.parse(fs.readFileSync(path.join(baseDir,"baseline.json"),"utf8"));
function fakeReports() {
  const rows=(n,prefix)=>Array.from({length:n},(_,i)=>({
    id:prefix+String(i+1).padStart(2,"0"),source_sha256:"a".repeat(64),
    kernel_verified:false
  }));
  const research=rows(12,"R"),holdout=rows(6,"H"),external=rows(12,"E");
  const original=(data,counts)=>({
    schema_version:1,phase:"statement_parsing_only",
    counts:structuredClone(counts),results:data
  });
  return {
    research:original(research,expected.research),
    holdout:original(holdout,expected.holdout),
    external:original(external,expected.external),
    externalSummary:{
      schema_version:1,phase:"external_source_translation_and_overlap",
      by_cohort:{overlap_discovery:structuredClone(expected.discovery),
        author_holdout:structuredClone(expected.author_holdout)},
      results:external.map(x=>({id:x.id,source_sha256:x.source_sha256,
        source_faithfulness:"unassessed",proof_completion:"unassessed"}))
    },
    oracle:{
      schema_version:1,status:"completed",source_review:"pending",
      totals:structuredClone(expected.oracle),
      results:external.map(x=>({id:x.id,source_sha256:x.source_sha256,
        independent_text_review:"pending"}))
    }
  };
}
test("frozen original/external results pass without pretending source review",()=>{
 assert.equal(auditBaseline(fakeReports(),expected).status,"frozen_baseline_matched");
});
test("unexpected coverage loss fails CI instead of reporting success",()=>{
 const reports=fakeReports();reports.external.counts.covered=6;
 assert.throws(()=>auditBaseline(reports,expected),/frozen parsing baseline/);
});
test("source-oracle reference regressions fail CI",()=>{
 const reports=fakeReports();reports.oracle.totals.reference_matches=10;
 assert.throws(()=>auditBaseline(reports,expected),/typed source-reference results/);
});
test("external semantic equivalence regressions fail CI",()=>{
 const reports=fakeReports();reports.externalSummary.by_cohort.overlap_discovery.equivalent=3;
 assert.throws(()=>auditBaseline(reports,expected),/overlap discovery baseline/);
});
test("fabricated proof and independently reviewed source status fail CI",()=>{
 const reports=fakeReports();reports.research.results[0].kernel_verified=true;
 assert.throws(()=>auditBaseline(reports,expected),/wrongly granted kernel/);
 reports.research.results[0].kernel_verified=false;
 reports.oracle.results[0].independent_text_review="verified";
 assert.throws(()=>auditBaseline(reports,expected),/unreviewed oracle/);
});
test("cross-report source identity mismatch fails CI",()=>{
 const reports=fakeReports();
 reports.oracle.results[3].source_sha256="b".repeat(64);
 assert.throws(()=>auditBaseline(reports,expected),/unbound to original source/);
});
test("the original benchmark cannot silently drop case entries",()=>{
 const reports=fakeReports();
 reports.research.results.pop();
 assert.throws(()=>auditBaseline(reports,expected),/total\/result mismatch/);
});
