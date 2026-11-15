#!/usr/bin/env node
// Source provenance and immutable corpus checks; never inspects parser outputs.
import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";
import {fileURLToPath} from "node:url";
import {validateSource} from "../unified/contract.mjs";

const own = path.dirname(fileURLToPath(import.meta.url));
const fail = msg => {throw Error(msg);};
const ids = /^[A-Z][0-9]{2}$/;
export function validateCorpus(dir=own) {
  const manifest=JSON.parse(fs.readFileSync(path.join(dir,"manifest.json"),"utf8"));
  const lock=JSON.parse(fs.readFileSync(path.join(dir,"lock.json"),"utf8"));
  if (manifest.schema_version!==1||lock.schema_version!==1||
      !/^[0-9a-f]{40}$/.test(lock.source_snapshot_commit||""))
    fail("unrecognized external corpus or lock");
  if (!Array.isArray(manifest.cases)||manifest.cases.length===0)
    fail("empty external corpus");
  const cases=manifest.cases;
  const seen=new Set();
  const groups=new Set();
  for (const item of cases) {
    const {id,source_group,cohort,source_url,source_location,transcribed_equation,transcription}=item;
    if (!ids.test(id)||seen.has(id)) fail("unsafe or duplicate case id "+id);
    seen.add(id);groups.add(source_group);
    if (!["openstax","dlmf","nicholson"].includes(source_group) ||
        (source_group==="openstax" ? cohort!=="overlap_discovery" : cohort!=="author_holdout"))
      fail("invalid author holdout split "+id);
    if (!source_url?.startsWith("https://") ||
        !["openstax.org","dlmf.nist.gov","math.libretexts.org"].includes(new URL(source_url).hostname) ||
        !source_location || !transcription || typeof transcribed_equation!=="string")
      fail("untraceable external source "+id);
    const bytes=fs.readFileSync(path.join(dir,"cases",id+".tex"));
    validateSource(bytes);
    const s=bytes.toString("utf8");
    if (!s.includes("$"+transcribed_equation+"$") ||
        (s.match(/\\begin\{theorem\}/g)||[]).length!==1 ||
        (s.match(/\\end\{theorem\}/g)||[]).length!==1)
      fail("equation or theorem wrapper changed "+id);
    const expected=lock.git_blob_sha1?.[id];
    const gitObject=Buffer.concat([Buffer.from("blob "+bytes.length+"\0"),bytes]);
    const actual=crypto.createHash("sha1").update(gitObject).digest("hex");
    if (expected!==actual) fail("locked source changed "+id);
  }
  const onDisk=fs.readdirSync(path.join(dir,"cases")).filter(n=>n.endsWith(".tex"))
    .map(n=>n.slice(0,-4)).sort();
  if (onDisk.join()!==[...seen].sort().join() ||
      Object.keys(lock.git_blob_sha1||{}).sort().join()!==onDisk.join())
    fail("manifest/locked corpus mismatch");
  for (const required of ["openstax","dlmf","nicholson"])
    if (!groups.has(required)) fail("missing source family "+required);
  return {count:cases.length,
    source_groups:Object.fromEntries([...groups].sort().map(g=>[g,cases.filter(x=>x.source_group===g).length])),
    cohorts:{overlap_discovery:cases.filter(x=>x.cohort==="overlap_discovery").length,
      author_holdout:cases.filter(x=>x.cohort==="author_holdout").length}};
}
if (process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url))
  console.log(JSON.stringify(validateCorpus(process.argv[2]?path.resolve(process.argv[2]):own)));
