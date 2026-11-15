#!/usr/bin/env node
// Independent source-oracle shape comparison. The oracle is compiled before
// candidate artifacts are introduced into the Lake environment.
// Passing rfl means only a definitional match to the reference proposition.
// Human/source review is not replaced by this test.
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import crypto from "node:crypto";
import {spawnSync} from "node:child_process";
import {fileURLToPath} from "node:url";
import {validateCorpus} from "../validate.mjs";
import {sha256,validateSource,select,LEANIFY_COMMIT} from "../../unified/contract.mjs";
const sourceDir=path.dirname(fileURLToPath(import.meta.url));
const fail=message=>{throw Error(message);};
const ok=(value,message)=>{if(!value)fail(message);};
const hash=/^[a-f0-9]{64}$/;

export function probeSource(id,namespace,backend) {
  ok(/^[A-Z][0-9]{2}$/.test(id),"unsafe source identifier");
  ok(/^[A-Za-z][A-Za-z0-9]*$/.test(namespace),"unsafe module identifier");
  ok(["leanify","structural"].includes(backend),"unknown backend");
  const claim=backend==="leanify" ? "claim0" : "claim";
  return "import ExternalGold\nimport "+namespace+(backend==="leanify"?".Article":"")+
    "\n\nnamespace ExternalOracleProbe\n"+
    "theorem shape_match : ExternalGold."+id+" ↔ "+namespace+"."+claim+" := by rfl\n"+
    "#print axioms shape_match\nend ExternalOracleProbe\n";
}
function run(cmd,args,cwd) {
  const r=spawnSync(cmd,args,{cwd,encoding:"utf8",shell:false,
    timeout:180_000,maxBuffer:2_000_000});
  return {exit_code:r.status,stdout:r.stdout??"",stderr:r.stderr??"",
    launch_error:r.error?String(r.error):null};
}
function stage(dir,name,r) {
  const logs={};
  for(const stream of ["stdout","stderr"]) {
    const file=name+"."+stream, bytes=Buffer.from(r[stream]);
    fs.writeFileSync(path.join(dir,file),bytes,{flag:"wx"});
    logs[file]=sha256(bytes);
  }
  return {exit_code:r.exit_code,launch_error:r.launch_error,logs};
}
function relativeBytes(root,name,expected) {
  ok(hash.test(expected||""),"missing artifact SHA256");
  const bytes=fs.readFileSync(path.join(root,name));
  ok(sha256(bytes)===expected,"tampered native artifact "+name);
  return bytes;
}
function targetEntries(targets) {
  return targets.map(([name,glob])=>'\n[[lean_lib]]\nname = "'+name+
    '"\nsrcDir = "."\nglobs = ["'+glob+'"]\n').join("");
}
function trustedExit(r) {return r.exit_code===0&&!r.launch_error;}
export function runOracle({externalDir,receiptsDir,leanifyDir,outDir}) {
  validateCorpus(externalDir);
  const manifest=JSON.parse(fs.readFileSync(path.join(externalDir,"manifest.json"),"utf8"));
  const cwd=path.resolve(leanifyDir);
  const version=run("git",["rev-parse","HEAD"],cwd);
  ok(trustedExit(version)&&version.stdout.trim()===LEANIFY_COMMIT,"unpinned Leanify checkout");
  const oracle=fs.readFileSync(path.join(externalDir,"oracle","ExternalGold.lean"));
  const oracleHash=sha256(oracle);
  const names=manifest.cases.map(item=>{
    const sourceFile=path.join(externalDir,"cases",item.id+".tex");
    const identity=validateSource(fs.readFileSync(sourceFile));
    const receiptFile=path.join(receiptsDir,item.id,"receipt.json");
    const receiptBytes=fs.readFileSync(receiptFile);
    const receipt=JSON.parse(receiptBytes.toString("utf8"));
    ok(receipt.source?.sha256===identity.sha256 &&
      receipt.source?.bytes===identity.bytes, "source identity mismatch "+item.id);
    ok(JSON.stringify(select(receipt.observations))===JSON.stringify(receipt.selection),
      "backend choice mismatch "+item.id);
    return {item,sourceFile,identity,receipt,receipt_hash:sha256(receiptBytes),
      leftNS:"Unified"+identity.sha256.slice(0,20),
      rightNS:"Struct"+identity.sha256.slice(0,16)};
  });
  fs.mkdirSync(outDir,{recursive:true});
  const config=path.join(cwd,"lakefile.toml");
  const original=fs.readFileSync(config,"utf8");
  const allTargets=[["ExternalGold","ExternalGold"]];
  for(const t of names) {
    allTargets.push([t.leftNS,t.leftNS+".+"]);
    allTargets.push([t.rightNS,t.rightNS]);
  }
  for(const [name] of allTargets)
    ok(!original.includes('name = "'+name+'"'),"preexisting temporary Lake target "+name);
  const modified=original+targetEntries(allTargets);
  const goldPath=path.join(cwd,"ExternalGold.lean");
  let ownsGold=false, ownsConfig=false;
  const results=[];
  try {
    fs.writeFileSync(goldPath,oracle,{flag:"wx"});
    ownsGold=true;
    fs.writeFileSync(config,modified);
    ownsConfig=true;
    const setup=run("lake",["build","ExternalGold"],cwd);
    const setupFile=path.join(outDir,"gold-build");
    fs.mkdirSync(setupFile);
    const setupEvidence=stage(setupFile,"build",setup);
    if(!trustedExit(setup)) {
      const report={status:"oracle_build_failed",oracle_sha256:oracleHash,setup:setupEvidence};
      fs.writeFileSync(path.join(outDir,"summary.json"),JSON.stringify(report,null,2)+"\n",{flag:"wx"});
      return report;
    }
    for(const record of names) {
      const {item,identity,receipt,receipt_hash,leftNS,rightNS,sourceFile}=record;
      const sourceBytes=fs.readFileSync(sourceFile);
      const accepted=receipt.observations.filter(x=>x.status==="parsed").map(x=>x.backend).sort();
      const location=path.join(outDir,item.id);
      fs.mkdirSync(location);
      const one={id:item.id,source_sha256:identity.sha256,
        translation_receipt_sha256:receipt_hash,oracle_sha256:oracleHash,
        source_group:item.source_group,cohort:item.cohort,
        independent_text_review:"pending",oracle_matches:{}};
      const goldDefined=item.id!=="D02";
      for(const backend of ["leanify","structural"]) {
        if(!accepted.includes(backend)) {
          one.oracle_matches[backend]={status:"not_accepted"};
          continue;
        }
        if(!goldDefined) {
          one.oracle_matches[backend]={status:"oracle_not_formalized"};
          continue;
        }
        const ns=backend==="leanify"?leftNS:rightNS;
        let owned=null,work=null;
        try {
          if(backend==="leanify") {
            ok(receipt.generated.leanify?.namespace===ns,"namespace mismatch "+item.id);
            const newOwned=path.join(cwd,ns);
            fs.mkdirSync(newOwned); // take ownership only after success
            owned=newOwned;
            for(const name of ["Article.lean","Compiled.lean"]) {
              const entry=receipt.generated.leanify.modules?.[name];
              ok(entry?.name===ns+"/"+name,"native path mismatch "+item.id);
              fs.writeFileSync(path.join(owned,name),
                relativeBytes(path.join(receiptsDir,item.id),entry.name,entry.sha256),{flag:"wx"});
            }
            fs.writeFileSync(path.join(owned,"article.tex"),sourceBytes,{flag:"wx"});
          } else {
            const e=receipt.generated.structural;
            ok(e?.name===ns+".lean","structural path mismatch "+item.id);
            const newOwned=path.join(cwd,ns+".lean");
            fs.writeFileSync(newOwned,relativeBytes(path.join(receiptsDir,item.id),e.name,e.sha256),{flag:"wx"});
            owned=newOwned;
          }
          work=fs.mkdtempSync(path.join(cwd,".external-oracle-"));
          const build=run("lake",["build",ns+(backend==="leanify"?".Article":"")],cwd);
          const built=stage(location,backend+".build",build);
          if(!trustedExit(build)) {
            one.oracle_matches[backend]={status:"tool_error",build:built};
            continue;
          }
          const src=probeSource(item.id,ns,backend);
          const probe=path.join(work,"Probe.lean");
          fs.writeFileSync(probe,src,{flag:"wx"});
          fs.writeFileSync(path.join(location,backend+".Proof.lean"),src,{flag:"wx"});
          const result=run("lake",["env","lean",probe],cwd);
          const checked=stage(location,backend+".proof",result);
          const admitted=/(?:sorryAx|admit)/.test(result.stdout+result.stderr);
          const status=!result.launch_error&&result.exit_code===0&&!admitted?
            "reference_definitional_match":
            result.launch_error?"tool_error":"not_definitionally_equal";
          one.oracle_matches[backend]={status,build:built,proof:checked,
            probe_sha256:sha256(Buffer.from(src))};
        } finally {
          if(owned) fs.rmSync(owned,{recursive:true,force:true});
          if(work) fs.rmSync(work,{recursive:true,force:true});
        }
      }
      fs.writeFileSync(path.join(location,"oracle.json"),JSON.stringify(one,null,2)+"\n",{flag:"wx"});
      results.push(one);
    }
    const stat=rows=>({
      total:rows.length,
      generated_translations:rows.reduce((n,r)=>n+Object.values(r.oracle_matches)
        .filter(x=>x.status!=="not_accepted").length,0),
      reference_matches:rows.reduce((n,r)=>n+Object.values(r.oracle_matches)
        .filter(x=>x.status==="reference_definitional_match").length,0),
      no_definitional_match:rows.reduce((n,r)=>n+Object.values(r.oracle_matches)
        .filter(x=>x.status==="not_definitionally_equal").length,0),
      tool_errors:rows.reduce((n,r)=>n+Object.values(r.oracle_matches)
        .filter(x=>x.status==="tool_error").length,0),
      audited_source_faithfulness:0
    });
    const report={schema_version:1,status:"completed",oracle_sha256:oracleHash,
      source_review:"pending",setup:setupEvidence,totals:stat(results),
      by_cohort:{
        overlap_discovery:stat(results.filter(r=>r.cohort==="overlap_discovery")),
        author_holdout:stat(results.filter(r=>r.cohort==="author_holdout"))
      },results};
    fs.writeFileSync(path.join(outDir,"summary.json"),JSON.stringify(report,null,2)+"\n",{flag:"wx"});
    return report;
  } finally {
    const matches=fs.readFileSync(config,"utf8")===modified;
    if(ownsConfig && matches) fs.writeFileSync(config,original);
    if(ownsGold) fs.rmSync(goldPath,{force:true});
    if(ownsConfig&&!matches) fail("concurrent Lake configuration mutation; original not overwritten");
  }
}
if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  const [externalDir,receiptsDir,leanifyDir,outDir,...extra]=process.argv.slice(2);
  if(!externalDir||!receiptsDir||!leanifyDir||!outDir||extra.length)
    throw Error("usage: node oracle/check.mjs EXTERNAL_DIR RECEIPTS_DIR LEANIFY_DIR OUT_DIR");
  const r=runOracle({externalDir:path.resolve(externalDir),
    receiptsDir:path.resolve(receiptsDir),leanifyDir:path.resolve(leanifyDir),
    outDir:path.resolve(outDir)});
  console.log(JSON.stringify({status:r.status,totals:r.totals,by_cohort:r.by_cohort}));
  if(r.status!=="completed"||r.totals.tool_errors)process.exitCode=2;
}
