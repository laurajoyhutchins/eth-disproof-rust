#!/usr/bin/env node
// One entry point; two independently pinned frontends; one fail-closed contract.
// No claim here that their internal type systems are equivalent.
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import {spawnSync} from "node:child_process";
import {generateLeanify} from "./generate-leanify.mjs";
import {sha256,validateSource,classifyLeanify,classifyStructural,receipt,
  LEANIFY_COMMIT,MAX_LOG_BYTES} from "./contract.mjs";

function parseArgs(argv){
  if(argv.length!==8)throw Error("usage: node run.mjs --source FILE.tex --out DIR --structural-bin BINARY --leanify-dir CHECKOUT");
  const a={};
  for(let i=0;i<argv.length;i+=2){
    if(!argv[i].startsWith("--")||a[argv[i].slice(2)]!==undefined)throw Error("duplicate or invalid argument");
    a[argv[i].slice(2)]=argv[i+1];
  }
  if(["source","out","structural-bin","leanify-dir"].some(k=>!a[k])||
      Object.keys(a).length!==4)throw Error("expected source/out/structural-bin/leanify-dir");
  return a;
}
function run(command,args,options={}){
  const x=spawnSync(command,args,{encoding:"utf8",shell:false,timeout:90_000,
    maxBuffer:MAX_LOG_BYTES,...options});
  return {stdout:x.stdout??"",stderr:x.stderr??"",exitCode:x.status,
    timedOut:x.error?.code==="ETIMEDOUT",
    launchError:x.error&&!["ETIMEDOUT"].includes(x.error.code)?String(x.error):null};
}
function exclusive(file,bytes){fs.writeFileSync(file,bytes,{flag:"wx"});}
function main(){
  const args=parseArgs(process.argv.slice(2));
  const input=path.resolve(args.source);
  const source=fs.readFileSync(input);
  const identity=validateSource(source);
  const output=path.resolve(args.out);
  if(fs.existsSync(path.join(output,"receipt.json")))throw Error("output already contains a receipt; refuse overwrite");
  fs.mkdirSync(output,{recursive:true});
  const temp=fs.mkdtempSync(path.join(os.tmpdir(),"latex-unified-"));
  try{
    const identicalSource=path.join(temp,"article.tex");
    fs.writeFileSync(identicalSource,source);
    const namespace="Struct"+identity.sha256.slice(0,16);
    const generatedFile=path.join(temp,namespace+".lean");
    const binary=path.resolve(args["structural-bin"]);
    const binarySha=sha256(fs.readFileSync(binary));
    const vendor=path.resolve(args["leanify-dir"]);
    const pinned=run("git",["rev-parse","HEAD"],{cwd:vendor});
    if(pinned.launchError||pinned.exitCode!==0||pinned.stdout.trim()!==LEANIFY_COMMIT)
      throw Error("Leanify revision differs from mandatory "+LEANIFY_COMMIT);
    const structuralRun=run(binary,[identicalSource,generatedFile,namespace]);
    const generated=structuralRun.exitCode===0 && fs.existsSync(generatedFile)?
      fs.readFileSync(generatedFile,"utf8"):null;
    const structural=classifyStructural({...structuralRun,outputText:generated},namespace);
    if(structuralRun.launchError){
      structural.status="tool_error";structural.diagnostics.push(structuralRun.launchError);
    }
    if(sha256(fs.readFileSync(identicalSource))!==identity.sha256)
      throw Error("source modified by structural backend");
    const leanRun=run("lake",["exe","leanify","check",identicalSource,"--claims","--defined"],{cwd:vendor});
    const leanify=classifyLeanify(leanRun);
    if(leanRun.launchError){
      leanify.status="tool_error";leanify.diagnostics.push(leanRun.launchError);
    }
    if(sha256(fs.readFileSync(identicalSource))!==identity.sha256)
      throw Error("source modified by Leanify backend");
    let native=null;
    if(leanify.status==="parsed"){
      try{native=generateLeanify({vendor,source,sourceSha:identity.sha256,run});}
      catch(error){
        leanify.status="tool_error";
        leanify.diagnostics.push("native Leanify elaboration: "+String(error));
      }
      if(native&&!native.ok){
        leanify.status="tool_error";
        leanify.diagnostics.push("Leanify native "+native.stage+" failed");
      }
    }
    const files={};
    if(structural.status==="parsed"){
      const file=namespace+".lean";
      exclusive(path.join(output,file),generated);
      files.structural={name:file,sha256:sha256(Buffer.from(generated))};
    }
    if(native?.ok){
      const dir=path.join(output,native.namespace);
      fs.mkdirSync(dir);
      const modules={};
      for(const name of ["Article.lean","Compiled.lean"]){
        const bytes=native.modules[name];
        exclusive(path.join(dir,name),bytes);
        modules[name]={name:native.namespace+"/"+name,sha256:sha256(bytes)};
      }
      files.leanify={namespace:native.namespace,modules};
    }
    if(native){
      exclusive(path.join(output,"leanify.init.stdout"),native.init.stdout);
      exclusive(path.join(output,"leanify.init.stderr"),native.init.stderr);
      if(native.build){
        exclusive(path.join(output,"leanify.build.stdout"),native.build.stdout);
        exclusive(path.join(output,"leanify.build.stderr"),native.build.stderr);
      }
    }
    exclusive(path.join(output,"leanify.stdout"),leanRun.stdout);
    exclusive(path.join(output,"leanify.stderr"),leanRun.stderr);
    exclusive(path.join(output,"structural.stdout"),structuralRun.stdout);
    exclusive(path.join(output,"structural.stderr"),structuralRun.stderr);
    const logs={
      leanify_stdout_sha256:sha256(Buffer.from(leanRun.stdout)),
      leanify_stderr_sha256:sha256(Buffer.from(leanRun.stderr)),
      structural_stdout_sha256:sha256(Buffer.from(structuralRun.stdout)),
      structural_stderr_sha256:sha256(Buffer.from(structuralRun.stderr))
    };
    if(native){
      logs.leanify_init_stdout_sha256=sha256(Buffer.from(native.init.stdout));
      logs.leanify_init_stderr_sha256=sha256(Buffer.from(native.init.stderr));
      if(native.build){
        logs.leanify_build_stdout_sha256=sha256(Buffer.from(native.build.stdout));
        logs.leanify_build_stderr_sha256=sha256(Buffer.from(native.build.stderr));
      }
    }
    const result=receipt({
      source:identity,observations:[leanify,structural],
      tools:{leanify:{commit:LEANIFY_COMMIT,command:"lake exe leanify check --claims --defined / init / build"},
        structural:{binary_sha256:binarySha}},
      generated:files,logs
    });
    exclusive(path.join(output,"receipt.json"),JSON.stringify(result,null,2)+"\n");
    console.log(JSON.stringify({source_sha256:identity.sha256,
      selection:result.selection,observations:result.observations.map(x=>({backend:x.backend,status:x.status,claims:x.claim_count}))}));
    if(result.selection.status==="incomplete")process.exitCode=2;
    if(result.selection.status==="conflict_requires_equivalence")process.exitCode=3;
  }finally{fs.rmSync(temp,{recursive:true,force:true});}
}
try{main();}catch(e){console.error(String(e));process.exitCode=1;}
