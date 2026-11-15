import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import {sha256} from "./contract.mjs";
import {generateLeanify} from "./generate-leanify.mjs";

function fixture(){
 const root=fs.mkdtempSync(path.join(os.tmpdir(),"native-lean-"));
 const source=Buffer.from("\\begin{theorem}$1=1$\\end{theorem}");
 const sourceSha=sha256(source),ns="Unified"+sourceSha.slice(0,20);
 return {root,source,sourceSha,ns};
}
function clean(f,t){t.after(()=>fs.rmSync(f.root,{recursive:true,force:true}));}
test("actual native module bytes are returned; temporary directory is cleaned",t=>{
 const f=fixture();clean(f,t);
 const log=[];
 const result=generateLeanify({vendor:f.root,source:f.source,sourceSha:f.sourceSha,run:(cmd,args,opts)=>{
   assert.equal(cmd,"lake");assert.equal(opts.cwd,f.root);log.push(args.join(" "));
   if(args.includes("init")){
     const dir=path.join(f.root,f.ns);
     assert.equal(sha256(fs.readFileSync(path.join(dir,"article.tex"))),f.sourceSha);
     fs.writeFileSync(path.join(dir,"Article.lean"),"article");
     fs.writeFileSync(path.join(dir,"Compiled.lean"),"compiled");
   }
   return {exitCode:0,stdout:"ok",stderr:""};
 }});
 assert.equal(result.ok,true);assert.equal(result.namespace,f.ns);
 assert.equal(result.modules["Article.lean"].toString(),"article");
 assert.equal(result.modules["Compiled.lean"].toString(),"compiled");
 assert.equal(log.length,2);assert.equal(fs.existsSync(path.join(f.root,f.ns)),false);
});
test("native compilation failures never become successful receipts",t=>{
 const f=fixture();clean(f,t);
 const result=generateLeanify({vendor:f.root,source:f.source,sourceSha:f.sourceSha,
   run:()=>({exitCode:1,stdout:"",stderr:"failed"})});
 assert.equal(result.ok,false);assert.equal(result.stage,"init");
 assert.equal(fs.existsSync(path.join(f.root,f.ns)),false);
});
test("existing namespace cannot be overwritten or deleted",t=>{
 const f=fixture();clean(f,t);
 fs.mkdirSync(path.join(f.root,f.ns));
 fs.writeFileSync(path.join(f.root,f.ns,"Article.lean"),"preexisting");
 assert.throws(()=>generateLeanify({vendor:f.root,source:f.source,sourceSha:f.sourceSha,run:()=>{throw Error("must not run");}}));
 assert.equal(fs.readFileSync(path.join(f.root,f.ns,"Article.lean"),"utf8"),"preexisting");
});
test("malformed source identity cannot generate native declarations",t=>{
 const f=fixture();clean(f,t);
 assert.throws(()=>generateLeanify({vendor:f.root,source:f.source,sourceSha:"bad",run:()=>{throw Error("never");}}));
});
