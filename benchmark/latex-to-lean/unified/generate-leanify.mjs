// Leanify's generated modules, kept separate from a checker-only observation.
// The checkout is pinned externally; this function creates a temporary module
// directory and restores the temporary Lake target after generation.
import fs from "node:fs";
import path from "node:path";
import {sha256} from "./contract.mjs";

export function generateLeanify({vendor,source,sourceSha,run}){
  if(typeof sourceSha!=="string"||!/^[0-9a-f]{64}$/.test(sourceSha))
    throw Error("invalid source identity");
  const ns="Unified"+sourceSha.slice(0,20);
  const dir=path.join(vendor,ns);
  // Leanify init appends a library target to lakefile.toml. That mutation must
  // not escape this invocation; otherwise later comparisons observe stale
  // targets even after the temporary source folder has been removed.
  const lakefile=path.join(vendor,"lakefile.toml");
  const before=fs.readFileSync(lakefile,"utf8");
  const added="\n[[lean_lib]]\nname = \""+ns+"\"\nsrcDir = \".\"\nglobs = [\""+ns+".+\"]\n";
  const expected=before+(before.endsWith("\n")?"":"\n")+added;
  // Refuse any existing worktree name rather than overwrite or merge with it.
  fs.mkdirSync(dir);
  try{
    const article=path.join(dir,"article.tex");
    fs.writeFileSync(article,source,{flag:"wx"});
    if(sha256(fs.readFileSync(article))!==sourceSha)throw Error("source changed before native compilation");
    const init=run("lake",["exe","leanify","init",ns+"/article.tex","--name",ns],{cwd:vendor});
    if(init.exitCode!==0||init.launchError||init.timedOut)
      return {ok:false,stage:"init",init,build:null,namespace:ns};
    const build=run("lake",["build",ns+".Article"],{cwd:vendor});
    if(build.exitCode!==0||build.launchError||build.timedOut)
      return {ok:false,stage:"build",init,build,namespace:ns};
    if(sha256(fs.readFileSync(article))!==sourceSha)
      throw Error("Leanify modified its source during compilation");
    const modules={};
    for(const name of ["Article.lean","Compiled.lean"]){
      const file=path.join(dir,name);
      if(!fs.existsSync(file))throw Error("native module missing: "+name);
      modules[name]=fs.readFileSync(file);
    }
    return {ok:true,namespace:ns,init,build,modules};
  }finally{
    // Source cleanup is ours. An unrelated Lake edit is not ours and must
    // never be clobbered, even if the upstream init command failed.
    fs.rmSync(dir,{recursive:true,force:true});
    const after=fs.readFileSync(lakefile,"utf8");
    if(after===expected)fs.writeFileSync(lakefile,before);
    else if(after!==before)
      throw Error("Leanify modified Lake configuration beyond its own temporary target");
  }
}
