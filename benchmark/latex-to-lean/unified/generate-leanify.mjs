// Leanify's generated modules, kept separate from a checker-only observation.
// The checkout is pinned externally; this function creates a temporary module
// directory and deletes it, so a user's tracked source tree is never rewritten.
import fs from "node:fs";
import path from "node:path";
import {sha256} from "./contract.mjs";

export function generateLeanify({vendor,source,sourceSha,run}){
  if(typeof sourceSha!=="string"||!/^[0-9a-f]{64}$/.test(sourceSha))
    throw Error("invalid source identity");
  const ns="Unified"+sourceSha.slice(0,20);
  const dir=path.join(vendor,ns);
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
    fs.rmSync(dir,{recursive:true,force:true});
  }
}
