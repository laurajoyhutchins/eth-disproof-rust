// Unified evidence schema for two independent mathematical parsers.
// Parsing is never proof or semantic-equivalence credit.
import crypto from "node:crypto";

export const LEANIFY_COMMIT="134da59ae02e9fffc011a5ea89acf4320268d220";
export const MAX_SOURCE_BYTES=1_000_000;
export const MAX_LOG_BYTES=2_000_000;
export const sha256=bytes=>crypto.createHash("sha256").update(bytes).digest("hex");
const forbidden=/\\(?:input|include|subfile|newcommand|renewcommand|catcode|write18|openout|read|def)\b/;

export function validateSource(bytes) {
  if(!Buffer.isBuffer(bytes))throw Error("source must be raw bytes");
  if(!bytes.length||bytes.length>MAX_SOURCE_BYTES)throw Error("source outside size limits");
  const source=new TextDecoder("utf-8",{fatal:true}).decode(bytes);
  if(forbidden.test(source))throw Error("dynamic TeX input/macro rewriting requires pinned expansion provenance");
  return {sha256:sha256(bytes),bytes:bytes.length};
}
export function classifyLeanify({stdout="",stderr="",exitCode=null,timedOut=false}) {
  const result={backend:"leanify",status:"tool_error",claim_count:0,diagnostics:[],counts:null};
  if(timedOut){result.status="timeout";return result;}
  const rows=[...stdout.matchAll(/\bresults:\s*(\d+) compiled,\s*(\d+) failed,\s*(\d+) prose \(of (\d+)\)/g)];
  const numbers=[...stdout.matchAll(/\b(\d+) definitions,\s*(\d+) claims\b/g)];
  if(rows.length!==1||numbers.length!==1){result.diagnostics=["missing native summary"];return result;}
  const [compiled,failed,prose,total]=rows[0].slice(1).map(Number);
  const [definitions,claimsDeclared]=numbers[0].slice(1).map(Number);
  const claims=[...stdout.matchAll(/\binfo: claim\s+\d+:\s*(.+)$/gm)].map(m=>m[1]);
  const warnings=stdout.split("\n").filter(s=>/\b(?:warning|error):/.test(s));
  result.diagnostics=warnings;
  if(!total||compiled+failed+prose!==total||claimsDeclared!==claims.length||
     (compiled===0&&claimsDeclared>0)){
    result.diagnostics=[...warnings,"inconsistent statement or claim counts"];
    return result;
  }
  result.counts={compiled,failed,prose,total,definitions,claimsDeclared};
  result.claim_count=claimsDeclared;result.claims=claims;
  const gap=warnings.some(s=>/not checked|partly checked|does not read/i.test(s));
  if(failed>0)result.status="diagnosed_failure";
  else if(exitCode!==0)result.status="tool_error";
  else if(compiled===total&&claimsDeclared>0&&!gap)result.status="parsed";
  else result.status="unsupported_or_partial";
  return result;
}
export function classifyStructural({exitCode=null,timedOut=false,outputText=null,stderr=""},namespace){
  const result={backend:"structural",status:"unsupported",claim_count:0,diagnostics:[]};
  if(timedOut){result.status="timeout";return result;}
  if(exitCode!==0){
    result.diagnostics=[(stderr.trim().split("\n")[0]||"no diagnostic").slice(0,1024)];
    result.status=stderr.trim()?"diagnosed_failure":"tool_error";
    return result;
  }
  if(typeof outputText!=="string"||!outputText.startsWith("import Mathlib.Basic.Real.Basic\n")||
     !outputText.includes("namespace "+namespace+"\n")||
     !outputText.includes("def claim : Prop :=")||
     !outputText.includes("end "+namespace+"\n")){
    result.status="tool_error";result.diagnostics=["missing or invalid generated Lean"];return result;
  }
  result.status="parsed";result.claim_count=1;
  return result;
}
export function select(results){
  if(!Array.isArray(results)||results.length!==2||
    new Set(results.map(x=>x.backend)).size!==2)throw Error("expected exactly two backend results");
  const parsed=results.filter(x=>x.status==="parsed");
  if(results.some(x=>["tool_error","timeout"].includes(x.status)))
    return {status:"incomplete",backend:null,reason:"a required backend failed"};
  if(parsed.length===2)
    return {status:"conflict_requires_equivalence",backend:null,reason:"two accepted translations need independent equivalence"};
  if(parsed.length===1)
    return {status:"translation_requires_kernel_review",backend:parsed[0].backend,
      reason:"translation only; no mathematical correctness credit"};
  return {status:"unsupported",backend:null,reason:"neither backend compiled unchanged input"};
}
export function receipt({source,observations,tools,generated,logs}){
  return {schema_version:1,source,observations,selection:select(observations),
    tools,generated,logs,verification:{kernel_checked:false,semantic_equivalence:false,
    proof_completed:false,note:"parser status does not imply mathematical verification"}};
}
