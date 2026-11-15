#!/usr/bin/env node
import {verifySemanticCase} from "./semantic.mjs";
const argv = process.argv.slice(2);
const args = {};
for (let i=0; i<argv.length; i+=2) {
  const key=argv[i]?.replace(/^--/,"");
  if (!key || !["source","receipt-dir"].includes(key) || args[key] || !argv[i+1])
    throw Error("usage: node semantic-verify.mjs --source FILE.tex --receipt-dir DIR");
  args[key]=argv[i+1];
}
if (Object.keys(args).length !== 2) throw Error("expected source and receipt-dir");
try {
  const result=verifySemanticCase(args.source,args["receipt-dir"]);
  console.log(JSON.stringify({source_sha256:result.source_sha256,status:result.status,
    kernel_checked:result.checks.kernel_checked}));
} catch (error) {
  console.error(String(error));
  process.exitCode=1;
}
