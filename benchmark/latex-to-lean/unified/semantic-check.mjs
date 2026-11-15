#!/usr/bin/env node
import {runSemanticCase} from "./semantic.mjs";

const argv = process.argv.slice(2);
const args = {};
for (let i=0; i<argv.length; i+=2) {
  const key = argv[i]?.replace(/^--/, "");
  if (!key || !["source","receipt-dir","leanify-dir"].includes(key) || args[key] || !argv[i+1])
    throw Error("usage: node semantic-check.mjs --source FILE.tex --receipt-dir DIR --leanify-dir PINNED_CHECKOUT");
  args[key] = argv[i+1];
}
if (Object.keys(args).length !== 3) throw Error("expected source, receipt-dir and leanify-dir");
try {
  const result = runSemanticCase({sourceFile:args.source, caseDir:args["receipt-dir"],
    leanifyDir:args["leanify-dir"]});
  console.log(JSON.stringify({source_sha256:result.source_sha256,status:result.status,
    checks:result.checks}));
  if (result.status === "tool_error") process.exitCode = 2;
} catch (error) {
  console.error(String(error));
  process.exitCode = 1;
}
