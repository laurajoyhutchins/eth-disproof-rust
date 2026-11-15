// Compare generated propositions in the pinned Lean environment.
// A checked equivalence between translations is not evidence of LaTeX faithfulness.
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import {spawnSync} from "node:child_process";
import {sha256, validateSource, select, LEANIFY_COMMIT, MAX_LOG_BYTES} from "./contract.mjs";

const SHA = /^[0-9a-f]{64}$/;
function assert(ok, message) { if (!ok) throw Error(message); }
function readMatched(dir, entry, label) {
  assert(entry && SHA.test(entry.sha256 || ""), "missing " + label + " hash");
  const bytes = fs.readFileSync(path.join(dir, entry.name));
  assert(sha256(bytes) === entry.sha256, label + " hash mismatch");
  return bytes;
}
export function prepareSemanticCase(sourceBytes, caseDir) {
  const source = validateSource(sourceBytes);
  const record = JSON.parse(fs.readFileSync(path.join(caseDir, "receipt.json"), "utf8"));
  assert(record.schema_version === 1, "unrecognized translation receipt");
  assert(record.source?.sha256 === source.sha256 && record.source?.bytes === source.bytes,
    "LaTeX source identity mismatch");
  assert(record.tools?.leanify?.commit === LEANIFY_COMMIT, "wrong Leanify revision");
  assert(Array.isArray(record.observations) && record.observations.length === 2,
    "missing translation observations");
  assert(JSON.stringify(record.selection) === JSON.stringify(select(record.observations)),
    "untrusted backend selection");
  const both = record.observations.every(x => x.status === "parsed");
  const base = {source_sha256: source.sha256, source_bytes: source.bytes,
    translation_receipt_sha256: sha256(fs.readFileSync(path.join(caseDir, "receipt.json"))),
    semantic_faithfulness: "not_assessed", proof_completion: "not_assessed"};
  if (!both) return {...base, status: "not_applicable",
    reason: "comparison requires two accepted translations"};
  const counts = record.observations.map(x => x.claim_count);
  if (counts.some(n => n !== 1)) return {...base, status: "unresolved_pairing",
    reason: "no independently justified correspondence for multiple claims"};
  const leanify = record.generated?.leanify;
  const structural = record.generated?.structural;
  const leftNS = "Unified" + source.sha256.slice(0, 20);
  const rightNS = "Struct" + source.sha256.slice(0, 16);
  assert(leanify?.namespace === leftNS, "Leanify namespace mismatch");
  assert(structural?.name === rightNS + ".lean", "structural namespace mismatch");
  const names = ["Article.lean", "Compiled.lean"];
  const modules = {};
  for (const name of names) {
    const entry = leanify.modules?.[name];
    assert(entry?.name === leftNS + "/" + name, "unexpected native module path");
    modules[name] = readMatched(caseDir, entry, name);
  }
  const structuralBytes = readMatched(caseDir, structural, "structural Lean");
  return {...base, status: "ready", leftNS, rightNS, modules,
    structuralBytes, artifact_hashes: {
      article: leanify.modules["Article.lean"].sha256,
      compiled: leanify.modules["Compiled.lean"].sha256,
      structural: structural.sha256
    }};
}

// No AST translation or pretty-printed Leanify claim is used. The imported
// native declaration and the structural declaration are elaborated by Lean.
export function makeProbes(prepared) {
  assert(prepared.status === "ready", "comparison inputs not ready");
  const lines = prepared.structuralBytes.toString("utf8").split("\n");
  const imports = [];
  let i = 0;
  while (i < lines.length && /^import [A-Za-z_][A-Za-z_0-9.]*\r?$/.test(lines[i])) {
    imports.push(lines[i].trimEnd());
    i++;
  }
  assert(imports.length > 0, "structural module lacks imports");
  const body = lines.slice(i).join("\n");
  assert(!/^\s*import\s+/m.test(body), "non-leading structural import");
  assert(body.includes("namespace " + prepared.rightNS + "\n"), "missing structural namespace");
  assert(body.includes("end " + prepared.rightNS), "missing structural namespace end");
  const prefix = [...new Set([...imports, "import " + prepared.leftNS + ".Article"])]
    .join("\n") + "\n" + body + "\n";
  const declarations = "\nnamespace LatexSemanticProbe\n" +
    "private def left : Prop := " + prepared.leftNS + ".claim0\n" +
    "private def right : Prop := " + prepared.rightNS + ".claim\n";
  const typed = prefix + declarations + "end LatexSemanticProbe\n";
  const proof = prefix + declarations +
    "theorem definitional_equivalence : left ↔ right := by rfl\n" +
    "#print axioms definitional_equivalence\nend LatexSemanticProbe\n";
  return {typed, proof};
}
function execute(command, args, cwd) {
  const p = spawnSync(command, args, {cwd, shell:false, encoding:"utf8",
    timeout:180_000, maxBuffer:MAX_LOG_BYTES});
  return {exit_code:p.status, stdout:p.stdout || "", stderr:p.stderr || "",
    launch_error:p.error ? String(p.error) : null};
}
function saveStage(dir, name, result) {
  const outputs = {};
  for (const stream of ["stdout", "stderr"]) {
    const file = name + "." + stream;
    const bytes = Buffer.from(result[stream] || "", "utf8");
    fs.writeFileSync(path.join(dir, file), bytes, {flag:"wx"});
    outputs[file] = sha256(bytes);
  }
  return {exit_code:result.exit_code, launch_error:result.launch_error, logs:outputs};
}
export function runSemanticCase({sourceFile, caseDir, leanifyDir, executeCommand=execute}) {
  const prepared = prepareSemanticCase(fs.readFileSync(sourceFile), caseDir);
  const destination = path.join(caseDir, "semantic");
  fs.mkdirSync(destination); // never replace existing comparison evidence
  const publicRecord = {schema_version:1, ...Object.fromEntries(
    Object.entries(prepared).filter(([k]) => !["modules","structuralBytes"].includes(k))),
    toolchain: {leanify_commit:LEANIFY_COMMIT}, checks: {
      both_typed:false, definitional_equivalence:false, kernel_checked:false
    }};
  let work = null, namespaceDir = null;
  const finish = () => {
    fs.writeFileSync(path.join(destination, "comparison.json"),
      JSON.stringify(publicRecord, null, 2) + "\n", {flag:"wx"});
    return publicRecord;
  };
  if (prepared.status !== "ready") return finish();
  try {
    const cwd = path.resolve(leanifyDir);
    const revision = executeCommand("git", ["rev-parse", "HEAD"], cwd);
    assert(!revision.launch_error && revision.exit_code === 0 &&
      revision.stdout.trim() === LEANIFY_COMMIT, "untrusted Leanify checkout");
    const probes = makeProbes(prepared);
    work = fs.mkdtempSync(path.join(cwd, ".semantic-probe-"));
    namespaceDir = path.join(cwd, prepared.leftNS);
    fs.mkdirSync(namespaceDir); // refuse concurrent or pre-existing source
    for (const [name, bytes] of Object.entries(prepared.modules))
      fs.writeFileSync(path.join(namespaceDir, name), bytes, {flag:"wx"});
    const typedFile = path.join(work, "Typed.lean");
    const proofFile = path.join(work, "Proof.lean");
    fs.writeFileSync(typedFile, probes.typed);
    fs.writeFileSync(proofFile, probes.proof);
    publicRecord.probe_hashes = {
      typed: sha256(Buffer.from(probes.typed)),
      proof: sha256(Buffer.from(probes.proof))
    };
    const version = executeCommand("lake", ["env", "lean", "--version"], cwd);
    publicRecord.toolchain.lean_version = version.stdout.trim();
    assert(!version.launch_error && version.exit_code === 0, "Lean unavailable");
    const build = executeCommand("lake", ["build", prepared.leftNS + ".Article"], cwd);
    publicRecord.build = saveStage(destination, "build", build);
    if (build.launch_error || build.exit_code !== 0) {
      publicRecord.status = "tool_error";
      publicRecord.reason = "native Leanify module could not be rebuilt";
      return finish();
    }
    const typed = executeCommand("lake", ["env", "lean", typedFile], cwd);
    publicRecord.elaboration = saveStage(destination, "elaboration", typed);
    if (typed.launch_error) {
      publicRecord.status = "tool_error";
      publicRecord.reason = "Lean elaboration failed to start";
      return finish();
    }
    if (typed.exit_code !== 0) {
      publicRecord.status = "unelaboratable";
      publicRecord.reason = "one or both generated declarations failed to elaborate as Prop";
      return finish();
    }
    publicRecord.checks.both_typed = true;
    const proof = executeCommand("lake", ["env", "lean", proofFile], cwd);
    publicRecord.proof = saveStage(destination, "proof", proof);
    if (proof.launch_error) {
      publicRecord.status = "tool_error";
      publicRecord.reason = "Lean proof checker failed to start";
    } else if (proof.exit_code !== 0) {
      publicRecord.status = "unresolved";
      publicRecord.reason = "definitional equivalence not established; no inequivalence inferred";
    } else if (/(?:sorryAx|admit)/.test(proof.stdout + proof.stderr)) {
      publicRecord.status = "unresolved";
      publicRecord.reason = "admission detected in proof audit";
    } else {
      publicRecord.status = "definitionally_equivalent";
      publicRecord.reason = "Lean checked the generated Iff theorem by rfl";
      publicRecord.checks.definitional_equivalence = true;
      publicRecord.checks.kernel_checked = true;
    }
    return finish();
  } finally {
    if (namespaceDir) fs.rmSync(namespaceDir, {recursive:true, force:true});
    if (work) fs.rmSync(work, {recursive:true, force:true});
  }
}
