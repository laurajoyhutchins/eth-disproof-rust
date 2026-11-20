// Small, deterministic contract checker. Lean itself verifies the theorem.
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import {fileURLToPath} from "node:url";

const dirname = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(dirname,"../..");
const manifest = JSON.parse(fs.readFileSync(path.join(dirname,"mode-product-contraction.json"),"utf8"));
const pin = "d13f23b723b8a846827a245b89c10fc7d3f11612";
assert.equal(manifest.schema_version,1);
assert.equal(manifest.id,"mode-product-contraction");
assert.equal(manifest.formal_source.repository,"leanprover-community/mathlib4");
assert.equal(manifest.formal_source.commit,pin);
assert.equal(manifest.bridge.proof_status,"must_verify_with_pinned_lean");
assert.equal(manifest.literature.role,"contraction-framework-reference");
assert.match(manifest.literature.qualification,/not a theorem attributed/);
assert.equal(manifest.bridge.declaration,"ETH.LiteratureImports.mode_product_contraction");
for(const key of ["assumptions","unresolved","nonclaims"]) {
  assert.ok(Array.isArray(manifest.bridge[key]) && manifest.bridge[key].length,
    "missing explicit " + key);
}
for (const symbol of ["Finset.prod_univ_sum","Finset.sum_equiv"]) {
  assert.ok(manifest.formal_source.declarations.includes(symbol), "missing mathematical dependency");
}
const sourcePath=path.resolve(root,manifest.bridge.path);
assert.ok(sourcePath.startsWith(root + path.sep),"path outside repository");
const lean=fs.readFileSync(sourcePath,"utf8");
assert.match(lean,/theorem mode_product_contraction\b/);
assert.match(lean,/Finset\.prod_univ_sum/);
assert.match(lean,/Finset\.sum_equiv/);
assert.match(lean,/\bhvalid\b/);
assert.match(lean,/\bhfactor\b/);
assert.doesNotMatch(lean,/\b(?:sorry|admit)\b/);
console.log(JSON.stringify({status:"import_contract_matched",id:manifest.id,
  lean_file:manifest.bridge.path,mathlib_commit:pin,
  unresolved_obligations:manifest.bridge.unresolved.length}));
