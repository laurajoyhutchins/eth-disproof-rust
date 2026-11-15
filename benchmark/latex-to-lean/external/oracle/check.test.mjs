import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import {fileURLToPath} from "node:url";
import {probeSource} from "./check.mjs";
const dir=path.dirname(fileURLToPath(import.meta.url));
test("external oracle definitions are independent of frontend modules",()=>{
 const src=fs.readFileSync(path.join(dir,"ExternalGold.lean"),"utf8");
 assert.match(src,/namespace ExternalGold/);
 assert.match(src,/def O01 : Prop/);
 assert.match(src,/def D01 : Prop/);
 assert.match(src,/def N02 : Prop/);
 assert.doesNotMatch(src,/\b(?:sorry|admit|axiom)\b(?!s)/);
 assert.doesNotMatch(src,/def D02 : Prop/); // complex generalized binomial needs context
 assert.doesNotMatch(src,/\b(?:Unified|Struct[0-9a-f]{16})/);
});
test("oracle checks use actual generated declarations rather than text",()=>{
 const p=probeSource("O01","Unified01234567890123456789","leanify");
 assert.match(p,/import Unified01234567890123456789.Article/);
 assert.match(p,/ExternalGold.O01 ↔ Unified01234567890123456789.claim0/);
 assert.match(p,/:= by rfl/);
 assert.doesNotMatch(p,/\bsorry\b/);
 const s=probeSource("N01","Struct0123456789abcdef","structural");
 assert.match(s,/import Struct0123456789abcdef/);
 assert.match(s,/ExternalGold.N01 ↔ Struct0123456789abcdef.claim/);
 for(const x of ["../../bad","O01\\naxiom k : False"])
   assert.throws(()=>probeSource(x,"Safe","structural"));
});
