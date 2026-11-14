#!/usr/bin/env node
// Enforce exact one-clause semantic mutations against the immutable originals.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
const dirname=path.dirname(new URL(import.meta.url).pathname);
const manifest=JSON.parse(fs.readFileSync(path.join(dirname,'manifest.json'),'utf8'));
if(manifest.schema_version!==1||manifest.mutations.length!==3)throw Error('wrong mutation manifest');
const ids=new Set(),bases=new Set();
const hashes=[];
for(const m of manifest.mutations){
 if(ids.has(m.id)||bases.has(m.base))throw Error('duplicate mutation');
 ids.add(m.id);bases.add(m.base);
 const source=fs.readFileSync(path.resolve(dirname,'../cases',m.base+'.tex'),'utf8');
 const mutant=fs.readFileSync(path.join(dirname,'cases',m.id+'.tex'),'utf8');
 if(!m.from||!m.to||m.from===m.to||source.split(m.from).length!==2)throw Error(m.id+' does not have a unique original clause');
 if(source.replace(m.from,m.to)!==mutant)throw Error(m.id+' is not an exact one-clause mutation');
 hashes.push({id:m.id,base:m.base,source_sha256:crypto.createHash('sha256').update(mutant).digest('hex'),false_claim_index:m.falseClaim});
}
console.log(JSON.stringify({mutations:hashes},null,2));
