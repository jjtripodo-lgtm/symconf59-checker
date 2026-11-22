"""Only the pinned ordinary Lean/Mathlib axiom closure is acceptable."""
import re,sys
path,count=sys.argv[1],int(sys.argv[2])
out=open(path).read()
pat=re.compile(r"'[^'\n]+' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)[ \t]*\n")
matches=list(pat.finditer(out))
if len(matches)!=count or ''.join(m[0] for m in matches)!=out:
    raise SystemExit(f'expected {count} well-formed axiom closures, got {len(matches)}')
allowed={'propext','Classical.choice','Quot.sound'}
for m in matches:
    names={x.strip() for x in m[1].split(',')} if m[1] else set()
    if names-allowed: raise SystemExit(f'nonstandard axiom: {m[0]}')
print(f'PASS: {count} scoped endpoint closures, standard kernel axioms only')
