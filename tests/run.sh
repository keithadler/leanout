#!/bin/sh
# End-to-end tests. Usage: tests/run.sh [path-to-lean-kernel-replay-binary]
# Needs: lake build done; optionally `tenet` (DOTNET_ROOT set) and a replay checker binary.
set -u
cd "$(dirname "$0")/.."
BIN=.lake/build/bin/leanout
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
KERNEL=${1:-}
fail=0
check() { if [ "$2" = "$3" ]; then echo "ok   $1"; else echo "FAIL $1 (got $2, want $3)"; fail=1; fi; }

$BIN Init --prefix Nat.add_comm -o "$T/a.ndjson"
$BIN --validate "$T/a.ndjson" 2>/dev/null; check "validate good export" $? 0

# deterministic output
$BIN Init --prefix Nat.add_comm -o "$T/b.ndjson"; cmp -s "$T/a.ndjson" "$T/b.ndjson"; check "deterministic" $? 0

# single constant, explicit root
$BIN Init -- Nat.add_comm -o "$T/c.ndjson" 2>/dev/null || $BIN -o "$T/c.ndjson" Init -- Nat.add_comm
$BIN --validate "$T/c.ndjson" 2>/dev/null; check "validate single-root export" $? 0

# structural negative: delete a name line
python3 -I - "$T/a.ndjson" "$T/bad1.ndjson" "$T/bad2.ndjson" <<'PY'
import json,sys
src,o1,o2=sys.argv[1:]
L=open(src).read().splitlines()
i=next(k for k,l in enumerate(L) if '"in":5,' in l or l.startswith('{"in":5'))
open(o1,'w').write("\n".join(L[:i]+L[i+1:])+"\n")
# semantic negative: swap the types of two theorems
th=[k for k,l in enumerate(L) if l.startswith('{"thm"')]
a,b=th[0],th[-1]
ja,jb=json.loads(L[a]),json.loads(L[b])
ja['thm']['type'],jb['thm']['type']=jb['thm']['type'],ja['thm']['type']
L[a],L[b]=json.dumps(ja,separators=(',',':')),json.dumps(jb,separators=(',',':'))
open(o2,'w').write("\n".join(L)+"\n")
PY
$BIN --validate "$T/bad1.ndjson" 2>/dev/null; check "validator rejects missing name" $? 1

TEN=$(command -v tenet || echo "$HOME/.dotnet/tools/tenet")
if [ -x "$TEN" ]; then
  DOTNET_ROOT=${DOTNET_ROOT:-$HOME/.dotnet} $TEN check "$T/a.ndjson" --quiet >/dev/null 2>&1; check "tenet accepts" $? 0
  DOTNET_ROOT=${DOTNET_ROOT:-$HOME/.dotnet} $TEN check "$T/bad2.ndjson" --quiet >/dev/null 2>&1; r=$?
  [ $r -ne 0 ]; check "tenet rejects swapped theorem types" $? 0
fi
if [ -n "$KERNEL" ]; then
  $KERNEL "$T/a.ndjson" >/dev/null 2>&1; check "lean kernel accepts" $? 0
  $KERNEL "$T/bad2.ndjson" >/dev/null 2>&1; r=$?
  [ $r -ne 0 ]; check "lean kernel rejects swapped theorem types" $? 0
fi
# fixtures: mutual/nested/reflexive/indexed inductives, structures, quotients, literals, wf recursion
lake build Fixtures >/dev/null 2>&1
lake env $BIN Fixtures --module Fixtures -o "$T/fx.ndjson"; check "fixtures export" $? 0
$BIN --validate "$T/fx.ndjson" 2>/dev/null; check "validate fixtures" $? 0
grep -q unsafeId "$T/fx.ndjson"; [ $? -ne 0 ]; check "unsafe code skipped by default" $? 0
lake env $BIN Fixtures --module Fixtures --unsafe -o "$T/fxu.ndjson"; grep -q unsafeId "$T/fxu.ndjson"; check "--unsafe includes unsafe code" $? 0

# gzip output, --exclude, --module
$BIN Init --prefix Nat.add --exclude Nat.add_ -o "$T/z.ndjson.gz"; gunzip -c "$T/z.ndjson.gz" > "$T/z.ndjson"
$BIN --validate "$T/z.ndjson" 2>/dev/null; check "gzip output round-trips and validates" $? 0
grep -q '"str":"add_comm"' "$T/z.ndjson"; [ $? -ne 0 ]; check "--exclude drops roots" $? 0

# semantic negative on fixtures: swap recursor rule right-hand sides
python3 -I - "$T/fx.ndjson" "$T/bad3.ndjson" <<'PY'
import json,sys
src,dst=sys.argv[1:]
L=open(src).read().splitlines()
done=False
for k,l in enumerate(L):
    if l.startswith('{"inductive"') and not done:
        j=json.loads(l)
        for r in j['inductive']['recs']:
            if len(r['rules'])>=2 and r['rules'][0]['rhs']!=r['rules'][1]['rhs']:
                a,b=r['rules'][0],r['rules'][1]
                a['rhs'],b['rhs']=b['rhs'],a['rhs']; done=True; break
        if done: L[k]=json.dumps(j,separators=(',',':'))
assert done
open(dst,'w').write("\n".join(L)+"\n")
PY
if [ -x "$HOME/.dotnet/tools/tenet" ]; then
  DOTNET_ROOT=${DOTNET_ROOT:-$HOME/.dotnet} $TEN check "$T/fx.ndjson" --quiet >/dev/null 2>&1; check "tenet accepts fixtures" $? 0
  DOTNET_ROOT=${DOTNET_ROOT:-$HOME/.dotnet} $TEN check "$T/bad3.ndjson" --quiet >/dev/null 2>&1; [ $? -ne 0 ]; check "tenet rejects swapped recursor rules" $? 0
fi
if [ -n "$KERNEL" ]; then
  $KERNEL "$T/fx.ndjson" >/dev/null 2>&1; check "lean kernel accepts fixtures" $? 0
  $KERNEL "$T/bad3.ndjson" >/dev/null 2>&1; [ $? -ne 0 ]; check "lean kernel rejects swapped recursor rules" $? 0
fi
exit $fail
