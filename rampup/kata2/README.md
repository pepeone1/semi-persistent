# Kata 2

## Saturating Rule Set

`saturating.egg` contains a rewrite that reaches saturation.

```bash
./target/release/semi-persistent rampup/kata2/saturating.egg
```

Output:

```text
ok — 4 nodes
```

The rule rewrites `f(a)` to `f(b)`. After the equality is established, the rule produces no new information, so the e-graph reaches saturation.


## Diverging Rule Set

`diverging.egg` contains a rewrite that keeps generating new terms.

```bash
./target/release/semi-persistent rampup/kata2/diverging.egg
```

Output:

```text
ok — 22 nodes
```

The rule rewrites `up(x)` to `up(s(x))`, repeatedly adding another `s`. It does not naturally reach saturation, so the run is stopped after 10 iterations.


## Union-by

`union_by.egg` demonstrates that the surviving e-class representative can depend on the `--union-by` policy.

```bash
./target/release/semi-persistent rampup/kata2/union_by.egg --union-by rank
./target/release/semi-persistent rampup/kata2/union_by.egg --union-by size
./target/release/semi-persistent rampup/kata2/union_by.egg --union-by uses
./target/release/semi-persistent rampup/kata2/union_by.egg --union-by sum
```

Results:

```text
rank -> e-class 0
size -> e-class 0
uses -> e-class 3
sum  -> e-class 3
```

The equality relation is the same under all policies, but different policies can choose different surviving representatives.


## Query Plan

This file is based on the running example from §2 of the practicum proposal. Two rewrite rules were added so that the matcher can generate query plans.

```lisp
(rewrite (Add x (Lit 0)) x)
(rewrite (Ite (True) x y) x)
```

Run with:

```bash
EGRAPH_DUMP_PLAN=1 ./target/release/semi-persistent rampup/kata2/plan.egg
```

### Rule 1: `(Add x (Lit 0))`

```text
=== plan: 3 atoms, 7 steps ===
step[0]: Join target=v2 atom=2 lookups=[ByOp { op: op56 }]
step[1]: ExtractChild target=v3 parent=v2 pos=0
step[2]: ExtractChild target=v1 parent=v2 pos=1
step[3]: Join target=v1 atom=1 lookups=[ByRepr { repr: VarId(1) }, ByOp { op: op55 }]
step[4]: ExtractChild target=v0 parent=v1 pos=0
step[5]: Join target=v0 atom=0 lookups=[ByRepr { repr: VarId(0) }, ByOp { op: op50 }]
step[6]: CheckLit node=v0
```

The steps match `(Add x (Lit 0))` as follows:

1. `Join` finds an `Add` node
2. `ExtractChild` gets the first child `x`
3. `ExtractChild` gets the second child `(Lit 0)`
4. `Join` checks that the second child is a `Lit`
5. `ExtractChild` gets the literal value
6. `Join` finds the literal node
7. `CheckLit` checks that the literal value is `0`

### Rule 2: `(Ite (True) x y)`

```text
=== plan: 2 atoms, 5 steps ===
step[0]: Join target=v1 atom=1 lookups=[ByOp { op: op57 }]
step[1]: ExtractChild target=v0 parent=v1 pos=0
step[2]: ExtractChild target=v2 parent=v1 pos=1
step[3]: ExtractChild target=v3 parent=v1 pos=2
step[4]: Join target=v0 atom=0 lookups=[ByRepr { repr: VarId(0) }, ByOp { op: op53 }]
```

The steps match `(Ite (True) x y)` as follows:

1. `Join` finds an `Ite` node
2. `ExtractChild` gets the condition
3. `ExtractChild` gets the then-arm `x`
4. `ExtractChild` gets the else-arm `y`
5. `Join` checks that the condition is `True`

The planner can also choose a different join order:

```text
=== plan: 2 atoms, 5 steps ===
step[0]: Join target=v0 atom=0 lookups=[ByOp { op: op53 }]
step[1]: Join target=v1 atom=1 lookups=[ByOp { op: op57 }, ByChildPos { child: Local(VarId(0)), pos: 0 }]
step[2]: CheckChildEq parent=v1 pos=0 expected=Local(VarId(0))
step[3]: ExtractChild target=v2 parent=v1 pos=1
step[4]: ExtractChild target=v3 parent=v1 pos=2
```

In this plan, the matcher first finds `True`. It then uses `ByChildPos` to find `Ite` nodes whose first child is that `True`, checks the child equality, and extracts the two remaining children.