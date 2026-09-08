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

This file is based on the running example from §2 of the practicum proposal.

```bash
EGRAPH_DUMP_PLAN=1 ./target/release/semi-persistent rampup/kata2/plan.egg
```

Output:

```text
ok — 12 nodes
```

No query plan was printed.

The current runnable §2 example only constructs terms and performs unions. It does not contain a rewrite or another matcher-driven query, so there is no query plan for `EGRAPH_DUMP_PLAN=1` to dump.

The guarded rewrite shown later in §2 uses `within`, which depends on abstract-guard functionality that is part of the later practicum work and is not available in the current engine.