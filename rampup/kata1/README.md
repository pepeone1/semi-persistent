# Kata 1

## Union-Find

`union_find.rs` implements union-find from scratch with:

- Path compression in `find`
- Union by rank
- A naive set-of-sets model for comparison

The tests perform many unions and check that the union-find and naive model agree on which elements belong to the same set.

Run:

```bash
rustc --test union_find.rs -o union_find_test
./union_find_test
```

## Toy E-Graph

`toy_egraph.rs` implements a small e-graph with:

- add
- find
- union
- Hash-consing
- rebuild

The regression test demonstrates why `rebuild` is necessary. After merging `a` and `b`, `f(a)` and `f(b)` are not immediately merged. After `rebuild`, they become equal through congruence.

Run:

```bash
rustc --test toy_egraph.rs -o toy_egraph_test
./toy_egraph_test
```