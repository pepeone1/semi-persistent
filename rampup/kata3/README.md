# Kata 3

## Goal

Implement an interval over `u8` with `has` and `add`, and use Verus to prove that the result contains the sum of any values contained in the input intervals.

## Implementation

```rust
struct Interval {
    lo: u8,
    hi: u8,
}
```

* `wf`: checks `lo <= hi`.
* `has`: checks whether a value is inside the interval.
* `add`: adds the lower and upper bounds.
* If the upper-bound addition may overflow `u8`, return Top `[0, 255]`.

The soundness contract is:

```rust
forall|x: int, y: int|
    self.has(x) && other.has(y) && x + y <= 255
    ==> result.has(x + y)
```

Verification:

```text
verification results:: 2 verified, 0 errors
```

## Comparison with `domains.rs`

The existing implementation uses the same `lo`/`hi`, `wf`, and `has` structure.

The main difference is overflow semantics. My implementation proves containment for non-overflowing mathematical sums. The existing implementation uses `wrapping_add` and proves containment of the actual machine-width wrapped result.

When wrapping makes a normal interval unsuitable, the existing implementation conservatively returns Top.
