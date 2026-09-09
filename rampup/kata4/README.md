# Kata 4

## Goal

Explore interval lattice laws in Verus:

- Prove `meet` is commutative and idempotent.
- Prove `add` is monotone.
- Add an explicit `Bottom` value and re-prove the meet laws.

## Implementation

Implemented an interval domain over `u8` using:

- `Range { lo, hi }` for normal intervals.
- `Bottom` for the empty set.
- `meet` for interval intersection.
- `add` for interval addition.
- `subset_of` for interval containment.

If addition may overflow, the implementation conservatively returns:

```text
Range { lo: 0, hi: 255 }
```

## Verification

Verus successfully verifies:

- `meet(a, b) = meet(b, a)` (commutativity)
- `meet(a, a) = a` (idempotence)
- If `a1 ⊆ a2` and `b1 ⊆ b2`, then `a1 + b1 ⊆ a2 + b2` (add monotonicity)
- The meet laws still hold after adding `Bottom`.

Run:

```bash
cargo verus verify
```