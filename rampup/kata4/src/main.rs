use vstd::prelude::*;

verus! {

#[derive(Clone, Copy, PartialEq, Eq)]
enum Interval {
    Bottom,
    Range { lo: u8, hi: u8 },
}

impl Interval {
    spec fn wf(&self) -> bool {
        match self {
            Interval::Bottom => true,
            Interval::Range { lo, hi } => *lo <= *hi,
        }
    }

    spec fn has(&self, x: int) -> bool {
        match self {
            Interval::Bottom => false,
            Interval::Range { lo, hi } => {
                *lo as int <= x && x <= *hi as int
            }
        }
    }

    fn add(&self, other: &Interval) -> (result: Interval)
        // require wf()
        requires
            self.wf(),
            other.wf(),
        // ensure retuslt is well-formed
        ensures
            result.wf(),
            forall|x: int, y: int|
                self.has(x) && other.has(y) && x + y <= 255
                ==> result.has(x + y),
    {
        match (self, other) {
            // Bottom + anything = Bottom
            (Interval::Bottom, _) => {
                Interval::Bottom
            }

            (_, Interval::Bottom) => {
                Interval::Bottom
            }

            (
                Interval::Range {
                    lo: lo1,
                    hi: hi1
                },
                Interval::Range {
                    lo: lo2,
                    hi: hi2
                },
            ) => {
                // overflow
                if (*hi1 as u16) + (*hi2 as u16) > 255 {
                    Interval::Range {
                        lo: 0,
                        hi: 255,
                    }
                } else {
                    let new_lo = *lo1 + *lo2;
                    let new_hi = *hi1 + *hi2;

                    Interval::Range {
                        lo: new_lo,
                        hi: new_hi,
                    }
                }
            }
        }
    }

    fn meet(&self, other: &Interval) -> (result: Interval)
        requires
            self.wf(),
            other.wf(),
        ensures
            result.wf(),
            forall|x: int|
                self.has(x) && other.has(x)
                ==> result.has(x),
            result == self.meet_spec(other),
    {
        match (self, other) {
            (Interval::Bottom, _) => {
                Interval::Bottom
            }

            (_, Interval::Bottom) => {
                Interval::Bottom
            }

            (
                Interval::Range {
                    lo: lo1,
                    hi: hi1
                },
                Interval::Range {
                    lo: lo2,
                    hi: hi2
                },
            ) => {
                let new_lo =
                    if *lo1 > *lo2 {
                        *lo1
                    } else {
                        *lo2
                    };

                let new_hi =
                    if *hi1 < *hi2 {
                        *hi1
                    } else {
                        *hi2
                    };

                if new_lo > new_hi {
                    Interval::Bottom
                } else {
                    Interval::Range {
                        lo: new_lo,
                        hi: new_hi,
                    }
                }
            }
        }
    }

    // spec function for proof to call
    spec fn meet_spec(&self, other: &Interval) -> Interval {
        match (self, other) {
            (Interval::Bottom, _) => Interval::Bottom,

            (_, Interval::Bottom) => Interval::Bottom,

            (
                Interval::Range {
                    lo: lo1, hi: hi1
                },
                Interval::Range {
                    lo: lo2, hi: hi2
                },
            ) => {
                let new_lo =
                    if *lo1 > *lo2 {
                        *lo1
                    } else {
                        *lo2
                    };

                let new_hi =
                    if *hi1 < *hi2 {
                        *hi1
                    } else {
                        *hi2
                    };

                if new_lo > new_hi {
                    Interval::Bottom
                } else {
                    Interval::Range {
                        lo: new_lo,
                        hi: new_hi,
                    }
                }
            }
        }
    }

    // spec function for monotone proof
    spec fn subset_of(&self, other: &Interval) -> bool {
        match (self, other) {
            // ∅ is a subset of any interval
            (Interval::Bottom, _) => true,

            // any interval is not a subset of ∅
            (Interval::Range { .. }, Interval::Bottom) => false,

            (
                Interval::Range {
                    lo: lo1,
                    hi: hi1
                },
                Interval::Range {
                    lo: lo2,
                    hi: hi2
                },
            ) => {
                *lo1 >= *lo2 && *hi1 <= *hi2
            }
        }
    }

    spec fn add_spec(&self, other: &Interval) -> Interval {
        match (self, other) {
            (Interval::Bottom, _) => Interval::Bottom,
            (_, Interval::Bottom) => Interval::Bottom,

            (
                Interval::Range {
                    lo: lo1,
                    hi: hi1
                },
                Interval::Range {
                    lo: lo2,
                    hi: hi2
                },
            ) => {
                if (*hi1 as int) + (*hi2 as int) > 255 {
                    Interval::Range {
                        lo: 0,
                        hi: 255,
                    }
                } else {
                    Interval::Range {
                        lo: ((*lo1 as int) + (*lo2 as int)) as u8,
                        hi: ((*hi1 as int) + (*hi2 as int)) as u8,
                    }
                }
            }
        }
    }
}

// commutative proof
proof fn meet_commutative(a: &Interval, b: &Interval)
    requires
        a.wf(),
        b.wf(),
    ensures
        a.meet_spec(b) == b.meet_spec(a),
{
}

// idempotent proof
proof fn meet_idempotent(a: &Interval)
    requires
        a.wf(),
    ensures
        a.meet_spec(a) == *a,
{
}

// monotone proof
// if:
// a1 ⊆ a2
// b1 ⊆ b2
// then:
// a1 + b1 ⊆ a2 + b2
proof fn add_monotone(
    a1: &Interval,
    a2: &Interval,
    b1: &Interval,
    b2: &Interval,
)
    requires
        a1.wf(),
        a2.wf(),
        b1.wf(),
        b2.wf(),
        a1.subset_of(a2),
        b1.subset_of(b2),
    ensures
        a1.add_spec(b1).subset_of(&a2.add_spec(b2)),
{
}

fn main() {}

}