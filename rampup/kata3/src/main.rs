use vstd::prelude::*;

verus! {

struct Interval {
    lo: u8,
    hi: u8,
}

impl Interval {
    spec fn wf(&self) -> bool {
        self.lo <= self.hi
    }

    spec fn has(&self, x: int) -> bool {
        self.lo as int <= x && x <= self.hi as int
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
        // overflow check
        if (self.hi as u16) + (other.hi as u16) > 255 {
            Interval {
                lo: 0,
                hi: 255,
            }
        } else {
            let new_lo = self.lo + other.lo;
            let new_hi = self.hi + other.hi;

            Interval {
                lo: new_lo,
                hi: new_hi,
            }
        }
    }


}

// proof fn add_sound(a: &Interval, b: &Interval, x: u8, y: u8)
//     requires
//         a.wf(),
//         b.wf(),
//         a.has(x as int),
//         b.has(y as int),
//         (x as int) + (y as int) <= 255,
//     ensures
//         a.add(b).has((x as int) + (y as int)),
// {
// }

fn main() {}

}