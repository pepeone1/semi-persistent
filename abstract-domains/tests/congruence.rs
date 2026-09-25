// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Exhaustive oracle for the real executable Congruence<u8>.
use semi_persistent_abstract_domains::congruence::Congruence;
use std::collections::HashMap;

type C = Congruence<u8>;

fn check_wf(c: &C) {
    let (m, r) = c.parts();
    assert!(m == 0 || (r < m && u16::from(r) + u16::from(m) <= 255));
    assert!(c.contains(r));
}

// Enumerate the raw progression using widened arithmetic, independently of
// the implementation's remainder-based membership check.
fn oracle(m: u8, r: u8) -> [u64; 4] {
    let mut bits = [0; 4];
    let mut x = if m == 0 {
        u16::from(r)
    } else {
        u16::from(r % m)
    };
    loop {
        bits[usize::from(x / 64)] |= 1u64 << (x % 64);
        if m == 0 {
            break;
        }
        x += u16::from(m);
        if x > 255 {
            break;
        }
    }
    bits
}

#[test]
fn constants_and_top() {
    let top = C::top();
    check_wf(&top);
    assert_eq!(top.parts(), (1, 0));
    for r in 0..=u8::MAX {
        let c = C::constant(r);
        check_wf(&c);
        assert_eq!(c.parts(), (0, r));
        for x in 0..=u8::MAX {
            assert_eq!(c.contains(x), x == r);
            assert!(top.contains(x));
        }
    }
}

#[test]
fn exhaustive_raw_inputs_membership_normalization_and_canonicity() {
    let mut representatives = HashMap::new();
    for m in 0..=u8::MAX {
        for r in 0..=u8::MAX {
            let c = C::new(m, r);
            check_wf(&c);
            let expected = oracle(m, r);
            let copied = c;
            assert!(copied.same(&c));
            let reconstructed = C::new(c.parts().0, c.parts().1);
            assert_eq!(reconstructed.parts(), c.parts());
            let mut actual = [0u64; 4];
            for x in 0..=u8::MAX {
                let has = c.contains(x);
                assert_eq!(
                    has,
                    expected[usize::from(x / 64)] & (1u64 << (x % 64)) != 0,
                    "m={m}, r={r}, x={x}"
                );
                if has {
                    actual[usize::from(x / 64)] |= 1u64 << (x % 64);
                }
            }
            let cardinality: u32 = actual.iter().map(|bits| bits.count_ones()).sum();
            assert_eq!(c.is_top(), cardinality == 256);
            assert_eq!(c.as_constant().is_some(), cardinality == 1);
            if let Some(value) = c.as_constant() {
                assert!(c.contains(value));
            }
            assert!(c.same(&reconstructed));
            assert_eq!(c.same(&C::top()), actual == [u64::MAX; 4]);
            assert_eq!(c.same(&C::constant(r)), actual == oracle(0, r));
            assert_eq!(c.same(&C::new(3, r)), actual == oracle(3, r));
            // Every canonical representation is reached by its own raw pair.
            // Identical sets must always yield identical canonical pairs.
            if let Some(previous) = representatives.insert(actual, c.parts()) {
                assert_eq!(previous, c.parts(), "duplicate gamma for m={m}, r={r}");
            }
        }
    }
    // 256 singletons + sum(min(m, 256-m), m=1..255) progressions.
    assert_eq!(representatives.len(), 16_640);
}

#[test]
fn finite_width_singleton_and_second_member_boundary() {
    assert_eq!(C::new(201, 200).parts(), C::constant(200).parts());
    assert_eq!(C::new(128, 127).parts(), (128, 127));
    assert!(C::new(128, 127).contains(255));
    assert_eq!(C::new(129, 127).parts(), (0, 127));
    assert_eq!(C::new(255, 0).parts(), (255, 0));
    assert!(C::new(255, 0).contains(255));
    assert_eq!(C::new(255, 255).parts(), (255, 0));
    assert_eq!(C::new(4, 5).parts(), (4, 1));
    assert_eq!(C::new(1, 255).parts(), C::top().parts());
}

#[test]
fn generic_widths_and_width_aliases() {
    macro_rules! check {
        ($word:ty, $alias:ty) => {{
            let c = Congruence::<$word>::new(<$word>::MAX, <$word>::MAX - 1);
            assert_eq!(c.parts(), (0, <$word>::MAX - 1));
            let c: $alias = Congruence::<$word>::new(<$word>::MAX, 0);
            assert!(c.contains(0));
            assert!(c.contains(<$word>::MAX));
            assert!(!c.contains(1));
        }};
    }
    use semi_persistent_abstract_domains::domains::{d8, d16, d32, d64};
    check!(u8, d8::Congruence);
    check!(u16, d16::Congruence);
    check!(u32, d32::Congruence);
    check!(u64, d64::Congruence);
}

macro_rules! core_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::congruence::Congruence;
            type C = Congruence<$uint>;
            let max = <$uint>::MAX;
            let top = C::top();
            for x in [0, 1, max] {
                let singleton = C::constant(x);
                assert!(singleton.contains(x));
                assert!(!singleton.contains(x.wrapping_add(1)));
                assert!(singleton.refines(&top));
                assert!(!top.refines(&singleton));
            }
            let even = C::new(2, 0);
            let odd = C::new(2, 1);
            let four = C::new(4, 0);
            assert!(four.refines(&even));
            assert!(!even.refines(&four));
            assert!(!even.refines(&odd));
            assert!(even.refines(&even));

            let finite_singleton = C::new(max, 1);
            assert!(finite_singleton.refines(&C::constant(1)));
            assert!(C::constant(1).refines(&finite_singleton));
            assert!(finite_singleton.refines(&odd));
            let two_values = C::new(max, 0);
            assert!(!two_values.refines(&C::constant(0)));
            assert!(!two_values.refines(&even));

            for m in [0, 1, 2, max] {
                for r in [0, 1, max] {
                    let normalized = C::new(m, r).normalize();
                    let nr = if m == 0 { r } else { r % m };
                    let nm = if m != 0 && m > max - nr { 0 } else { m };
                    assert_eq!(normalized.parts(), (nm, nr));
                    let twice = normalized.normalize();
                    assert_eq!(twice.parts(), normalized.parts());
                    for x in [0, 1, 2, max - 1, max] {
                        assert_eq!(
                            normalized.contains(x),
                            if m == 0 { x == r } else { x % m == r % m }
                        );
                    }
                }
            }
        }
    };
}

core_cases!(core_u8, d8, u8);
core_cases!(core_u16, d16, u16);
core_cases!(core_u32, d32, u32);
core_cases!(core_u64, d64, u64);

#[test]
fn refinement_matches_finite_u8_sets() {
    use semi_persistent_abstract_domains::congruence::Congruence;
    type C = Congruence<u8>;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = C::new(m, r).normalize();
            let values: Vec<bool> = (0..=u8::MAX)
                .map(|x| if m == 0 { x == r } else { x % m == r % m })
                .collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let subset = av.iter().zip(bv).all(|(x, y)| !x || *y);
            assert_eq!(
                a.refines(b),
                subset,
                "({}, {}) refines ({}, {})",
                a.parts().0,
                a.parts().1,
                b.parts().0,
                b.parts().1
            );
        }
    }
}

use semi_persistent_abstract_domains::lattice::BotOr;

fn meet_value<W>(result: BotOr<Congruence<W>>) -> Congruence<W> {
    match result {
        BotOr::Val(value) => value,
        BotOr::Bot => panic!("expected nonempty intersection"),
    }
}

macro_rules! meet_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::congruence::Congruence;
            type C = Congruence<$uint>;
            let a = C::new(6, 1);
            let b = C::new(4, 3);
            let merged = meet_value(a.meet(&b));
            assert_eq!(merged.parts(), (12, 7));
            assert!(matches!(a.meet(&C::new(4, 2)), BotOr::Bot));
            let top = C::top();
            for (left, right) in [(&a, &top), (&top, &a), (&a, &a)] {
                let result = meet_value(left.meet(right));
                assert_eq!(result.parts(), a.parts());
            }
            for x in [0, 7] {
                let singleton = C::constant(x);
                for result in [a.meet(&singleton), singleton.meet(&a)] {
                    if x == 7 {
                        let r = meet_value(result);
                        assert_eq!(r.parts(), (0, x));
                    } else {
                        assert!(matches!(result, BotOr::Bot));
                    }
                }
                assert!(meet_value(singleton.meet(&singleton)).contains(x));
                assert!(matches!(singleton.meet(&C::constant(x + 1)), BotOr::Bot));
            }
            let max = <$uint>::MAX;
            for x in [0, 1, max] {
                let left = C::new(max, x % max);
                let right = C::new(max - 1, x % (max - 1));
                for result in [left.meet(&right), right.meet(&left)] {
                    let r = meet_value(result);
                    assert_eq!(r.parts(), (0, x));
                }
            }
            let left = C::new(max, max - 1);
            let right = C::new(max - 1, max - 2);
            assert!(matches!(left.meet(&right), BotOr::Bot));
            assert!(matches!(right.meet(&left), BotOr::Bot));
        }
    };
}

meet_cases!(meet_u8, d8, u8);
meet_cases!(meet_u16, d16, u16);
meet_cases!(meet_u32, d32, u32);
meet_cases!(meet_u64, d64, u64);

#[test]
fn meet_matches_finite_u8_sets() {
    use semi_persistent_abstract_domains::congruence::Congruence;
    type C = Congruence<u8>;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = C::new(m, r).normalize();
            let values: Vec<bool> = (0..=u8::MAX)
                .map(|x| if m == 0 { x == r } else { x % m == r % m })
                .collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let result = a.meet(b);
            if let BotOr::Val(r) = &result {
                let (m, r) = r.parts();
                assert!(m == 0 || (r < m && u16::from(r) + u16::from(m) <= 255));
            }
            let mut nonempty = false;
            for x in 0..=u8::MAX {
                let expected = av[x as usize] && bv[x as usize];
                nonempty |= expected;
                assert_eq!(
                    matches!(&result, BotOr::Val(r) if r.contains(x)),
                    expected,
                    "({}, {}) meet ({}, {}) at {x}",
                    a.parts().0,
                    a.parts().1,
                    b.parts().0,
                    b.parts().1
                );
            }
            assert_eq!(matches!(result, BotOr::Val(_)), nonempty);
        }
    }
}
