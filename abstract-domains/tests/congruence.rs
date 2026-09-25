// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

macro_rules! core_cases {
    ($name:ident, $domain:ident, $uint:ty) => {
        #[test]
        fn $name() {
            use semi_persistent_abstract_domains::domains::$domain::Congruence;
            let max = <$uint>::MAX;
            let top = Congruence::top();
            for x in [0, 1, max] {
                let singleton = Congruence::constant(x);
                assert!(singleton.contains(x));
                assert!(!singleton.contains(x.wrapping_add(1)));
                assert!(singleton.refines(&top));
                assert!(!top.refines(&singleton));
            }
            let even = Congruence { modulus: 2, residue: 0 };
            let odd = Congruence { modulus: 2, residue: 1 };
            let four = Congruence { modulus: 4, residue: 0 };
            assert!(four.refines(&even));
            assert!(!even.refines(&four));
            assert!(!even.refines(&odd));
            assert!(even.refines(&even));

            let finite_singleton = Congruence { modulus: max, residue: 1 };
            assert!(finite_singleton.refines(&Congruence::constant(1)));
            assert!(Congruence::constant(1).refines(&finite_singleton));
            assert!(finite_singleton.refines(&odd));
            let two_values = Congruence { modulus: max, residue: 0 };
            assert!(!two_values.refines(&Congruence::constant(0)));
            assert!(!two_values.refines(&even));

            for m in [0, 1, 2, max] {
                for r in [0, 1, max] {
                    let normalized = Congruence { modulus: m, residue: r }.normalize();
                    assert_eq!(normalized.modulus, m);
                    assert_eq!(normalized.residue, if m == 0 { r } else { r % m });
                    let twice = normalized.normalize();
                    assert_eq!((twice.modulus, twice.residue), (normalized.modulus, normalized.residue));
                    for x in [0, 1, 2, max - 1, max] {
                        assert_eq!(normalized.contains(x), if m == 0 { x == r } else { x % m == r % m });
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
    use semi_persistent_abstract_domains::domains::d8::Congruence;
    let mut classes = Vec::new();
    for m in [0, 1, 2, 3, 4, 127, 128, 129, 200, 254, 255] {
        for r in [0, 1, 2, 100, 127, 128, 200, 254, 255] {
            let c = Congruence { modulus: m, residue: r }.normalize();
            let values: Vec<bool> = (0..=u8::MAX).map(|x| {
                if m == 0 { x == r } else { x % m == r % m }
            }).collect();
            classes.push((c, values));
        }
    }
    for (a, av) in &classes {
        for (b, bv) in &classes {
            let subset = av.iter().zip(bv).all(|(x, y)| !x || *y);
            assert_eq!(a.refines(b), subset,
                "({}, {}) refines ({}, {})", a.modulus, a.residue, b.modulus, b.residue);
        }
    }
}
