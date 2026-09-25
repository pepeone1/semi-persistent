// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Canonical, nonempty congruences over unsigned finite-width words.
//! Core operations are inherent methods; meet uses external `BotOr` and
//! wrapping addition is specified by `Unsigned<W>` semantics.
#![allow(unused_imports, unused_variables)]
use crate::arithmetic::*;
use crate::lattice::BotOr;
use crate::semantics::*;
use crate::word::Word;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

/// `(0, r)` is a singleton; `(1, 0)` is top. Other canonical pairs
/// satisfy `r < m` and have a representable second member `r + m`.
/// Use `new` for raw pairs; fields cannot bypass normalization.
pub struct Congruence<W> {
    modulus: W,
    residue: W,
}

/// Raw descriptions use a congruence class, even for an unreduced residue.
pub open spec fn raw_has<W: Word>(m: W, r: W, x: W) -> bool {
    if m.view() == 0 { x == r }
    else { x.view() % m.view() == r.view() % m.view() }
}

/// A member after the least member is at least one full step away.
proof fn lemma_next(m: nat, r: nat, x: nat)
    requires m > 0, r < m, x % m == r,
    ensures r <= x, x == r || r + m <= x,
{
    lemma_mod_decreases(x, m);
    lemma_fundamental_div_mod(x as int, m as int);
    assert(x == r || r + m <= x) by (nonlinear_arith)
        requires m > 0, x == m * (x / m) + r;
}

/// Bridge executable word addition to the shared unsigned semantics.
fn wrapping_sum<W: Word>(a: W, b: W) -> (r: W)
    ensures r == Unsigned::<W>::add(a, b),
        r.view() == (a.view() + b.view()) % W::modulus(),
{
    let max = W::max().to_u64();
    let period = max as u128 + 1;
    let sum = a.to_u64() as u128 + b.to_u64() as u128;
    let residue = sum % period;
    let r = W::from_u64(residue as u64);
    proof {
        W::lemma_from_int((a.view() + b.view()) as int);
        W::lemma_view_injective(r, Unsigned::<W>::add(a, b));
    }
    r
}

impl<W: Word> Congruence<W> {
    pub closed spec fn modulus(&self) -> W { self.modulus }
    pub closed spec fn residue(&self) -> W { self.residue }

    pub open spec fn wf(&self) -> bool {
        self.modulus().view() == 0 || (
            self.residue().view() < self.modulus().view()
            && self.residue().view() + self.modulus().view() < W::modulus())
    }

    pub open spec fn gamma(&self, x: W) -> bool {
        if self.modulus().view() == 0 { x == self.residue() }
        else { x.view() % self.modulus().view() == self.residue().view() }
    }

    pub open spec fn has(&self, x: W) -> bool { self.gamma(x) }

    pub fn parts(&self) -> (r: (W, W))
        ensures r.0 == self.modulus(), r.1 == self.residue(),
    { (self.modulus, self.residue) }

    /// The canonical residue is the least member.
    pub proof fn residue_member(&self)
        requires self.wf(),
        ensures self.has(self.residue()),
    {
        if self.modulus.view() > 0 {
            lemma_small_mod(self.residue.view(), self.modulus.view());
        }
    }

    pub proof fn member_decomposition(&self, x: W)
        requires self.wf(), self.has(x),
        ensures x.view() >= self.residue().view(),
            self.modulus().view() > 0 ==> x.view() == self.residue().view()
                + self.modulus().view() * (x.view() / self.modulus().view()),
            self.modulus().view() == 0 ==> x == self.residue(),
    {
        self.lemma_least(x);
        if self.modulus.view() > 0 {
            lemma_fundamental_div_mod(x.view() as int, self.modulus.view() as int);
        }
    }

    /// Decide exact containment over representable words.
    pub fn refines(&self, other: &Self) -> (result: bool)
        requires self.wf(), other.wf(),
        ensures result == (forall|x: W| #[trigger] self.has(x) ==> other.has(x)),
    {
        proof { self.residue_member(); }
        if !other.contains(self.residue) { return false; }
        if self.modulus.eq(W::zero()) { return true; }
        let ghost second = self.lemma_second();
        proof { assert(self.has(second)); }
        if other.modulus.eq(W::zero()) {
            proof { assert(!other.has(second)); }
            return false;
        }
        let divides = self.modulus.urem(other.modulus).eq(W::zero());
        proof {
            if divides {
                lemma_fundamental_div_mod(self.modulus.view() as int, other.modulus.view() as int);
                assert forall|x: W| #[trigger] self.has(x) implies other.has(x) by {
                    self.member_decomposition(x);
                    let m = self.modulus.view() as int;
                    let n = other.modulus.view() as int;
                    let r = self.residue.view() as int;
                    let q = x.view() as int / m;
                    let d = m / n;
                    assert(x.view() as int == r + n * (d * q)) by (nonlinear_arith)
                        requires x.view() as int == r + m * q, m == n * d;
                    congruence_shift(x.view() as int, r, n, d * q);
                }
            } else {
                if other.has(second) {
                    lemma_mod_equivalence(second.view() as int, self.residue.view() as int,
                        other.modulus.view() as int);
                    assert(false);
                }
                assert(!other.has(second));
            }
        }
        divides
    }

    /// A divisor of the canonical stride preserves every member's residue.
    pub proof fn member_mod_divisor(&self, x: W, d: nat)
        requires self.wf(), self.has(x), d > 0,
            self.modulus().view() > 0 ==> self.modulus().view() % d == 0,
        ensures x.view() % d == self.residue().view() % d,
    {
        if self.modulus.view() > 0 {
            normalize_preserves_divisor(x.view(), self.modulus.view(), d);
        }
    }

    /// Sound upper bound using the GCD of strides and residue distance.
    pub fn join(&self, other: &Self) -> (r: Self)
        requires self.wf(), other.wf(),
        ensures r.wf(),
            forall|x: W| #[trigger] self.has(x) ==> r.has(x),
            forall|x: W| #[trigger] other.has(x) ==> r.has(x),
    {
        let a = self.residue.to_u64();
        let b = other.residue.to_u64();
        let distance = if a >= b { a - b } else { b - a };
        proof {
            self.residue.lemma_view_bounded();
            other.residue.lemma_view_bounded();
        }
        let delta = W::from_u64(distance);
        let stride_gcd = gcd(self.modulus, other.modulus);
        let modulus = gcd(stride_gcd, delta);
        if modulus.eq(W::zero()) {
            proof { W::lemma_view_injective(self.residue, other.residue); }
            return Self::constant(self.residue);
        }
        proof {
            lemma_gcd_divisor_iff(self.modulus.view(), other.modulus.view(), modulus.view());
            if a >= b {
                lemma_mod_equivalence(a as int, b as int, modulus.view() as int);
            } else {
                lemma_mod_equivalence(b as int, a as int, modulus.view() as int);
            }
        }
        let r = Self::new(modulus, self.residue);
        proof {
            assert forall|x: W| #[trigger] self.has(x) implies r.has(x) by {
                self.member_mod_divisor(x, modulus.view());
            }
            assert forall|x: W| #[trigger] other.has(x) implies r.has(x) by {
                other.member_mod_divisor(x, modulus.view());
            }
        }
        r
    }

    /// Cover all wrapping sums using gcd(strides, machine modulus).
    pub fn add(&self, other: &Self) -> (r: Self)
        requires self.wf(), other.wf(),
        ensures r.wf(),
            forall|x: W, y: W| #[trigger] self.has(x) && #[trigger] other.has(y)
                ==> r.has(Unsigned::<W>::add(x, y)),
    {
        let stride = gcd(self.modulus, other.modulus);
        let sum = wrapping_sum(self.residue, other.residue);
        if stride.eq(W::zero()) {
            return Self::constant(sum);
        }
        let wide_modulus = gcd_machine_modulus(stride);
        proof {
            W::lemma_modulus();
            stride.lemma_view_bounded();
            assert(wide_modulus <= stride.view()) by (nonlinear_arith)
                requires wide_modulus > 0, stride.view() > 0,
                    stride.view() % (wide_modulus as nat) == 0;
        }
        let modulus = W::from_u64(wide_modulus as u64);
        let r = Self::new(modulus, sum);
        proof {
            lemma_gcd_divisor_iff(self.modulus.view(), other.modulus.view(), modulus.view());
            lemma_wrapping_congruence::<W>(stride.view(),
                (self.residue.view() + other.residue.view()) as int);
            assert forall|x: W, y: W| #[trigger] self.has(x) && #[trigger] other.has(y)
                implies r.has(Unsigned::<W>::add(x, y)) by {
                self.member_mod_divisor(x, modulus.view());
                other.member_mod_divisor(y, modulus.view());
                lemma_add_mod_noop(x.view() as int, y.view() as int, modulus.view() as int);
                lemma_add_mod_noop(self.residue.view() as int, other.residue.view() as int,
                    modulus.view() as int);
                lemma_wrapping_congruence::<W>(stride.view(), (x.view() + y.view()) as int);
                W::lemma_from_int((x.view() + y.view()) as int);
            }
        }
        r
    }

    /// Exact intersection, with emptiness outside the domain.
    pub fn meet(&self, other: &Self) -> (result: BotOr<Self>)
        requires self.wf(), other.wf(),
        ensures match result {
            BotOr::Val(r) => r.wf() && (forall|x: W| #[trigger] r.has(x)
                <==> self.has(x) && other.has(x)),
            BotOr::Bot => forall|x: W| #[trigger] self.has(x) ==> !other.has(x),
        },
    {
        if self.modulus.eq(W::zero()) {
            return if other.contains(self.residue) {
                BotOr::Val(self.normalize())
            } else { BotOr::Bot };
        }
        if other.modulus.eq(W::zero()) {
            return if self.contains(other.residue) {
                BotOr::Val(other.normalize())
            } else { BotOr::Bot };
        }
        proof {
            lemma_small_mod(self.residue.view(), self.modulus.view());
            lemma_small_mod(other.residue.view(), other.modulus.view());
        }
        let merged = crt_merge(self.modulus, self.residue, other.modulus, other.residue);
        match merged {
            CrtMergeResult::Class { modulus, residue } => {
                let r = Self::new(modulus, residue);
                proof {
                    lemma_small_mod(residue.view(), modulus.view());
                    assert forall|x: W| #[trigger] r.has(x) <==> self.has(x) && other.has(x) by {
                        assert(merged.has(x) == is_common_congruence_solution(x.view() as int,
                            self.modulus.view(), self.residue.view(), other.modulus.view(), other.residue.view()));
                    }
                }
                BotOr::Val(r)
            },
            CrtMergeResult::Singleton { value } => {
                let r = Self::constant(value);
                proof {
                    assert forall|x: W| #[trigger] r.has(x) <==> self.has(x) && other.has(x) by {
                        assert(merged.has(x) == is_common_congruence_solution(x.view() as int,
                            self.modulus.view(), self.residue.view(), other.modulus.view(), other.residue.view()));
                    }
                }
                BotOr::Val(r)
            },
            CrtMergeResult::Empty => {
                proof {
                    assert forall|x: W| #[trigger] self.has(x) implies !other.has(x) by {
                        assert(merged.has(x) == is_common_congruence_solution(x.view() as int,
                            self.modulus.view(), self.residue.view(), other.modulus.view(), other.residue.view()));
                    }
                }
                BotOr::Bot
            },
        }
    }

    pub fn contains(&self, x: W) -> (r: bool)
        ensures r == self.gamma(x), r == self.has(x),
    {
        if self.modulus.eq(W::zero()) {
            proof { W::lemma_view_injective(x, self.residue); }
            x.eq(self.residue)
        } else { x.urem(self.modulus).eq(self.residue) }
    }

    pub fn constant(x: W) -> (r: Self)
        ensures r.wf(), r.modulus().view() == 0, r.residue() == x,
            forall|c: W| #[trigger] r.gamma(c) <==> c == x,
    { Self { modulus: W::zero(), residue: x } }

    pub fn top() -> (r: Self)
        ensures r.wf(), r.modulus().view() == 1, r.residue().view() == 0,
            forall|c: W| #[trigger] r.gamma(c),
    {
        proof { W::lemma_modulus(); }
        Self { modulus: W::one(), residue: W::zero() }
    }

    /// Normalize a raw class, collapsing progressions with only one word.
    /// For nonzero `modulus`, raw membership means `x % m == residue % m`,
    /// including when the input residue is not reduced. No addition wraps.
    pub fn new(modulus: W, residue: W) -> (r: Self)
        ensures r.wf(),
            forall|x: W| #[trigger] r.gamma(x) <==> raw_has(modulus, residue, x),
    {
        if modulus.eq(W::zero()) { Self::constant(residue) }
        else {
            let rem = residue.urem(modulus);
            proof { lemma_mod_bound(residue.view() as int, modulus.view() as int); }
            match rem.checked_add(modulus) {
                Some(second) => {
                    proof { second.lemma_view_bounded(); }
                    Self { modulus, residue: rem }
                },
                None => {
                    let r = Self::constant(rem);
                    proof {
                        assert forall|x: W| #[trigger] r.gamma(x) <==> raw_has(modulus, residue, x) by {
                            x.lemma_view_bounded();
                            lemma_small_mod(rem.view(), modulus.view());
                            if raw_has(modulus, residue, x) {
                                lemma_next(modulus.view(), rem.view(), x.view());
                                W::lemma_view_injective(x, rem);
                            }
                        }
                    }
                    r
                },
            }
        }
    }

    /// Already-constructed values are canonical, so normalization is identity.
    /// To normalize a raw/legacy pair, use `new(modulus, residue)`.
    pub fn normalize(&self) -> (r: Self)
        requires self.wf(),
        ensures r.wf(), r == *self,
            forall|x: W| #[trigger] r.gamma(x) == self.gamma(x),
    { Self { modulus: self.modulus, residue: self.residue } }

    pub proof fn lemma_nonempty(&self)
        requires self.wf(),
        ensures exists|c: W| self.gamma(c),
    {
        if self.modulus.view() > 0 { lemma_small_mod(self.residue.view(), self.modulus.view()); }
        assert(self.gamma(self.residue));
    }

    proof fn lemma_least(&self, x: W)
        requires self.wf(), self.gamma(x),
        ensures self.residue.view() <= x.view(),
            self.modulus.view() > 0 ==> (x == self.residue || self.residue.view() + self.modulus.view() <= x.view()),
    {
        if self.modulus.view() > 0 {
            lemma_next(self.modulus.view(), self.residue.view(), x.view());
            W::lemma_view_injective(x, self.residue);
        }
    }

    proof fn lemma_second(&self) -> (s: W)
        requires self.wf(), self.modulus.view() > 0,
        ensures self.gamma(s), s.view() == self.residue.view() + self.modulus.view(),
    {
        let i = self.residue.view() + self.modulus.view();
        let s = W::from_int(i as int);
        W::lemma_from_int(i as int);
        lemma_small_mod(i, W::modulus());
        lemma_mod_add_multiples_vanish(self.residue.view() as int, self.modulus.view() as int);
        lemma_small_mod(self.residue.view(), self.modulus.view());
        s
    }

    pub proof fn lemma_canonical(a: &Self, b: &Self)
        requires a.wf(), b.wf(),
            forall|c: W| #![trigger a.gamma(c)] a.gamma(c) == b.gamma(c),
        ensures *a == *b,
    {
        // Equal sets have the same least member, hence the same residue.
        a.lemma_nonempty();
        b.lemma_nonempty();
        if a.modulus.view() > 0 { lemma_small_mod(a.residue.view(), a.modulus.view()); }
        if b.modulus.view() > 0 { lemma_small_mod(b.residue.view(), b.modulus.view()); }
        assert(a.gamma(a.residue) && b.gamma(b.residue));
        assert(a.gamma(b.residue) && b.gamma(a.residue));
        a.lemma_least(b.residue);
        b.lemma_least(a.residue);
        W::lemma_view_injective(a.residue, b.residue);
        // Each nonconstant has a second member. It rules out equality with
        // a singleton and bounds the other progression's step from above.
        // Applying this in both directions forces equal moduli, including top.
        if a.modulus.view() > 0 {
            let s = a.lemma_second();
            assert(b.gamma(s));
            b.lemma_least(s);
        }
        if b.modulus.view() > 0 {
            let s = b.lemma_second();
            assert(a.gamma(s));
            a.lemma_least(s);
        }
        W::lemma_view_injective(a.modulus, b.modulus);
    }
}
} // verus!
