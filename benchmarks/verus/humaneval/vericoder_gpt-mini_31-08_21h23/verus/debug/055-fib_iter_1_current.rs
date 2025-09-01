use vstd::prelude::*;

verus! {

#[verifier::memoize]
spec fn spec_fib(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        1
    } else {
        spec_fib((n - 1) as nat) + spec_fib((n - 2) as nat)
    }
}
// pure-end
// pure-end

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// pure-end

// <vc-helpers>
use core::ops::Add;

#[verifier::proof]
fn lemma_fib_rec(n: nat)
    ensures spec_fib(n + 2) == spec_fib(n) + spec_fib(n + 1)
    decreases n
{
    if n == 0 {
        // spec_fib(2) == spec_fib(1) + spec_fib(0)
        assert(spec_fib(2) == spec_fib(1) + spec_fib(0));
    } else {
        lemma_fib_rec(n - 1);
        // By the definition of spec_fib, the recurrence holds for all n
        assert(spec_fib(n + 2) == spec_fib(n + 1) + spec_fib(n));
    }
}

#[verifier::proof]
fn lemma_fib_nondec(n: nat)
    ensures spec_fib(n) <= spec_fib(n + 1)
    decreases n
{
    if n == 0 {
        assert(spec_fib(0) <= spec_fib(1));
    } else {
        // spec_fib(n+1) = spec_fib(n) + spec_fib(n-1) >= spec_fib(n)
        lemma_fib_rec(n - 1); // gives spec_fib(n+1) == spec_fib(n) + spec_fib(n-1)
        assert(spec_fib(n) <= spec_fib(n + 1));
    }
}

#[verifier::proof]
fn lemma_fib_monotone(k: nat, n: nat)
    requires k <= n
    ensures spec_fib(k) <= spec_fib(n)
    decreases n - k
{
    if k == n {
        // trivially equal
    } else {
        // k < n
        lemma_fib_monotone(k, n - 1);
        lemma_fib_nondec(n - 1); // spec_fib(n-1) <= spec_fib(n)
        assert(spec_fib(k) <= spec_fib(n));
    }
}

#[verifier::proof]
fn lemma_checked_add_some_eq(a: u32, b: u32, c: u32)
    requires a.checked_add(b) == Some(c)
    ensures (a as nat) + (b as nat) == (c as nat)
{
    // From the semantics of checked_add, when Some(c) is returned, c equals the mathematical sum modulo 2^32,
    // but since checked_add returned Some, there was no overflow and thus the mathematical sum fits in u32.
    // Therefore the cast to nat preserves the sum.
    assert((a as nat) + (b as nat) == (c as nat));
}

#[verifier::proof]
fn lemma_checked_add_none_overflow(a: u32, b: u32)
    requires a.checked_add(b) == None
    ensures (a as nat) + (b as nat) > (u32::MAX as nat)
{
    // If checked_add returns None, then the true sum does not fit in u32, hence greater than u32::MAX.
    assert((a as nat) + (b as nat) > (u32::MAX as nat));
}
// </vc-helpers>

// <vc-spec>
fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut i: u32 = 0;
    let mut a: u32 = 0; // fib(0)
    let mut b: u32 = 1; // fib(1)

    // loop until i == n, maintaining a == spec_fib(i) and b == spec_fib(i+1)
    while i < n
        invariant
            i <= n,
            (a as nat) == spec_fib(i as nat),
            (b as nat) == spec_fib((i as nat) + 1),
        decreases (n - i)
    {
        if i + 1 == n {
            // one final step: advance i by 1 without performing an addition that could overflow beyond needed
            // new i = i+1, new a = b which equals spec_fib(i+1)
            i = i + 1;
            a = b;
            // invariant preserved automatically: a == spec_fib(i)
        } else {
            // i + 1 < n => it's safe to compute next = a + b corresponding to spec_fib(i+2)
            match a.checked_add(b) {
                None => {
                    // overflow detected: (a as nat) + (b as nat) > u32::MAX
                    lemma_checked_add_none_overflow(a, b);
                    // (a as nat) + (b as nat) == spec_fib(i+2)
                    lemma_fib_rec(i as nat);
                    // therefore spec_fib(i+2) > u32::MAX
                    assert(spec_fib((i as nat) + 2) > (u32::MAX as nat));
                    // since i + 2 <= n (because i+1 < n), spec_fib(n) >= spec_fib(i+2)
                    lemma_fib_monotone((i as nat) + 2, n as nat);
                    // conclude spec_fib(n) > u32::MAX, so return None satisfies postcondition
                    return None;
                }
                Some(tmp) => {
                    // tmp as nat == (a as nat) + (b as nat)
                    lemma_checked_add_some_eq(a, b, tmp);
                    // by recurrence, that's spec_fib(i+2)
                    lemma_fib_rec(i as nat);
                    assert((tmp as nat) == spec_fib((i as nat) + 2));
                    // advance: new a = b (fib(i+1)), new b = tmp (fib(i+2)), i += 1
                    a = b;
                    b = tmp;
                    i = i + 1;
                    // invariants preserved: (a as nat) == spec_fib(i), (b as nat) == spec_fib(i+1)
                }
            }
        }
    }

    // at exit i == n and a == spec_fib(n)
    return Some(a);
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}