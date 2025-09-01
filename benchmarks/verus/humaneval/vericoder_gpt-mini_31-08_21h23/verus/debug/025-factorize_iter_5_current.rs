use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::assert_by_contradiction;
use vstd::calc;
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> (result:bool) {
    forall|i: nat| 1 < i < n ==> #[trigger] (n % i) != 0
}
// pure-end
// pure-end


spec fn is_prime_factorization(n: nat, factorization: Seq<nat>) -> (result:bool) {

    &&& forall|i: int|
        0 <= i < factorization.len() ==> #[trigger] is_prime(
            factorization[i] as nat,
        )

    &&& factorization.fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat)
        == n

    &&& forall|i: nat, j: nat|
        (1 < i <= j < factorization.len()) ==> (#[trigger] factorization[i as int]
            <= #[trigger] factorization[j as int])
}
// pure-end

// <vc-helpers>
proof fn lemma_is_prime_from_trial(rem: nat, i: nat)
    requires
        rem > 1,
        i * i > rem,
        forall|p: nat| 2 <= p < i ==> rem % p != 0,
    ensures
        is_prime(rem)
{
    // If rem is already prime, done.
    if is_prime(rem) {
        return;
    }

    // Otherwise, there is a nontrivial divisor d of rem.
    let d = choose(|d: nat| 1 < d && d < rem && rem % d == 0);
    let e = rem / d;
    // d * e == rem
    assert(d * e == rem);

    // It cannot be that both d >= i and e >= i, because then d * e >= i * i > rem.
    if d >= i && e >= i {
        // contradiction: d * e >= i * i > rem, but d * e == rem
        assert(d * e >= i * i);
        assert(i * i > rem);
        assert(d * e > rem);
        assert(false); // contradiction
    } else {
        // So one of d < i or e < i. Either way we have a divisor < i, contradicting the assumption.
        if d < i {
            assert(2 <= d); // since 1 < d
            assert(rem % d == 0);
            // contradicts the assumption that no p in 2..i-1 divides rem
            assert(false);
        } else {
            // e < i
            assert(e > 1);
            assert(2 <= e);
            assert(rem % e == 0);
            // contradicts the assumption
            assert(false);
        }
    }
}

proof fn lemma_dividing_implies_factor_is_prime(rem: nat, i: nat)
    requires
        2 <= i,
        rem >= 1,
        rem % i == 0,
        forall|p: nat| 2 <= p < i ==> rem % p != 0,
    ensures
        is_prime(i)
{
    // If i is already prime, done.
    if is_prime(i) {
        return;
    }

    // Otherwise, i has a non-trivial divisor d with 1 < d < i.
    let d = choose(|d: nat| 1 < d && d < i && i % d == 0);
    // Because i divides rem, any divisor of i also divides rem.
    // Let q = i / d, so i = d * q.
    let q = i / d;
    assert(i == d * q);
    // rem = i * (rem / i), so rem is a multiple of i, hence of d.
    // Therefore rem % d == 0, contradicting the assumption that no p < i divides rem.
    assert(rem % d == 0);
    assert(false);
}
// </vc-helpers>

// <vc-spec>
fn factorize(n: u8) -> (factorization: Vec<u8>)
    // pre-conditions-start
    requires
        1 <= n <= u8::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_prime_factorization(n as nat, factorization@.map(|_idx, j: u8| j as nat)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut rem: nat = n as nat;
    let mut i: nat = 2;
    let mut res: Vec<u8> = Vec::new();

    while i * i <= rem
        invariant
            rem >= 1
        &&& 2 <= i
        &&& (res@.fold_right(|x: u8, acc: nat| (acc * (x as nat)), 1nat)) * rem == n as nat
        &&& forall|k: int| 0 <= k && (k < res@.len()) ==> #[trigger] is_prime(res@[k] as nat)
        &&& forall|p: nat, q: nat| (1 < p && p <= q && q < res@.len()) ==> (#[trigger] res@[p as int] <= #[trigger] res@[q as int])
        &&& forall|p: nat| 2 <= p && p < i ==> rem % p != 0
        &&& forall|k: int| 0 <= k && (k < res@.len()) ==> (res@[k] as nat) <= i
    {
        if rem % i == 0 {
            // i divides rem and no p < i divides rem, so i is prime
            proof {
                lemma_dividing_implies_factor_is_prime(rem, i);
            }
            res.push(i as u8);
            // update remainder
            rem = rem / i;
            // product invariant follows from rem_old == i * rem_new and res updated with i
            assert((res@.fold_right(|x: u8, acc: nat| (acc * (x as nat)), 1nat)) * rem == n as nat);
        } else {
            // move to next potential factor
            i = i + 1;
            // the invariant forall|p| 2 <= p < i ==> rem % p != 0 is maintained:
            // for p < i (new), either p < old i (holds by invariant) or p == old i (we know rem % old i != 0 in this branch)
        }
    }

    if rem > 1 {
        // rem is prime by trial division property
        proof {
            lemma_is_prime_from_trial(rem, i);
        }
        res.push(rem as u8);
    }

    res
}
// </vc-code>

} // verus!
fn main() { }