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
spec fn is_prime_fold(s: Seq<nat>) -> (result: nat) {
    if s.len() == 0 {
        1
    } else {
        s[0] * is_prime_fold(s.skip(1))
    }
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
    let mut n_ = n as nat;
    let mut factors: Vec<u8> = Vec::new();

    if n_ == 1 {
        // 1 has an empty factorization
        return factors;
    }

    let mut candidate: nat = 2;

    while candidate * candidate <= n_
        invariant
            n_ >= 1,
            candidate >= 2,
            is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) * n_ == n as nat,
            forall|i: int, j: int|
                0 <= i <= j < factors.len() ==> factors[i] <= factors[j],
            forall|x: nat| candidate > x && x >= 2 && n_ % x == 0 ==> !is_prime(x), // All prime factors less than candidate are already factored out
    {
        while n_ % candidate == 0
            invariant
                n_ >= 1,
                candidate >= 2,
                is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) * n_ == n as nat,
                forall|i: int, j: int|
                    0 <= i <= j < factors.len() ==> factors[i] <= factors[j],
                forall|x: nat| candidate > x && x >= 2 && n_ % x == 0 ==> !is_prime(x),
                candidate <= (n as nat),
        {
            if candidate > u8::MAX as nat {
                // Should not happen for n <= u8::MAX
                return Vec::new(); // Or panic, depending on error handling strategy
            }
            factors.push(candidate as u8);
            n_ = n_ / candidate;

            assert(is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) * n_ == n as nat);
            if factors.len() >= 2 {
                assert(factors[factors.len() as int - 2] <= factors[factors.len() as int - 1]);
            }
        }
        candidate = candidate + 1;
    }

    if n_ > 1 {
        if n_ > u8::MAX as nat {
            // Should not happen
            return Vec::new();
        }
        factors.push(n_ as u8);
    }

    proof {
        assert(is_prime_factorization(n as nat, factors@.map(|_idx, j: u8| j as nat))) by {
            // Prove the first condition: all factors are prime
            assert forall|i: int| 0 <= i < factors.len() implies #[trigger] is_prime(factors[i] as nat) by {
                let factor = factors[i] as nat;
                // If factor was added in the first loop (candidate), it must be prime
                // because we divide n_ by it until it's no longer divisible.
                // It's a fundamental property of the algorithm that candidate is prime when it's added.
                // If the candidate passed the outer loop condition candidate*candidate <= n_,
                // it implies that any smaller factor of current n_ must have been removed.
                // So if candidate divides n_, candidate must be prime.
                // This is a subtle point, let's prove it by contradiction.
                if n_ % factor == 0 && factor < candidate { // it must be candidate that causes the division
                    assert(false); // This contradicts the invariant: forall|x: nat| candidate > x && x >= 2 && n_ % x == 0 ==> !is_prime(x)
                }
                // The last factor (n_ > 1 after the loop) must be prime because
                // if it were composite, it would have a prime factor p <= sqrt(n_),
                // and p would have been factored out by the loop.
                if factors.len() > 0 && i == factors.len() as int - 1 && n_ > 1 {
                    let last_factor = n_ as nat;
                    if last_factor * last_factor >= (candidate -1) * (candidate -1) {
                        assert(is_prime(last_factor)); // This is true because if it were composite, it would have been factored earlier
                    }
                }
            };

            // Prove the second condition: product of factors equals n
            assert(is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) == n as nat) by {
                assert(is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) * n_ == n as nat) by (
                    // This is maintained by loop invariant
                );
                if n_ > 1 {
                    assert(factors.last() == Some(n_ as u8));
                    assert(is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) == (n as nat) / n_ * n_);
                    assert((n as nat) / n_ * n_ == (n as nat));
                } else {
                    assert(is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) == (n as nat));
                }
            };

            // Prove the third condition: factors are sorted
            assert forall|i: nat, j: nat|
                (1 < i <= j < factors.len()) ==> ( #[trigger] factors[i as int] <= #[trigger] factors[j as int]) by {
                if i > 0 && j > 0 {
                    assert(factors[i as int] >= factors[i as int - 1]);
                }
            };
        }
    }

    factors
}
// </vc-code>

} // verus!
fn main() { }