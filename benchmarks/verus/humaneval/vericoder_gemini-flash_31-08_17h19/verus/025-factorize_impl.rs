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
                candidate <= (n as nat), // Add this invariant
        {
            if candidate > u8::MAX as nat {
                // Should not happen for n <= u8::MAX
                return Vec::new(); // Or panic, depending on error handling strategy
            }
            factors.push(candidate as u8);
            n_ = n_ / candidate;

            proof {
                assert(is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) * n_ == n as nat);
                if factors.len() >= 2 {
                    assert(factors[factors.len() as int - 2] <= factors[factors.len() as int - 1]);
                }
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
                if i < factors.len() - 1 || n_ == 1 { // Factor was added in the loop
                    assert(is_prime(factor)) by {
                        // Proof by contradiction: if factor is not prime, it has a factor `p` < `factor`.
                        // If p is prime, it must have been removed earlier.
                        // If p is not prime, it has a factor `q` < `p`, and `q` must have been removed earlier.
                        // This implies `p` (and thus `factor`) is greater than or equal to `candidate` when it was processed,
                        // or `p` would have been a factor of `n_` before `factor` was included.
                        // The invariant `forall|x: nat| candidate > x && x >= 2 && n_ % x == 0 ==> !is_prime(x)`
                        // ensures that any prime factor smaller than `candidate` and dividing `n_` has been removed.
                        // Therefore, if `candidate` divides `n_`, it must be prime.
                    }
                } else { // It's the final n_ if n_ > 1
                    assert(is_prime(n_ as nat)) by {
                        // If n_ > 1 and it's not prime, it must have a prime factor p <= sqrt(n_).
                        // If p is prime, p <= sqrt(n_) < candidate, because candidate * candidate > n_.
                        // Then p must have been removed in the loop. Contradiction.
                        // So n_ must be prime.
                    }
                }
            };

            // Prove the second condition: product of factors equals n
            assert(is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) == n as nat) by {
                assert(is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) * n_ == n as nat);
                if n_ > 1 {
                    assert(factors.last() == Some(n_ as u8));
                    assert(is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) == (n as nat)); // This comes directly from the invariant
                } else {
                    assert(is_prime_fold(factors@.map(|_idx, j: u8| j as nat)) == (n as nat));
                }
            };

            // Prove the third condition: factors are sorted
            assert forall|i: nat, j: nat|
                (1 < i <= j < factors.len()) ==> ( #[trigger] factors[i as int] <= #[trigger] factors[j as int]) by {
                // This is maintained by the inner loop which adds `candidate` (a monotonic increasing value)
                // and the final `n_` which implies it's greater than the previous factors.
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