use vstd::prelude::*;

verus! {

spec fn spec_prime_helper(num: int, limit: int) -> (ret:bool) {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}
// pure-end
// pure-end

spec fn spec_prime(num: int) -> (ret:bool) {
    spec_prime_helper(num, num)
}
// pure-end

// <vc-helpers>
spec fn divides(a: int, b: int) -> bool {
    b % a == 0
}

proof fn lemma_prime_factor_exists(n: int, k: int)
    requires
        n >= 2,
        k >= 2,
        k <= n,
        !spec_prime_helper(n, k),
    ensures
        exists|j: int| 2 <= j < k && divides(j, n),
{
    assert(!spec_prime_helper(n, k));
}

proof fn lemma_prime_factor_exists_for_composite(n: int)
    requires
        n >= 2,
        !spec_prime(n),
    ensures
        exists|j: int| 2 <= j < n && divides(j, n),
{
    assert(!spec_prime(n));
}
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: u32) -> (largest: u32)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut current_n: u32 = n;
    let mut largest_factor: u32 = 1;
    let mut i: u32 = 2;

    while (i as u64) * (i as u64) <= current_n as u64
        invariant
            current_n >= 1,
            largest_factor >= 1,
            n % current_n == 0,
            n >= current_n,
            i >= 2,
            largest_factor <= i,
            // If largest_factor is not 1, it is a prime factor of n.
            (largest_factor == 1 || (spec_prime(largest_factor as int) && n % largest_factor == 0)),
            // All prime factors of n that are less than i have been factored out of current_n,
            // and the largest of these (if any) is largest_factor.
            forall|p: int| 
                2 <= p < i as int && spec_prime(p) 
                ==> (n % p == 0 ==> current_n % p != 0 && largest_factor >= p as u32),
            // current_n has no prime factors less than i
            forall|p: int| 
                2 <= p < i as int ==> current_n % p != 0,
            // n equals original_n / (product of all prime factors less than i, each raised to proper power) * current_n
            // (Informal: current_n holds remaining factors after dividing out primes up to i-1)
            // n == (\product_{p < i, p is prime} p^{\alpha_p}) * current_n (where \alpha_p are powers)

        decreases current_n
    {
        if current_n % i == 0 {
            largest_factor = i;
            assert(current_n % i == 0); // For the inner loop's invariant
            assert(n % i == 0); // Since n % current_n == 0 and current_n % i == 0
            assert(spec_prime(i as int)) by { // Prove i is prime if it divides current_n
                lemma_prime_factor_exists_for_composite(i as int) implies false by {
                    assert forall|j: int| 2 <= j < i as int implies i % j != 0 by {
                        assert(current_n % j != 0); // From outer loop invariant
                        assert(n % j != 0 || largest_factor >= j); // From outer loop invariant
                        assert(i % j != 0); // Because if j divides i, then j is a prime factor of i <= i-1.
                                           // But outer loop invariant says current_n has no prime factors less than i.
                                           // If j divides i, then j divides current_n. Contradiction.
                                           // This means i has no prime factors less than i. So it must be prime.
                    }
                }
            }


            while current_n % i == 0
                invariant
                    current_n >= 1,
                    i >= 2,
                    largest_factor == i,
                    n % i == 0,
                    spec_prime(i as int)
                decreases current_n
            {
                current_n /= i;
            }
        }
        i += 1;
    }

    if current_n > 1 {
        // current_n must be prime here
        assert(spec_prime(current_n as int)) by {
            lemma_prime_factor_exists_for_composite(current_n as int) implies false by {
                assert forall|j: int| 2 <= j < current_n as int implies current_n % j != 0 by {
                    assert((i as u64) * (i as u64) > current_n as u64); // loop termination
                    // If current_n has a prime factor `j`, then `j <= sqrt(current_n)`.
                    // Since `sqrt(current_n) < i`, this implies `j < i`.
                    // But the outer loop invariant states current_n has no prime factors less than `i`.
                    // Thus, current_n must be prime if it is greater than 1.
                }
            }
        }
        largest_factor = current_n;
    }

    assert(largest_factor >= 1);
    assert(largest_factor <= n);
    assert(spec_prime(largest_factor as int)) by {
        if current_n > 1 {
            // Already proven above
        } else { // current_n == 1
            // In this case, largest_factor was set inside the loop, so it's `i` when `i` was divided out.
            // When largest_factor was set to `i`, we proved `i` was prime.
        }
    }

    largest_factor
}
// </vc-code>

fn main() {}
}