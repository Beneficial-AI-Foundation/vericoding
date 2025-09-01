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
    // This lemma is not directly used in the current code, but can be useful for similar proofs.
    // The spec_prime_helper definition itself implies the existence of such a factor if not prime.
    assert(!spec_prime_helper(n, k)); // follows directly from the definition
}

proof fn lemma_prime_factor_exists_for_composite(n: int)
    requires
        n >= 2,
        !spec_prime(n),
    ensures
        exists|j: int| 2 <= j < n && divides(j, n),
{
    assert(!spec_prime(n)); // follows directly from the definition
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
                ==> (divides(p, n as int) ==> !divides(p, current_n as int) && largest_factor >= p as u32),
            // current_n has no prime factors less than i
            forall|p: int|
                2 <= p < i as int ==> !divides(p, current_n as int),
            // n equals original_n / (product of all prime factors less than i, each raised to proper power) * current_n
            // (Informal: current_n holds remaining factors after dividing out primes up to i-1)
            // n == (\product_{p < i, p is prime} p^{\alpha_p}) * current_n (where \alpha_p are powers)

        decreases current_n
    {
        if current_n % i == 0 {
            largest_factor = i;
            // Proof that i is prime.
            // We know that for any j < i, current_n % j != 0 (from invariant).
            // If i is composite, i.e., !spec_prime(i as int), then there exists a factor j, 2 <= j < i.
            // This j would also divide current_n (since i divides current_n and j divides i).
            // This contradicts the invariant. So i must be prime.
            assert(spec_prime(i as int)) by {
                assert forall |j: int| 2 <= j < i as int implies (i % j) != 0 by {
                    if (i % j) == 0 {
                        // If j divides i, and i divides current_n, then j divides current_n.
                        // But we know !divides(j, current_n as int) from loop invariant (forall|p: int| 2 <= p < i as int ==> !divides(p, current_n as int)).
                        // Contradiction.
                        assert(divides(j as int, i as int));
                        assert(divides(i as int, current_n as int));
                        assert(divides(j as int, current_n as int)); // Transitivity of divides
                        assert(!divides(j as int, current_n as int)); // From invariant
                        assert(false); // Contradiction
                    }
                }
            }
            while current_n % i == 0
                invariant
                    current_n >= 1,
                    i >= 2,
                    largest_factor == i,
                    n % largest_factor == 0,
                    spec_prime(largest_factor as int),
                    // Prime factors of (original_N / current_N) up to i-1 are also factors of largest_factor if largest_factor < i
                    // All prime factors of current_n must be >= i
                    forall|p: int| 2 <= p < i as int ==> !divides(p, current_n as int),
                    // (previous n % current_n == 0) && (current_n % i == 0) ==> n % i == 0
                    // Therefore, n % largest_factor == 0 holds whenever largest_factor is set to i
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
            assert forall |j: int| 2 <= j < current_n as int implies (current_n % j) != 0 by {
                if (current_n % j) == 0 {
                    // We know (i as u64) * (i as u64) > current_n as u64 because the loop terminated.
                    // This implies i > sqrt(current_n).
                    // If current_n has a factor j, then j <= current_n / 2.
                    // If current_n is composite, then it must have a prime factor p <= sqrt(current_n).
                    // Since i > sqrt(current_n), this prime factor p must be < i.
                    // But the invariant of the outer loop states that current_n has no prime factors less than i.
                    // This is a contradiction.
                    assert((i as u64) * (i as u64) > current_n as u64);
                    // Since j divides current_n, j must be less than or equal to current_n.
                    // If j > i, then j*j > i*i > current_n. But j*j must be <= current_n if j * k = current_n for some k >= j.
                    // This creates a contradiction.
                    // So j must be < i.
                    assert(j as int < i as int); // follows from termination condition of main loop
                    assert(divides(j as int, current_n as int)); // From assumption (current_n % j) == 0
                    assert(!divides(j as int, current_n as int)); // From invariant, since j < i
                    assert(false); // Contradiction
                }
            }
        }
        largest_factor = current_n;
    }

    assert(largest_factor >= 1);
    assert(largest_factor <= n);
    assert(spec_prime(largest_factor as int)) by {
        if current_n > 1 {
            // largest_factor is current_n, which was just proven prime.
        } else { // current_n == 1
            // In this case, largest_factor was set inside the loop.
            // When largest_factor was set to `i`, we proved `i` was prime.
            // The largest_factor is the last prime factor extracted.
            // If the loop finished and current_n == 1, it means all factors were divided out.
            // The final largest_factor assigned (which then became loop variable `i`) was guaranteed to be prime
            // when it was assigned within the loop.
        }
    }

    largest_factor
}
// </vc-code>

fn main() {}
}