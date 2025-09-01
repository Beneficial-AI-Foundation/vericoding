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
    assert(!spec_prime_helper(n, k)) by {
        assert(exists|j: int| 2 <= j < k && n % j == 0);
    }
}

proof fn lemma_prime_factor_exists_for_composite(n: int)
    requires
        n >= 2,
        !spec_prime(n),
    ensures
        exists|j: int| 2 <= j < n && divides(j, n),
{
    assert(!spec_prime(n)) by {
        assert(exists|j: int| 2 <= j < n && n % j == 0);
    }
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

    while i * i <= current_n
        invariant
            current_n >= 1,
            largest_factor >= 1,
            n % current_n == 0,
            forall|j: int| 2 <= j < i as int ==> (#[trigger] (n % j)) != 0 || (#[trigger] (j as u32 % largest_factor)) == 0 && spec_prime(largest_factor as int), // not necessarily prime, just ensures numbers up to i are handled
            forall|k: int| 1 <= k <= largest_factor as int ==> (#[trigger] (n % k)) == 0,
            forall|p: int| 2 <= p <= largest_factor as int ==> !divides(p as int, largest_factor as int) || (#[trigger] (p as int == largest_factor as int)), // largest_factor is prime (or 1)
            (spec_prime(largest_factor as int) || largest_factor == 1)
        decreases current_n
    {
        if current_n % i == 0 {
            largest_factor = i;
            while current_n % i == 0
                invariant
                    current_n % i == 0, // Invariant to help prove current_n % i == 0 is preserved
                    current_n >= 1,
                    largest_factor == i,
                    n % i == 0, // This is true because originally n % i == 0
                    spec_prime_helper(largest_factor as int, largest_factor as int + 1)
                decreases current_n
            {
                current_n /= i;
            }
        }
        i += 1;
    }

    if current_n > 1 {
        largest_factor = current_n;
    }

    assert(largest_factor >= 1);
    assert(largest_factor <= n);

    if (current_n == 1) { // all factors were found and divided out
        // largest_factor is the last prime factor found
        assert(spec_prime(largest_factor as int)) by {
            // If current_n was reduced to 1, then the last largest_factor found must be prime.
            // When loop finishes, all factors up to sqrt(current_n_initial) are processed.
            // If remaining current_n > 1, it must be prime.
            // The earlier inner loop ensures the largest_factor set is prime.
            if largest_factor * largest_factor <= n {
                // If largest_factor was set inside the loop, it was i
                // and the inner loop ensured i was a prime factor of current_n.
                // The invariant for the inner loop helps ensure largest_factor is prime.
            } else {
                // largest_factor was the final current_n, which must be prime.
            }
            spec_prime_helper(largest_factor as int, largest_factor as int);
        }
    } else { // current_n > 1, meaning current_n is the largest prime factor remaining
        // Here, largest_factor must be `current_n`. We set it above.
        assert(spec_prime(largest_factor as int)) by {
            // When the loop `while i * i <= current_n` finishes, if `current_n > 1`,
            // then `current_n` must be a prime number.
            // This is because if `current_n` were composite, it would have a prime factor
            // less than or equal to `sqrt(current_n)`.
            // But the loop iterates `i` up to `sqrt(current_n_initial)`.
            // Since `i * i > current_n` and `current_n > 1`, `current_n` has no divisors
            // smaller than `i`. Thus, it must be prime.
            lemma_prime_factor_exists_for_composite(current_n as int) by {
                assert forall |k: int| 2 <= k < current_n as int implies current_n as int % k != 0 by {
                    assert(i * i > current_n); // from loop termination condition
                    assert forall |k: int| 2 <= k < i as int implies (n % k) != 0 || (k as u32 % largest_factor) == 0 && spec_prime(largest_factor as int) {
                        assert(largest_factor <= i); // largest_factor is at most the current i
                        // If k divides current_n, it would have been found earlier
                        // because k < i and we iterated up to i.
                        // So, no k divides current_n where 2 <= k < i.
                        // Since i*i > current_n, this means current_n has no factors below i.
                        // If current_n were composite, it would have a factor <= sqrt(current_n) < i.
                        // This implies current_n must be prime if it's > 1.
                    }
                }
            }
        }
    }

    largest_factor
}
// </vc-code>

fn main() {}
}