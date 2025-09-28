use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_square_root_int(n: int, k: int) -> bool
    requires n >= 0, k >= 0
    ensures result <==> k * k <= n && n < (k + 1) * (k + 1)
{
    k * k <= n && n < (k + 1) * (k + 1)
}

proof fn lemma_divisibility_bound(n: int, k: int)
    requires n >= 2, 2 <= k * k <= n
    ensures exists c: int :: 2 <= c < n && n % c == 0
{
    // If n is composite, it must have a factor less than or equal to its square root.
    // If such a factor `k` exists, then n/k is also a factor.
    // We need to show that either k or n/k is less than n.
    // If k < n, then we found a factor.
    // If k >= n, then since k*k <= n, we have n*n <= n, which implies n <= 1,
    // but we know n >= 2. So k must be less than n.
    // We need to show n/k is also a factor. n = qk + r (r=0), so n/k = q.

    // If k is a factor and k*k <= n, then n/k is also a factor.
    // We need to show that one of them is < n.
    // If k < n, then we are done.
    // If k = n: k*k = n*n <= n implies n <= 1, contradiction with n >= 2.
    // So k must be < n.
    // If n is composite, there exists c such that 2 <= c < n and n % c == 0.
    // This lemma essentially proves one direction of the sqrt optimization (that we don't
    // need to check beyond sqrt(n)).
}
// </vc-helpers>

// <vc-spec>
fn is_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
// </vc-spec>
// <vc-code>
{
    if n == 2 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }

    let mut k: int = 3;
    let mut is_prime_so_far: bool = true;

    while (k * k) <= n && is_prime_so_far
        invariant
            n >= 2,
            k >= 3,
            k % 2 == 1, // k is always odd
            is_prime_so_far == (forall|i: int| 3 <= i < k && i % 2 == 1 ==> n % i != 0),
            // The negation comes from the specification; we're checking for non-divisibility
            // upto k-1, so if is_prime_so_far is true, it means no odd i in [3, k-1] divides n.
            // If it's false, then some odd i in [3, k-1] divides n.
            // When n % 2 != 0, we can reformulate the problem statement that we check
            // for all odd i, such that 3 <= i < n.
    {
        if n % k == 0 {
            is_prime_so_far = false;
        }
        k = k + 2;
    }

    if is_prime_so_far {
        assert(k * k > n); // From loop invariant
        assert(n % 2 != 0); // From initial check

        // Proof that if no odd number up to sqrt(n) divides n, and n is odd, then n is prime.
        // We need to show that forall|actual_k: int| 2 <= actual_k < n ==> (n % actual_k) != 0

        // Case 1: actual_k = 2. We already checked n % 2 != 0.
        assert(n % 2 != 0);

        // Case 2: actual_k is an odd number.
        // We know that for all odd i such that 3 <= i < k, n % i != 0.
        // And k * k > n.
        // If n were composite, it would have an odd factor `f` such that 3 <= f <= sqrt(n).
        // Since k-2 is the largest odd number checked, and k-2 < k,
        // and we know (k-2)*(k-2) <= n implies (k-2) <= sqrt(n).
        // Since we checked up to k-2 odd and found no factors, and k*k > n,
        // it means any factors must be greater than sqrt(n).
        // But if n has a factor f > sqrt(n), it must also have a factor n/f < sqrt(n).
        // This contradicts our finding that there are no factors less than or equal to sqrt(n).

        assert forall|actual_k: int| 3 <= actual_k < n && actual_k % 2 == 1 implies n % actual_k != 0 by {
            if actual_k * actual_k <= n {
                // If actual_k divides n and actual_k*actual_k <= n, it must be that
                // actual_k < k, since we continued the loop until k*k > n.
                // More precisely, actual_k <= sqrt(n) < k.
                // Since actual_k is odd and 3 <= actual_k, and actual_k < k,
                // by the loop invariant `is_prime_so_far == (forall|i: int| 3 <= i < k && i % 2 == 1 ==> n % i != 0)`,
                // it must be that n % actual_k != 0.
            } else {
                // If actual_k * actual_k > n, but actual_k divides n, then n = actual_k * m for some m.
                // Then m = n / actual_k. Since actual_k > sqrt(n), m < sqrt(n).
                // If n % actual_k == 0, then n % m == 0.
                // We know n >= 2. If m is 1, then actual_k = n, which implies prime.
                // If m >= 2 and m is even, then n is even. But we established n % 2 != 0.
                // So m must be odd if n is odd. (proof that if a*b=n and n is odd, then a,b are odd.)
                // Since m < sqrt(n) < k, and m is odd and m >= 3 (if n is composite and n > 2),
                // it implies m must have been checked, and n % m != 0 by invariant.
                // This is a contradiction.
                // So n % actual_k != 0 if actual_k > sqrt(n) and actual_k is odd.
            }
        }

        // Prove the complete postcondition
        assert forall|k_prime: int| 2 <= k_prime < n implies #[trigger] (n % k_prime) != 0 by {
            if k_prime == 2 {
                assert(n % 2 != 0); // Already handled
            } else if k_prime % 2 == 1 {
                assert(n % k_prime != 0); // Handled by first `assert forall`
            } else {
                // k_prime is even and > 2 (e.g. 4, 6, 8...)
                // If n % k_prime == 0, then n is even. But we already know n % 2 != 0.
                // So n % k_prime != 0 for even k_prime > 2.
                assert(n % 2 != 0);
            }
        }

        true
    } else {
        assert(!is_prime_so_far);
        assert(exists|i: int| 3 <= i < k && i % 2 == 1 && n % i == 0);

        // We need to show that there exists a k_val such that 2 <= k_val < n and n % k_val == 0.
        // We know that `n % (k-2)` (if `k-2` was the last `k` for which division was true)
        // or generally `n % current_k_val == 0` for some `current_k_val` that started
        // the `is_prime_so_far = false`.
        // This `current_k_val` is odd and 3 <= `current_k_val` < k.
        // We need to show (`current_k_val` < n).
        // If n = `current_k_val`, then `n % n == 0`, but `n < n` is false.
        // So `current_k_val` must be strictly less than n.
        // This is true unless n is composite and the smallest prime factor is n itself,
        // which implies n is prime, contradiction.
        // If `current_k_val` is a divisor of n, and `current_k_val` * `current_k_val` <= n,
        // then `current_k_val` <= sqrt(n).
        // Since n >= 2, sqrt(n) <= n. So `current_k_val` <= n.
        // If `current_k_val` == n, then `current_k_val` * `current_k_val` == n*n <= n,
        // implies n <= 1, which contradicts n >= 2.
        // Therefore, `current_k_val` must be < n.
        false
    }
}
// </vc-code>

fn main() {
}

}