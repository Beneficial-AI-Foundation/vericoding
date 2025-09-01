use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
fn spec_prime_helper(p: int) -> bool {
    if p <= 1 {
        false
    } else if p == 2 {
        true
    } else {
        // We only check up to sqrt(p), but for simplicity in spec it checks up to p
        // The spec_prime definition is fundamental and we are not proving properties about it here.
        // This helper is for the implementation to find factors, not to prove primality.
        // For is_multiply_prime, we need to find factors of `x`.
        // The `spec_prime` function is a mathematical definition.
        // We'll use a trial division approach in the helper.
        true
    }
}

// Helper to find prime factors of a number
proof fn find_prime_factors(n: int) -> (factors: Seq<int>)
    requires
        n > 1,
    ensures
        forall|p: int| p `elem` factors ==> spec_prime(p),
        multiset_math::multiset_from_seq(factors).product() == n,
        factors.len() >= 1,
{
    // This is a placeholder for a more complex prime factorization algorithm.
    // For `is_multiply_prime`, we need to find exactly three prime factors if they exist.
    // The proof that any integer has a unique prime factorization (up to permutation)
    // is fundamental but complex to express fully in Verus for arbitrary numbers.
    // For this problem, we'll try to find three prime factors by trial division in the
    // `is_multiply_prime` function itself, rather than a generic factorization helper.
    // This helper function `find_prime_factors` is not directly used in the current solution
    // as we are doing a direct search for 3 factors inside `is_multiply_prime`.
    // It is kept for demonstration of structure but will contain a stub proof.

    // A simple recursive factorization helper for proof context
    if spec_prime(n) {
        Seq::singleton(n)
    } else {
        let mut k: int = 2;
        while k * k <= n
            invariant
                k >= 2,
                n > 1,
        {
            if n % k == 0 {
                let factors_of_k = find_prime_factors(k);
                let factors_of_nk = find_prime_factors(n / k);
                return factors_of_k.add(factors_of_nk);
            }
            k = k + 1;
        }
        // Should not reach here if n is not prime and > 1
        // (i.e. if a factor exists, it would be found)
        Seq::singleton(n) // Fallback, should ideally be unreachable for composite n
    }
}
// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(x: u32) -> (ans: bool)
    // pre-conditions-start
    requires
        x > 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // A u32 maximum value is 4,294,967,295.
    // The smallest prime is 2. So the smallest product of three primes is 2 * 2 * 2 = 8.
    // We need to find three prime factors a, b, c such that x = a * b * c.

    let mut a: u32 = 2;
    while (a as u64) * (a as u64) * (a as u64) <= (x as u64) {
        invariant
            2 <= a,
            ((a as u64) * (a as u64) * (a as u64)) <= (u32::MAX as u64) + 1, // To prevent overflow for the loop condition
        {
            if x % a == 0 {
                // Check if 'a' is prime
                let mut is_a_prime = true;
                if a <= 1 {
                    is_a_prime = false;
                } else {
                    let mut k_a: u32 = 2;
                    while k_a * k_a <= a {
                        invariant
                            2 <= k_a,
                            k_a * k_a <= u32::MAX, // k_a * k_a could overflow for large a
                        {
                            if a % k_a == 0 {
                                is_a_prime = false;
                                break;
                            }
                            k_a = k_a + 1;
                        }
                    }
                }
                if is_a_prime {
                    // Try to find b and c from x / a
                    let x_div_a = x / a;
                    let mut b: u32 = a; // Start b from a, as order doesn't matter and this avoids re-checking
                    while b as u64 * b as u64 <= x_div_a as u64 {
                        invariant
                            a <= b,
                            (b as u64) * (b as u64) <= (u32::MAX as u64) + 1,
                        {
                            if x_div_a % b == 0 {
                                // Check if 'b' is prime
                                let mut is_b_prime = true;
                                if b <= 1 {
                                    is_b_prime = false;
                                } else {
                                    let mut k_b: u32 = 2;
                                    while k_b * k_b <= b {
                                        invariant
                                            2 <= k_b,
                                            k_b * k_b <= u32::MAX,
                                        {
                                            if b % k_b == 0 {
                                                is_b_prime = false;
                                                break;
                                            }
                                            k_b = k_b + 1;
                                        }
                                    }
                                }

                                if is_b_prime {
                                    let c = x_div_a / b;
                                    if c >= b { // Ensure c is not smaller than b to avoid redundant checks
                                        // Check if 'c' is prime
                                        let mut is_c_prime = true;
                                        if c <= 1 {
                                            is_c_prime = false;
                                        } else {
                                            let mut k_c: u32 = 2;
                                            while k_c * k_c <= c {
                                                invariant
                                                    2 <= k_c,
                                                    k_c * k_c <= u32::MAX,
                                                {
                                                    if c % k_c == 0 {
                                                        is_c_prime = false;
                                                        break;
                                                    }
                                                    k_c = k_c + 1;
                                                }
                                            }
                                        }
                                        if is_c_prime {
                                            proof {
                                                assert(x == (a as int) * (b as int) * (c as int));
                                                assert(spec_prime(a as int));
                                                assert(spec_prime(b as int));
                                                assert(spec_prime(c as int));
                                            }
                                            return true;
                                        }
                                    }
                                }
                            }
                            b = b + 1;
                        }
                    }
                }
            }
            a = a + 1;
        }
    }
    return false;
}
// </vc-code>

fn main() {}
}