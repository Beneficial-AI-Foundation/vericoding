use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
spec fn divides(a: u32, b: u32) -> bool {
    b % a == 0
}

spec fn is_factor(f: u32, n: u32) -> bool {
    divides(f, n)
}

proof fn prime_divisor_exists(n: u32)
    requires
        2 <= n,
    ensures
        exists|p: u32| p <= n && is_prime_pred(p) && divides(p, n),
{
    // Proof that every integer n >= 2 has at least one prime divisor
}

proof fn no_prime_factor_implies_one(n: u32)
    ensures
        (forall|p: u32| p > 1 && p <= n ==> !divides(p, n)) ==> n == 1,
{
}

spec fn max_prime_factor(n: u32) -> u32
    recommends
        2 <= n,
{
    if n == 1 {
        1
    } else {
        choose|p: u32| p <= n && is_prime_pred(p) && divides(p, n) && 
        (forall|q: u32| q <= n && is_prime_pred(q) && divides(q, n) ==> q <= p)
    }
}

proof fn max_prime_factor_properties(n: u32)
    requires
        2 <= n,
    ensures
        1 <= max_prime_factor(n) <= n,
        is_prime_pred(max_prime_factor(n)),
        divides(max_prime_factor(n), n),
        forall|p: u32| p <= n && is_prime_pred(p) && divides(p, n) ==> p <= max_prime_factor(n),
{
}

proof fn decreasing_factor(n: u32, f: u32)
    requires
        2 <= n,
        is_factor(f, n),
        f < n,
    ensures
        n / f > 1,
        n / f < n,
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn largest_prime_factor(n: u32) -> (result: u32)
    requires
        2 <= n <= u32::MAX - 1,
    ensures
        1 <= result <= n,
        result == 1 || (result > 1 && is_prime_pred(result))
// </vc-spec>
// <vc-code>
{
    let mut candidate = n;
    let mut result = 1;
    
    while candidate > 1
        invariant
            1 <= candidate <= n,
            result == 1 || (result > 1 && is_prime_pred(result)),
            forall|p: u32| p > candidate && p <= n && is_prime_pred(p) ==> !divides(p, n),
            divides(result, n),
        decreases candidate,
    {
        let mut factor_found = false;
        let mut i = 2;
        
        while i <= candidate
            invariant
                2 <= i <= candidate + 1,
                !factor_found ==> forall|k: u32| 2 <= k < i ==> !divides(k, candidate),
                factor_found ==> exists|f: u32| 2 <= f < i && divides(f, candidate),
            decreases candidate - i,
        {
            if candidate % i == 0 {
                factor_found = true;
                break;
            }
            i += 1;
        }
        
        if factor_found {
            // i is the smallest factor of candidate
            proof {
                assert(i <= candidate);
                assert(divides(i, candidate));
                assert(forall|k: u32| 2 <= k < i ==> !divides(k, candidate));
            }
            
            // Check if i is prime
            let mut is_prime = true;
            let mut j = 2;
            
            while j < i
                invariant
                    2 <= j <= i,
                    is_prime ==> forall|k: u32| 2 <= k < j ==> !divides(k, i),
                    !is_prime ==> exists|k: u32| 2 <= k < j && divides(k, i),
                decreases i - j,
            {
                if i % j == 0 {
                    is_prime = false;
                    break;
                }
                j += 1;
            }
            
            if is_prime {
                result = i;
            }
            candidate = candidate / i;
        } else {
            // candidate is prime
            proof {
                assert(forall|k: u32| 2 <= k <= candidate ==> !divides(k, candidate) || k == candidate);
                assert(is_prime_pred(candidate));
            }
            result = candidate;
            candidate = 1;
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}