use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
// Helper lemma to show that if a number has no divisors between 2 and itself, it's prime
proof fn no_divisors_implies_prime(n: u32)
    requires
        n > 1,
        forall|k: int| 2 <= k < n ==> (n as int % k) != 0,
    ensures
        is_prime_pred(n),
{
}

// Helper lemma showing that if k divides n and k > 1, then n/k < n
proof fn division_decreases(n: u32, k: u32)
    requires
        n > 1,
        k > 1,
        n as int % k as int == 0,
    ensures
        n / k < n,
{
}

// Helper lemma for establishing that factors exist
proof fn factor_bounds(n: u32, k: u32)
    requires
        n >= 2,
        k >= 2,
        n as int % k as int == 0,
    ensures
        k <= n,
        n / k >= 1,
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
    let mut largest: u32 = 1;
    let mut i: u32 = 2;
    
    // Check if n itself is prime
    let mut n_is_prime = true;
    let mut j: u32 = 2;
    while j < n
        invariant
            2 <= j <= n,
            n_is_prime <==> (forall|k: int| 2 <= k < j ==> (n as int % k) != 0),
    {
        if n % j == 0 {
            n_is_prime = false;
        }
        j = j + 1;
    }
    
    if n_is_prime {
        assert(forall|k: int| 2 <= k < n ==> (n as int % k) != 0);
        no_divisors_implies_prime(n);
        assert(is_prime_pred(n));
        return n;
    }
    
    // Find largest prime factor
    while i <= n
        invariant
            2 <= i <= n + 1,
            1 <= largest <= n,
            largest == 1 || (largest > 1 && is_prime_pred(largest)),
    {
        if i == n + 1 {
            break;
        }
        
        if n % i == 0 {
            // Check if i is prime
            let mut is_prime = true;
            let mut k: u32 = 2;
            
            while k < i
                invariant
                    2 <= k <= i,
                    is_prime <==> (forall|m: int| 2 <= m < k ==> (i as int % m) != 0),
            {
                if i % k == 0 {
                    is_prime = false;
                }
                k = k + 1;
            }
            
            if is_prime && i > 1 {
                assert(forall|m: int| 2 <= m < i ==> (i as int % m) != 0);
                no_divisors_implies_prime(i);
                assert(is_prime_pred(i));
                largest = i;
            }
        }
        
        i = i + 1;
    }
    
    largest
}
// </vc-code>

fn main() {}
}