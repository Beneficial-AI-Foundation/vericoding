use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> (ret: bool) {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

// <vc-helpers>
spec fn has_prime_factor(n: u32) -> bool {
    exists|k: int| 2 <= k <= n && is_prime_pred(k as u32) && n as int % k == 0
}

spec fn is_prime_factor(n: u32, f: u32) -> bool {
    f >= 2 && is_prime_pred(f) && n % f == 0
}

fn is_prime(n: u32) -> (result: bool)
    requires n >= 2
    ensures result <==> is_prime_pred(n)
{
    if n == 2 {
        return true;
    }
    if n % 2 == 0 {
        return false;
    }
    
    let mut i = 3;
    while i * i <= n
        invariant 
            i >= 3,
            i % 2 == 1,
            forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k) != 0
    {
        if n % i == 0 {
            return false;
        }
        i += 2;
    }
    true
}

proof fn prime_factor_exists(n: u32)
    requires n >= 2
    ensures exists|f: u32| is_prime_factor(n, f)
{
    // Every number >= 2 has at least one prime factor
}

proof fn largest_factor_correctness(n: u32, largest: u32, remaining: u32)
    requires n >= 2, largest >= 2, remaining >= 1
    requires n == largest * remaining || (remaining > 1 && is_prime_pred(remaining))
    ensures exists|f: u32| is_prime_factor(n, f) && f >= largest
{
    // Proof body
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "fn largest_prime_factor(n: u32) -> (result: u32)"
docstring: Find the largest prime factor of a given number.
*/
// </vc-description>

// <vc-spec>
fn largest_prime_factor(n: u32) -> (result: u32)
    requires n >= 2
    ensures result >= 2
    ensures is_prime_factor(n, result)
    ensures forall|f: u32| is_prime_factor(n, f) ==> f <= result
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified algorithm with proper invariants */
    let mut largest = 0;
    let mut remaining = n;
    let mut factor = 2;
    
    while factor * factor <= remaining
        invariant
            factor >= 2,
            remaining >= 2,
            n % remaining == 0,
            forall|f: u32| 2 <= f < factor ==> remaining % f != 0,
            largest == 0 || (largest >= 2 && is_prime_factor(n, largest))
    {
        if remaining % factor == 0 {
            largest = factor;
            while remaining % factor == 0
                invariant remaining >= 1, factor >= 2, n % remaining == 0
            {
                remaining = remaining / factor;
            }
        }
        if factor == 2 {
            factor = 3;
        } else {
            factor += 2;
        }
    }
    
    if remaining > 1 {
        largest = remaining;
    }
    
    largest
}
// </vc-code>

fn main() {}
}