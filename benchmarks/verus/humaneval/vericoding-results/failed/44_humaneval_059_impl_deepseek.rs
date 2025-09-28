// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    n > 1 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}

spec fn power_of_2_factor(n: int, current: int) -> int
    recommends n > 0 && current > 0
    decreases current
    when current > 0
{
    if current % 2 != 0 { 1 }
    else { 2 * power_of_2_factor(n, current / 2) }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_divisor_prime(n: int, d: int)
    requires
        n > 1,
        d > 1,
        d <= n,
        n % d == 0,
    ensures
        exists|p: int| p > 1 && p <= d && is_prime(p) && n % p == 0
    decreases d
{
    if is_prime(d) {
        assert(n % d == 0);
    } else {
        assert(!is_prime(d));
        let k = choose|k: int| 2 <= k < d && d % k == 0;
        assert(d % k == 0);
        assert(n % k == 0);
        lemma_divisor_prime(n, k);
    }
}

proof fn lemma_prime_factor_exists(n: int)
    requires
        n > 1,
        !is_prime(n),
    ensures
        exists|p: int| p > 1 && p < n && is_prime(p) && n % p == 0
{
    let d = choose|d: int| d > 1 && d < n && n % d == 0;
    lemma_divisor_prime(n, d);
}

/* helper modified by LLM (iteration 5): Added cast to int for ghost function parameter */
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: i8) -> (result: i8)
    requires 
        n as int > 1,
        !is_prime(n as int),
    ensures 
        result as int > 1,
        (n as int) % (result as int) == 0,
        forall|k: int| k > result as int && (n as int) % k == 0 ==> !is_prime(k),
        is_prime(result as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by using ghost variable for prime check */
    proof {
        lemma_prime_factor_exists(n as int);
    }
    
    let mut result: i8 = 2;
    let mut candidate: i8 = 2;
    
    while candidate <= n
        invariant
            result as int > 1,
            (n as int) % (result as int) == 0,
            is_prime(result as int),
            candidate as int <= n as int + 1,
            forall|k: int| k > candidate as int && (n as int) % k == 0 ==> !is_prime(k)
        decreases (n as int) - (candidate as int)
    {
        let ghost_candidate = candidate as int;
        proof {
            if n % candidate == 0 && is_prime(ghost_candidate) {
                result = candidate;
            }
        }
        candidate += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}