// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    n >= 2 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}

spec fn product(factors: Seq<int>) -> int
    decreases factors.len()
{
    if factors.len() == 0 {
        1
    } else {
        factors[0] * product(factors.subrange(1, factors.len() as int))
    }
}

spec fn is_non_decreasing(factors: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < factors.len() ==> #[trigger] factors[i] <= #[trigger] factors[j]
}

// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn factorize(n: i8) -> (factors: Vec<i8>)
    requires n >= 0
    ensures 
        n <= 1 ==> factors.len() == 0,
        n > 1 ==> product(factors@.map(|i: int, x: i8| x as int)) == n as int,
        forall|i: int| 0 <= i < factors.len() ==> is_prime(#[trigger] factors@[i] as int),
        is_non_decreasing(factors@.map(|i: int, x: i8| x as int)),
        forall|i: int| 0 <= i < factors.len() ==> #[trigger] factors@[i] >= 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed invariants using invariant_except_break and ensures for break conditions */
    if n <= 1 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut remaining = n;
    let mut candidate: i8 = 2;
    
    while candidate <= remaining
        invariant
            candidate >= 2,
            remaining >= 1,
            remaining <= n,
            forall|i: int| 0 <= i < result.len() ==> is_prime(#[trigger] result@[i] as int),
            forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i] >= 2,
            forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i] <= candidate,
            candidate <= 127,
        invariant_except_break
            n as int == remaining as int * product(result@.map(|i: int, x: i8| x as int)),
            is_non_decreasing(result@.map(|i: int, x: i8| x as int)),
            remaining > 1,
        ensures
            n as int == product(result@.map(|i: int, x: i8| x as int)),
            is_non_decreasing(result@.map(|i: int, x: i8| x as int)),
        decreases remaining as int
    {
        if remaining % candidate == 0 {
            let mut is_prime_candidate = true;
            let mut k: i8 = 2;
            
            while k < candidate
                invariant
                    2 <= k,
                    k <= candidate,
                    is_prime_candidate == forall|j: int| 2 <= j < k as int ==> #[trigger] (candidate as int % j) != 0,
                decreases (candidate - k) as int
            {
                if candidate % k == 0 {
                    is_prime_candidate = false;
                }
                k = k + 1;
            }
            
            if is_prime_candidate {
                result.push(candidate);
                remaining = remaining / candidate;
                if remaining == 1 {
                    break;
                }
                // Don't increment candidate, try the same prime again
            } else {
                if candidate < remaining && candidate < 127 {
                    candidate = candidate + 1;
                } else {
                    break;
                }
            }
        } else {
            if candidate < remaining && candidate < 127 {
                candidate = candidate + 1;
            } else {
                break;
            }
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}