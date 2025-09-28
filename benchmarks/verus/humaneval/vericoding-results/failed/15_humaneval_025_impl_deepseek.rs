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
/* helper modified by LLM (iteration 5): Fixed type usage - use int instead of nat in proof helpers and ensure proper type conversions */
proof fn find_smallest_prime_factor(n: int, start: int) -> (factor: int)
    requires
        n >= 2,
        start >= 2,
        exists|k: int| k >= start && is_prime(k) && n % k == 0
    ensures
        factor >= start,
        is_prime(factor),
        n % factor == 0,
        forall|k: int| start <= k < factor ==> !(is_prime(k) && n % k == 0)
    decreases n - start
{
    if is_prime(start) && n % start == 0 {
        start
    } else {
        find_smallest_prime_factor(n, start + 1)
    }
}

proof fn prime_factorization_exists(n: int)
    requires
        n >= 2
    ensures
        exists|factors: Seq<int>| 
            product(factors) == n
            && forall|i: int| 0 <= i < factors.len() ==> is_prime(factors[i])
            && is_non_decreasing(factors)
    decreases n
{
    if is_prime(n) {
        assert(is_prime(n));
    } else {
        proof {
            let smallest_factor = find_smallest_prime_factor(n, 2);
            let remainder = n / smallest_factor;
            prime_factorization_exists(remainder);
        }
    }
}
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
/* code modified by LLM (iteration 5): Fixed variable types - use int instead of nat */
{
    if n <= 1 {
        Vec::new()
    } else {
        let mut factors = Vec::new();
        let mut remaining: int = n as int;
        let mut current_factor: int = 2;
        
        proof {
            prime_factorization_exists(remaining);
        }
        
        while remaining > 1
            invariant
                remaining >= 1,
                product(factors@.map(|i: int, x: i8| x as int)) * remaining == n as int,
                forall|i: int| 0 <= i < factors.len() ==> is_prime(#[trigger] factors@[i] as int),
                is_non_decreasing(factors@.map(|i: int, x: i8| x as int)),
                forall|i: int| 0 <= i < factors.len() ==> #[trigger] factors@[i] >= 2,
                current_factor >= 2
            decreases remaining
        {
            if remaining % current_factor == 0 {
                proof {
                    let smallest_factor = find_smallest_prime_factor(remaining, current_factor);
                }
                let next_factor = current_factor;
                factors.push(next_factor as i8);
                remaining = remaining / next_factor;
                current_factor = next_factor;
            } else {
                current_factor += 1;
            }
        }
        
        factors
    }
}
// </vc-code>


}

fn main() {}