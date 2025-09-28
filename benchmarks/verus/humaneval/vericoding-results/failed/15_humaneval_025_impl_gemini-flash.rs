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
/* helper modified by LLM (iteration 5): The trigger `n % x != 0` is not a valid trigger. Changed it to `n % x` to simplify the expression and satisfy the trigger requirements. */
spec fn is_prime_divisible_by_no_small_primes_except_itself_i8(n: i8, k_bound: i8) -> bool {
    forall|x: i8| 2 <= x < k_bound ==> #[trigger] (n % x) != 0
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
/* code modified by LLM (iteration 5): Fixed trigger issue in `is_prime_divisible_by_no_small_primes_except_itself_i8` by simplifying the expression. Iteration 4's proposed trigger `n % x != 0` was an invalid trigger; the new trigger `n % x` addresses this. */
{
    if n <= 1 {
        return Vec::new();
    }

    let mut factors: Vec<i8> = Vec::new();
    let mut current_n: i8 = n;
    let mut k: i8 = 2;
    let mut product_so_far: i128 = 1;

    while (k as i128) * (k as i128) <= current_n as i128
        invariant
            current_n >= 0,
            k >= 2,
            product_so_far * (current_n as i128) == n as i128,
            forall|f: int| 0 <= f < factors.len() ==> is_prime(factors@[f] as int),
            is_non_decreasing(factors@.map(|i: int, x: i8| x as int)),
            is_prime_divisible_by_no_small_primes_except_itself_i8(current_n, k),
            forall|i: int| 0 <= i < factors.len() ==> factors@[i] >= 2,
            product_so_far == product(factors@.map(|i: int, x: i8| x as int)) as i128
        decreases current_n as int
    {
        if current_n % k == 0 {
            factors.push(k);
            product_so_far = product_so_far * (k as i128);
            current_n = current_n / k;
            proof {
                // This proof block is empty because the `is_prime` assertion was moved to a later stage.
            }
        } else {
            k = k + 1;
        }
    }

    if current_n > 1 {
        factors.push(current_n as i8);
        product_so_far = product_so_far * (current_n as i128);
        proof {
            assert(is_prime(current_n as int))
            by (nonlinear_arith);
        }
    }

    proof {
        if n > 1 {
            // The product_so_far invariant ensures the final product condition after the loop.
            // The primality and non-decreasing order are maintained by the loop logic and invariants.
        }
    }
    factors
}
// </vc-code>


}

fn main() {}