// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    4 <= n <= 1000 && 1 <= k <= 4 && k < n
}

spec fn factorial(n: int) -> int
    decreases n
{
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}

spec fn derangement(n: int) -> int
    decreases n
{
    if n <= 1 { 0 }
    else if n == 2 { 1 }
    else { (n - 1) * (derangement(n - 1) + derangement(n - 2)) }
}

spec fn binomial(n: int, k: int) -> int {
    if k > n { 0 }
    else if k == 0 || k == n { 1 }
    else { factorial(n) / (factorial(k) * factorial(n - k)) }
}

spec fn sum_binomial_derangement(n: int, k: int, i: int) -> int
    decreases n - k - i
{
    if i >= n - k { 0 }
    else { binomial(n, i) * derangement(n - i) + sum_binomial_derangement(n, k, i + 1) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed, as it was not needed for fixing the errors */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures result as int == factorial(n as int) - sum_binomial_derangement(n as int, k as int, 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Updated the cast to use `as int` first, then convert back to `i8`. */
{
    let n_i: i8 = n;
    let k_i: i8 = k;

    let mut sum_b_d: i8 = 0;
    let mut i: i8 = 0;

    while i < n_i - k_i
        invariant
            0 <= i as int,
            i as int <= n_i as int - k_i as int,
            sum_b_d as int == sum_binomial_derangement(n_i as int, k_i as int, 0) - sum_binomial_derangement(n_i as int, k_i as int, i as int),
        decreases (n_i - k_i) - i
    {
        proof {
            if i < n_i - k_i {
                assert(sum_binomial_derangement(n_i as int, k_i as int, i as int) == binomial(n_i as int, i as int) * derangement(n_i as int - i as int) + sum_binomial_derangement(n_i as int, k_i as int, i as int + 1));
            }
        }
        let ghost b_term = binomial(n_i as int, i as int);
        let ghost d_term = derangement(n_i as int - i as int);
        let b_d_term: i8 = (b_term * d_term) as int as i8; // Cast to int first then i8
        sum_b_d = sum_b_d + b_d_term;
        i = i + 1;
    }

    let ghost total_permutations_ghost = factorial(n_i as int);
    let total_permutations: i8 = total_permutations_ghost as int as i8; // Cast to int first then i8
    let result_int: i8 = total_permutations - sum_b_d;
    result_int
}
// </vc-code>


}

fn main() {}