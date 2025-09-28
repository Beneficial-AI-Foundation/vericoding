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
/* helper modified by LLM (iteration 5): unfolds sum_binomial_derangement for one step */
proof fn sum_binomial_derangement_unfold(n: int, k: int, i: int)
    requires
        valid_input(n, k),
        0 <= i,
        i < n - k,
    ensures
        sum_binomial_derangement(n, k, i) == binomial(n, i) * derangement(n - i) + sum_binomial_derangement(n, k, i + 1),
    decreases n - k - i
{
    reveal(sum_binomial_derangement);
}

/* helper modified by LLM (iteration 5): sum_binomial_derangement equals 0 when i >= n - k */
proof fn sum_binomial_derangement_zero(n: int, k: int, i: int)
    requires
        valid_input(n, k),
        i >= n - k,
    ensures
        sum_binomial_derangement(n, k, i) == 0,
{
    reveal(sum_binomial_derangement);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures result as int == factorial(n as int) - sum_binomial_derangement(n as int, k as int, 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute sum via ghost loop and return factorial - sum (convert spec int to i8 via int_to_i8) */
    let result: i8;
    let ghost N: int = n as int;
    let ghost K: int = k as int;
    let ghost limit: int = N - K;
    let ghost mut i: int = 0 as int;
    let ghost mut acc: int = 0 as int;
    while i < limit
        invariant
            0 as int <= i && i <= limit,
            sum_binomial_derangement(N, K, i) + acc == sum_binomial_derangement(N, K, 0),
        decreases limit - i
    {
        proof {
            sum_binomial_derangement_unfold(N, K, i);
        }
        acc = acc + binomial(N, i) * derangement(N - i);
        i = i + (1 as int);
    }
    proof {
        sum_binomial_derangement_zero(N, K, limit);
        assert(sum_binomial_derangement(N, K, limit) == 0);
        assert(acc == sum_binomial_derangement(N, K, 0));
    }
    let ghost res_int: int = factorial(N) - acc;
    result = int_to_i8(res_int);
    result
}
// </vc-code>


}

fn main() {}