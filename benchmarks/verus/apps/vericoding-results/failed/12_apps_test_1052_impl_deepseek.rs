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
/* helper modified by LLM (iteration 5): Fixed compilation errors and ensured proper result handling */
fn compute_factorial(n: u64) -> (result: u64)
    requires n <= 20
    ensures result as int == factorial(n as int)
    decreases n
{
    if n <= 1 { 1 } else { n * compute_factorial(n - 1) }
}

fn compute_derangement(n: u64) -> (result: u64)
    requires n <= 20
    ensures result as int == derangement(n as int)
    decreases n
{
    if n <= 1 { 0 }
    else if n == 2 { 1 }
    else { (n - 1) * (compute_derangement(n - 1) + compute_derangement(n - 2)) }
}

fn compute_binomial(n: u64, k: u64) -> (result: u64)
    requires n <= 20 && k <= n
    ensures result as int == binomial(n as int, k as int)
{
    if k > n { 0 }
    else if k == 0 || k == n { 1 }
    else { compute_factorial(n) / (compute_factorial(k) * compute_factorial(n - k)) }
}

fn compute_sum_binomial_derangement(n: u64, k: u64, i: u64) -> (result: u64)
    requires n <= 20 && k <= n && i <= n - k
    ensures result as int == sum_binomial_derangement(n as int, k as int, i as int)
    decreases (n - k - i) as int
{
    if i >= n - k { 0 }
    else { compute_binomial(n, i) * compute_derangement(n - i) + compute_sum_binomial_derangement(n, k, i + 1) }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures result as int == factorial(n as int) - sum_binomial_derangement(n as int, k as int, 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed result variable declaration and bounds checking */
    let n_int = n as u64;
    let k_int = k as u64;
    
    proof {
        assert(n_int <= 20);
        assert(k_int <= n_int);
    }
    
    let fact_result = compute_factorial(n_int);
    let sum_result = compute_sum_binomial_derangement(n_int, k_int, 0);
    
    proof {
        assert(fact_result as int == factorial(n as int));
        assert(sum_result as int == sum_binomial_derangement(n as int, k as int, 0));
    }
    
    let result_val = fact_result - sum_result;
    proof {
        assert(result_val as int == factorial(n as int) - sum_binomial_derangement(n as int, k as int, 0));
    }
    result_val as i8
}
// </vc-code>


}

fn main() {}