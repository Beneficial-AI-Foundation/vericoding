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
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing fn keyword and adding proof blocks */
proof fn factorial_pos(n: int)
    requires n >= 0
    ensures factorial(n) > 0
    decreases n
{
    if n <= 1 {
    } else {
        factorial_pos(n - 1);
    }
}

proof fn derangement_bounds(n: int)
    requires n >= 0
    ensures derangement(n) >= 0
    decreases n
{
    if n <= 1 {
    } else if n == 2 {
    } else {
        derangement_bounds(n - 1);
        derangement_bounds(n - 2);
    }
}

proof fn binomial_bounds(n: int, k: int)
    requires n >= 0, k >= 0
    ensures binomial(n, k) >= 0
{
    factorial_pos(n);
    if k <= n {
        factorial_pos(k);
        factorial_pos(n - k);
    }
}

proof fn sum_binomial_derangement_bounds(n: int, k: int, i: int)
    requires n >= 0, k >= 0, i >= 0
    ensures sum_binomial_derangement(n, k, i) >= 0
    decreases n - k - i
{
    if i < n - k {
        binomial_bounds(n, i);
        derangement_bounds(n - i);
        sum_binomial_derangement_bounds(n, k, i + 1);
    }
}

fn factorial_value(n: int) -> (result: int)
    requires n >= 0
    ensures result == factorial(n)
{
    if n <= 1 { 1 } else { n * factorial_value(n - 1) }
}

fn derangement_value(n: int) -> (result: int)
    requires n >= 0
    ensures result == derangement(n)
{
    if n <= 1 { 0 }
    else if n == 2 { 1 }
    else { (n - 1) * (derangement_value(n - 1) + derangement_value(n - 2)) }
}

fn binomial_value(n: int, k: int) -> (result: int)
    requires n >= 0, k >= 0
    ensures result == binomial(n, k)
{
    if k > n { 0 }
    else if k == 0 || k == n { 1 }
    else { factorial_value(n) / (factorial_value(k) * factorial_value(n - k)) }
}

fn sum_binomial_derangement_value(n: int, k: int, i: int) -> (result: int)
    requires n >= 0, k >= 0, i >= 0
    ensures result == sum_binomial_derangement(n, k, i)
    decreases n - k - i
{
    if i >= n - k { 0 }
    else { binomial_value(n, i) * derangement_value(n - i) + sum_binomial_derangement_value(n, k, i + 1) }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures result as int == factorial(n as int) - sum_binomial_derangement(n as int, k as int, 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented actual computation using helper functions */
    let fact_n = factorial_value(n as int);
    let sum_val = sum_binomial_derangement_value(n as int, k as int, 0);
    (fact_n - sum_val) as i8
}
// </vc-code>


}

fn main() {}