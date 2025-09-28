// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int) -> bool {
    n >= 1 && a >= 1 && a <= b && b <= 36
}

spec fn digit_sum(n: int) -> int 
    decreases n
{
    if n <= 0 { 0 }
    else { (n % 10) + digit_sum(n / 10) }
}

spec fn sum_in_range(n: int, a: int, b: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else if a <= digit_sum(n) && digit_sum(n) <= b { 
        n + sum_in_range(n - 1, a, b) 
    }
    else { 
        sum_in_range(n - 1, a, b) 
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed compilation error: '!' not expected. */
lemma lemma_digit_sum_non_negative(n: int)
    requires n >= 0
    ensures digit_sum(n) >= 0
    decreases n
{
    if n > 0 {
        lemma_digit_sum_non_negative(n / 10);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: i8)
    requires valid_input(n as int, a as int, b as int)
    ensures 
        result as int == sum_in_range(n as int, a as int, b as int) &&
        result >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes, previous fix was correct. */
{
    let N: int = n as int;
    let A: int = a as int;
    let B: int = b as int;

    let mut total_sum: int = 0;
    let mut i: int = 1;

    while i <= N
        invariant
            1 <= i && i <= N + 1,
            total_sum == sum_in_range(i - 1, A, B),
            total_sum >= 0
        decreases N - i
    {
        proof {
            lemma_digit_sum_non_negative(i);
        }

        if A <= digit_sum(i) && digit_sum(i) <= B {
            total_sum = total_sum + i;
        }
        i = i + 1;
    }
    
    total_sum as i8
}
// </vc-code>


}

fn main() {}