// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: &Vec<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        result == sum_to(a, a.len() as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added decreases clause to the while loop to fix verification error */
{
    let mut sum = 0i32;
    let mut i = 0usize;
    while i < a.len()
        invariant
            i <= a.len(),
            sum as int == sum_to(a, i as int)
        decreases a.len() - i
    {
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}