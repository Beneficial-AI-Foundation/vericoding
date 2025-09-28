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
/* helper modified by LLM (iteration 5): add helper function to check int range */
proof fn is_valid_i32_value(x: int) -> bool {
    (i32::MIN as int) <= x <= (i32::MAX as int)
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        result == sum_to(a, a.len() as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use i32 accumulator instead of int */
{
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= (i as int) <= (a.len() as int),
            total == sum_to(a, i as int) as i32,
        decreases (a.len() as int) - (i as int)
    {
        total = total + a[i];
        i += 1;
    }
    total
}
// </vc-code>

}
fn main() {}