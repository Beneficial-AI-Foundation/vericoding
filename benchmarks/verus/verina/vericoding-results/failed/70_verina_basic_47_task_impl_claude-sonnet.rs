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
/* helper modified by LLM (iteration 5): fixed type mismatches with proper int conversions */
proof fn sum_to_bounds(a: &Vec<i32>, n: int)
    requires n >= 0, n <= a.len(), a.len() > 0,
             forall |j: int| 0 <= j < a.len() ==> a[j] >= i32::MIN / (a.len() as int) && a[j] <= i32::MAX / (a.len() as int)
    ensures sum_to(a, n) <= i32::MAX && sum_to(a, n) >= i32::MIN
    decreases n
{
    if n > 0 {
        sum_to_bounds(a, n - 1);
        assert(sum_to(a, n - 1) + a[n - 1] <= i32::MAX);
        assert(sum_to(a, n - 1) + a[n - 1] >= i32::MIN);
    }
}

proof fn sum_to_step(a: &Vec<i32>, n: int)
    requires n >= 0, n < a.len()
    ensures sum_to(a, n + 1) == sum_to(a, n) + a[n]
{
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        result == sum_to(a, a.len() as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type casting issue by using ghost variable */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum == sum_to(a, i as int)
        decreases a.len() - i
    {
        proof {
            sum_to_step(a, i as int);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}
// </vc-code>

}
fn main() {}