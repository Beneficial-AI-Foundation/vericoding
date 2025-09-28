// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no functional change */
fn max(a: i32, b: i32) -> (result: i32)
    ensures
        result >= a && result >= b,
        result == a || result == b,
{
    if a >= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn max_subarray_sum_divisible_by_k(arr: &Vec<i32>, k: i32) -> (result: i32)
    requires k > 0,
    ensures true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added k > 0 to loop invariants to fix precondition failure */
    let mut max_sum: i32 = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            k > 0,
        decreases arr.len() - i,
    {
        let mut current_sum: i32 = 0;
        let mut j: usize = i;
        while j < arr.len()
            invariant
                i <= j <= arr.len(),
                k > 0,
            decreases arr.len() - j,
        {
            let next_sum = current_sum.checked_add(arr[j]);
            if let Some(sum) = next_sum {
                current_sum = sum;
                if current_sum % k == 0 {
                    max_sum = max(max_sum, current_sum);
                }
            } else {
                // The sum of arr[i..=j] overflows, so any subarray starting at i
                // and extending beyond j will also overflow. We can stop checking from this i.
                // However, for simplicity, we just break the inner loop.
                break;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    max_sum
}
// </vc-code>

}
fn main() {}