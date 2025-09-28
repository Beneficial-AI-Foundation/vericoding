// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_negatives_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n == 0 { 
        0 
    } else if n > 0 && a[n - 1] < 0 { 
        sum_negatives_to(a, n - 1) + a[n - 1] 
    } else if n > 0 { 
        sum_negatives_to(a, n - 1) 
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper functions were already correct and did not need modification. */
proof fn sum_negatives_to_unroll(a: &[i32], n: int)
    requires 0 < n <= a.len()
    ensures
        sum_negatives_to(a, n) ==
            if a[n - 1] < 0 {
                sum_negatives_to(a, n - 1) + a[n - 1]
            } else {
                sum_negatives_to(a, n - 1)
            }
{}

/* helper modified by LLM (iteration 5): The helper functions were already correct and did not need modification. */
proof fn sum_negatives_non_increasing(a: &[i32], i: int, j: int)
    requires 0 <= i <= j <= a.len()
    ensures sum_negatives_to(a, i) >= sum_negatives_to(a, j)
    decreases j - i
{
    if i < j {
        sum_negatives_to_unroll(a, j);
        sum_negatives_non_increasing(a, i, j - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed invariant proof logic by reordering proof steps. */
    let mut sum: i32 = 0;
    let mut i: usize = 0;

    proof {
        sum_negatives_non_increasing(a, 0, a.len() as int);
    }

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum as int == sum_negatives_to(a, i as int),
            i32::MIN as int <= sum_negatives_to(a, a.len() as int),
        decreases a.len() - i
    {
        proof {
            sum_negatives_to_unroll(a, (i + 1) as int);
            if a[i] < 0 {
                sum_negatives_non_increasing(a, i as int, (i + 1) as int);
            }
        }

        if a[i] < 0 {
            sum = sum + a[i];
        }
        
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}