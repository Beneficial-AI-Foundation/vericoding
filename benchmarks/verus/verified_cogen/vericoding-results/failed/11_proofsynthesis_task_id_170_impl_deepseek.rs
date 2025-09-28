// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(arr: Seq<i64>) -> (result: int)
    decreases arr.len(),
{
    if arr.len() == 0 {
        0
    } else {
        sum_to(arr.drop_last()) + arr.last()
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove problematic int usage and add proper ghost conversions */
proof fn sum_to_base_case(arr: Seq<i64>) 
    ensures 
        arr.len() == 0 ==> sum_to(arr) == 0,
{
}

proof fn sum_to_recursive_case(arr: Seq<i64>) 
    requires 
        arr.len() > 0,
    ensures 
        sum_to(arr) == sum_to(arr.drop_last()) + arr.last(),
{
}

fn sum_iter(arr: &Vec<i64>, i: usize, j: usize, sum: &mut i128)
    requires
        0 <= i <= j < arr.len(),
    ensures
        *sum == sum_to(arr@.subrange(i as int, (j as int + 1))),
{
    *sum = 0;
    let mut idx = i;
    while idx <= j
        invariant
            i <= idx <= j + 1,
            *sum == sum_to(arr@.subrange(i as int, idx as int)),
            idx <= arr.len(),
        decreases (j + 1) - idx,
    {
        assert(idx < arr.len()) by {
            assert(i <= idx <= j);
            assert(j < arr.len());
        }
        proof {
            let ghost_sum = *sum as int;
            let ghost_val = arr[idx] as int;
            let ghost_new_sum = ghost_sum + ghost_val;
            *sum = ghost_new_sum as i128;
        }
        idx = idx + 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_range_list(arr: &Vec<i64>, start: usize, end: usize) -> (sum: i128)

    requires
        0 <= start <= end,
        start <= end < arr.len(),

    ensures
        sum_to(arr@.subrange(start as int, end + 1 as int)) == sum,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed to main function, helper handles the logic */
{
    let mut sum_val: i128 = 0;
    sum_iter(arr, start, end, &mut sum_val);
    sum_val
}
// </vc-code>

}
fn main() {}