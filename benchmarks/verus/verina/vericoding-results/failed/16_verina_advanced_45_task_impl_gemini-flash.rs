// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_sum(xs: &Vec<i32>, start: int, len: int) -> int 
    decreases len
{
    if len <= 0 {
        0
    } else {
        xs[start] + spec_sum(xs, start + 1, len - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed max_spec_sum and max_overall_sum_slice, as they were not being used in the executable code. */
spec fn max_ending_here(xs: &Vec<i32>, idx: int) -> int
    requires 0 <= idx < xs.len()
    decreases idx
{
    if idx == 0 {
        xs[0] as int
    } else {
        let prev_max = max_ending_here(xs, idx - 1);
        (prev_max + xs[idx]).max(xs[idx] as int)
    }
}
// </vc-helpers>

// <vc-spec>
fn max_subarray_sum(xs: &Vec<i32>) -> (result: i32)
    ensures
        xs.len() == 0 ==> result == 0,
        xs.len() > 0 ==> (
            exists|start: int, len: int| 
                0 <= start < xs.len() && 
                1 <= len <= xs.len() - start &&
                result == spec_sum(xs, start, len) as i32
        ) &&
        (forall|start: int, len: int|
            0 <= start < xs.len() && 
            1 <= len <= xs.len() - start
            ==> spec_sum(xs, start, len) <= result as int
        ),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type annotation for `i` in the `while` loop, and removed unused helper functions from helper section. */
{
    if xs.len() == 0 {
        return 0i32;
    }

    let mut max_so_far: i32 = xs[0];
    let mut current_max: i32 = xs[0]; // Initialize current_max with the first element

    let mut i: usize = 1; // type annotation added
    while i < xs.len()
        invariant // This invariant block needs to be before 'decreases'
            1 <= i <= xs.len()
        decreases xs.len() - i
    {
        let val_at_i = xs[i];
        let sum_with_prev = current_max + val_at_i;
        if sum_with_prev > val_at_i {
            current_max = sum_with_prev;
        } else {
            current_max = val_at_i;
        }
        
        if current_max > max_so_far {
            max_so_far = current_max;
        }

        i = i + 1;
    }
    max_so_far
}
// </vc-code>

}
fn main() {}