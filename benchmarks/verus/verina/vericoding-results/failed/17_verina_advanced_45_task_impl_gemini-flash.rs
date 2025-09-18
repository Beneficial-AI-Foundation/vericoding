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
/* helper modified by LLM (iteration 5): Renamed to ensure unique identifier.*/
fn spec_max_int_helper(a: i32, b: i32) -> i32 { if a > b { a } else { b } }
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
/* code modified by LLM (iteration 5): Corrected usage of `spec_max_int_helper` to reflect its helper status, avoiding direct calls from `exec` mode. Updated loop invariants to ensure correctness of `current_max` and `max_so_far`.*/
{
    let n = xs.len();
    if n == 0 {
        return 0i32;
    }

    let mut max_so_far: i32 = xs[0];
    let mut current_max: i32 = xs[0];

    let mut i: usize = 1;

    while i < n
        invariant
            1 <= i as int <= n as int,
            // max_so_far is the maximum subarray sum encountered so far up to index i-1
            // This exists and is less than or equal to `max_so_far`
            (exists|start: int, len: int|
                0 <= start < i as int &&
                1 <= len <= i as int - start &&
                max_so_far == spec_sum(xs, start, len) as i32
            ),
            (forall|start: int, len: int|
                0 <= start < i as int &&
                1 <= len <= i as int - start
                ==> spec_sum(xs, start, len) <= max_so_far as int
            ),
            // current_max is the maximum subarray sum ending at index i-1
            (exists|start: int|
                0 <= start < i as int &&
                current_max == spec_sum(xs, start, (i as int) - start) as i32
            ),
            (forall|start: int| // current_max is max of all sub-arrays ending at i-1
                0 <= start < i as int
                ==> spec_sum(xs, start, (i as int) - start) <= current_max as int
            )
        decreases n - i
    {
        current_max = spec_max_int_helper(xs[i], current_max + xs[i]);
        max_so_far = spec_max_int_helper(max_so_far, current_max);
        i = i + 1;
    }
    max_so_far
}
// </vc-code>

}
fn main() {}