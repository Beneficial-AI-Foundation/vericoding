// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_subarray_sum(sequence: Seq<i32>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end || start < 0 || end > sequence.len() {
        0
    } else if start + 1 == end {
        sequence[start] as int
    } else {
        sequence[start] as int + spec_subarray_sum(sequence, start + 1, end)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added a helper function to determine the maximum of two `i32` values. */
spec fn max_int(a: i32, b: i32) -> i32 { if a < b { b } else { a } }
// </vc-helpers>

// <vc-spec>
fn task_code(sequence: Vec<i32>) -> (result: i32)
    requires sequence.len() > 0,
    ensures 
        exists|start: int, end: int| 
            0 <= start < end <= sequence.len() && 
            result as int == spec_subarray_sum(sequence@, start, end) &&
            forall|s: int, e: int| (0 <= s < e <= sequence.len()) ==> 
                spec_subarray_sum(sequence@, s, e) <= result as int,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Cast `i` to `int` when indexing `sequence` to resolve the type mismatch error. */
{
    let mut max_so_far: i32 = sequence[0];
    let mut current_max: i32 = 0;

    let len = sequence.len();

    assert(len > 0);

    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int <= len as int,
            current_max as int >= 0,
            // max_so_far must be the maximum subarray sum found up to index i-1
            // and it must be non-negative if current_max is non-negative
            (i > 0 && exists|start: int, end: int|
                0 <= start < end <= i as int && max_so_far as int == spec_subarray_sum(sequence@, start, end)
            ) || (i == 0 && max_so_far == sequence[0]), // special case for the first element
            // current_max is the maximum subarray sum ending at index i-1
            (i > 0 && exists|start: int| 0 <= start < i as int && current_max as int == spec_subarray_sum(sequence@, start, i as int)) || (i == 0 && current_max == 0),
            // All subarray sums ending at an index j < i are <= max_so_far
            forall|s: int, e: int|
                0 <= s < e <= i as int && s < len as int && e <= len as int
                ==> spec_subarray_sum(sequence@, s, e) <= max_so_far as int
    {
        current_max = current_max + sequence[i as int];
        if current_max < 0 {
            current_max = 0;
        }

        if max_so_far < current_max {
            max_so_far = current_max;
        }

        proof {
            if i == 0 {
                assert(sequence[0] as int == spec_subarray_sum(sequence@, 0, 1));
            }
            if i > 0 {
                let prev_max_so_far = max_so_far;
                let prev_current_max = current_max;
                let element = sequence[i as int]; // Cast i to int for indexing

                if prev_current_max + element < 0 {
                    assert(current_max == 0);
                } else {
                    assert(current_max == prev_current_max + element);
                }

                if prev_max_so_far < current_max {
                    assert(max_so_far == current_max);
                } else {
                    assert(max_so_far == prev_max_so_far);
                }
            }
        }

        i = i + 1;
    }

    max_so_far
}
// </vc-code>

}
fn main() {}