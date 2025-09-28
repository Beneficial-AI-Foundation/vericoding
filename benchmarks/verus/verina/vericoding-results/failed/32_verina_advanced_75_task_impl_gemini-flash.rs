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
/* helper modified by LLM (iteration 4): Removed all helper functions because they are not needed for this solution. */
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
/* code modified by LLM (iteration 4): Added a `decreases` clause to the main loop and the inner loop to fix the verification error. */
{
    let mut max_so_far: i32 = -2_000_000_000; // Initialize with a very small number
    let mut current_max: i32 = 0;
    let mut start_idx: usize = 0;
    let mut end_idx: usize = 0;
    let mut current_start_idx: usize = 0;

    let len = sequence.len();

    if len == 0 {
        // This case should not be reached due to the `requires sequence.len() > 0` clause
        // However, for logical completeness, if it were to happen, the result would be 0 or some error indicator
        return 0;
    }

    let ghost seq_spec = sequence@;

    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i && i <= len,
            0 <= current_start_idx && current_start_idx <= i,
            // current_max is the sum of the subarray from current_start_idx to i-1
            // When i == current_start_idx, current_max is 0.
            current_max as int == spec_subarray_sum(seq_spec, current_start_idx as int, i as int),

            // max_so_far holds the maximum subarray sum found so far ending before or at i.
            // If max_so_far is still -2_000_000_000, it means no positive sum has been found.
            // We need to ensure that if max_so_far is updated, then start_idx and end_idx are valid for it.
            ((max_so_far == -2_000_000_000) || (0 <= start_idx && start_idx < end_idx && end_idx <= i)),
            (max_so_far as int == spec_subarray_sum(seq_spec, start_idx as int, end_idx as int)) || max_so_far == -2_000_000_000,

            // Every subarray found up to index i-1 (inclusive) cannot have a sum greater than max_so_far
            forall|s: int, e: int| (0 <= s && s < e && e <= i as int) ==> 
                spec_subarray_sum(seq_spec, s, e) <= max_so_far as int,
        decreases len - i
    {
        let next_current_max_val = current_max + sequence[i];

        if next_current_max_val > max_so_far {
            max_so_far = next_current_max_val;
            start_idx = current_start_idx;
            end_idx = i + 1;
        }

        if next_current_max_val < 0 {
            // If the current sum becomes negative, reset it to 0 and start a new subarray
            current_max = 0;
            current_start_idx = i + 1;
        } else {
            current_max = next_current_max_val;
        }
        i = i + 1;
    }

    // If all numbers are negative, max_so_far would still be -2_000_000_000, which is incorrect.
    // In this case, the largest single element is the desired result.
    if max_so_far == -2_000_000_000 {
        let mut largest_single_element: i32 = sequence[0];
        let mut k: usize = 1;
        while k < len
            invariant
                1 <= k && k <= len,
                forall|idx: int| 0 <= idx && idx < k ==> sequence[idx] <= largest_single_element,
            decreases len - k
        {
            if sequence[k] > largest_single_element {
                largest_single_element = sequence[k];
            }
            k = k + 1;
        }
        largest_single_element
    } else {
        max_so_far
    }
}
// </vc-code>

}
fn main() {}