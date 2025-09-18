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
/* helper modified by LLM (iteration 5): Added decreases clause to lemma_subarray_sum_positive */
proof fn lemma_subarray_sum_positive(sequence: Seq<i32>, start: int, end: int)
    decreases end - start
    requires
        0 <= start <= end <= sequence.len(),
        forall|i: int| 0 <= i < sequence.len() ==> sequence[i] >= 0,
    ensures
        spec_subarray_sum(sequence, start, end) >= 0
{
    if start < end {
        lemma_subarray_sum_positive(sequence, start + 1, end);
    }
}

/* helper modified by LLM (iteration 5): Added decreases clause to lemma_subarray_sum_add_element */
proof fn lemma_subarray_sum_add_element(sequence: Seq<i32>, start: int, end: int)
    decreases end - start
    requires
        0 <= start < end <= sequence.len(),
    ensures
        spec_subarray_sum(sequence, start, end) == sequence[start] as int + spec_subarray_sum(sequence, start + 1, end)
{
    // This follows directly from the spec definition
}

/* helper modified by LLM (iteration 5): Added decreases clause to lemma_subarray_sum_monotonic */
proof fn lemma_subarray_sum_monotonic(sequence: Seq<i32>, seq_start: int, seq_end: int, sub_start: int, sub_end: int)
    decreases seq_end - seq_start
    requires
        0 <= seq_start <= sub_start < sub_end <= seq_end <= sequence.len(),
        forall|i: int| seq_start <= i < seq_end ==> sequence[i] >= 0,
    ensures
        spec_subarray_sum(sequence, sub_start, sub_end) <= spec_subarray_sum(sequence, seq_start, seq_end)
{
    if seq_start < sub_start {
        lemma_subarray_sum_monotonic(sequence, seq_start + 1, seq_end, sub_start, sub_end);
    }
}
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
{
    /* code modified by LLM (iteration 5): Fixed main logic with verification support */
    let mut max_sum = sequence[0];
    let mut current_sum = sequence[0];
    
    let mut start_index = 0;
    let mut end_index = 1;
    let mut temp_start = 0;
    
    let mut i = 1;
    while i < sequence.len()
        invariant 
            0 <= i <= sequence.len(),
            current_sum as int == spec_subarray_sum(sequence@, temp_start as int, i as int),
            max_sum as int == spec_subarray_sum(sequence@, start_index as int, end_index as int),
            forall|s: int, e: int| (0 <= s < e <= i as int) ==> spec_subarray_sum(sequence@, s, e) <= max_sum as int,
            temp_start as int <= i as int,
            start_index as int <= end_index as int <= i as int,
            0 <= temp_start < sequence.len(),
            0 <= start_index < end_index <= sequence.len(),
    {
        if current_sum < 0 {
            current_sum = sequence[i];
            temp_start = i;
        } else {
            current_sum = current_sum + sequence[i];
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
            start_index = temp_start;
            end_index = i + 1;
        }
        
        i = i + 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}