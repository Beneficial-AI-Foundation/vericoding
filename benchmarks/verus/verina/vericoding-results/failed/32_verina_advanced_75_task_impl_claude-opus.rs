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
/* helper modified by LLM (iteration 5): Fixed proof helper for extending subarray sum */
proof fn lemma_subarray_sum_extend(sequence: Seq<i32>, start: int, end: int)
    requires
        0 <= start < end < sequence.len(),
    ensures
        spec_subarray_sum(sequence, start, end + 1) == spec_subarray_sum(sequence, start, end) + sequence[end] as int,
    decreases end - start,
{
    if start + 1 == end {
        assert(spec_subarray_sum(sequence, start, end) == sequence[start] as int);
        assert(spec_subarray_sum(sequence, start, end + 1) == sequence[start] as int + spec_subarray_sum(sequence, start + 1, end + 1));
        assert(spec_subarray_sum(sequence, start + 1, end + 1) == sequence[end] as int);
    } else {
        assert(spec_subarray_sum(sequence, start, end) == sequence[start] as int + spec_subarray_sum(sequence, start + 1, end));
        lemma_subarray_sum_extend(sequence, start + 1, end);
        assert(spec_subarray_sum(sequence, start + 1, end + 1) == spec_subarray_sum(sequence, start + 1, end) + sequence[end] as int);
        assert(spec_subarray_sum(sequence, start, end + 1) == sequence[start] as int + spec_subarray_sum(sequence, start + 1, end + 1));
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
    /* code modified by LLM (iteration 5): Fixed forall syntax with proper conjunction grouping */
    let mut max_sum: i32 = sequence[0];
    let mut i: usize = 0;
    let mut best_start: usize = 0;
    let mut best_end: usize = 1;
    
    while i < sequence.len()
        invariant
            0 <= i <= sequence.len(),
            0 <= best_start < best_end <= sequence.len(),
            max_sum as int == spec_subarray_sum(sequence@, best_start as int, best_end as int),
            forall|s: int, e: int| ((0 <= s < e && e <= i as int) ==> spec_subarray_sum(sequence@, s, e) <= max_sum as int),
    {
        let mut current_sum: i32 = 0;
        let mut j: usize = i;
        
        while j < sequence.len()
            invariant
                i <= j <= sequence.len(),
                0 <= i < sequence.len(),
                current_sum as int == spec_subarray_sum(sequence@, i as int, j as int),
                0 <= best_start < best_end <= sequence.len(),
                max_sum as int == spec_subarray_sum(sequence@, best_start as int, best_end as int),
                forall|s: int, e: int| ((0 <= s < e && e <= i as int) ==> spec_subarray_sum(sequence@, s, e) <= max_sum as int),
                forall|e: int| ((i as int < e && e <= j as int) ==> spec_subarray_sum(sequence@, i as int, e) <= max_sum as int),
        {
            current_sum = current_sum + sequence[j];
            j = j + 1;
            
            proof {
                lemma_subarray_sum_extend(sequence@, i as int, (j - 1) as int);
            }
            
            if current_sum > max_sum {
                max_sum = current_sum;
                best_start = i;
                best_end = j;
            }
        }
        i = i + 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}