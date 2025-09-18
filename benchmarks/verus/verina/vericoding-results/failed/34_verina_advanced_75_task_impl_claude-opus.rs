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
proof fn lemma_subarray_sum_extend(sequence: Seq<i32>, start: int, end: int)
    requires 0 <= start < end < sequence.len(),
    ensures spec_subarray_sum(sequence, start, end + 1) == spec_subarray_sum(sequence, start, end) + sequence[end] as int,
    decreases end - start
{
    if start + 1 == end {
        assert(spec_subarray_sum(sequence, start, end) == sequence[start] as int);
        assert(spec_subarray_sum(sequence, start, end + 1) == sequence[start] as int + spec_subarray_sum(sequence, start + 1, end + 1));
        assert(spec_subarray_sum(sequence, start + 1, end + 1) == sequence[end] as int);
    } else {
        assert(spec_subarray_sum(sequence, start, end) == sequence[start] as int + spec_subarray_sum(sequence, start + 1, end));
        assert(spec_subarray_sum(sequence, start, end + 1) == sequence[start] as int + spec_subarray_sum(sequence, start + 1, end + 1));
        lemma_subarray_sum_extend(sequence, start + 1, end);
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
    /* code modified by LLM (iteration 4): fixed invariant syntax without parentheses around exists */
    let mut max_sum: i32 = sequence[0];
    let mut i: usize = 0;
    
    while i < sequence.len()
        invariant 0 <= i <= sequence.len(),
        invariant exists|start: int, end: int| 
            0 <= start < end <= i as int && 
            max_sum as int == spec_subarray_sum(sequence@, start, end) &&
            forall|s: int, e: int| (0 <= s < e <= i as int) ==> 
                spec_subarray_sum(sequence@, s, e) <= max_sum as int,
    {
        let mut j: usize = i + 1;
        let mut current_sum: i32 = 0;
        
        while j <= sequence.len()
            invariant i < j <= sequence.len(),
            invariant current_sum as int == spec_subarray_sum(sequence@, i as int, j as int),
            invariant forall|e: int| (i as int < e <= j as int) ==> 
                spec_subarray_sum(sequence@, i as int, e) <= max_sum as int ||
                spec_subarray_sum(sequence@, i as int, e) == current_sum as int,
        {
            current_sum = current_sum + sequence[j - 1];
            proof {
                lemma_subarray_sum_extend(sequence@, i as int, (j - 1) as int);
            }
            if current_sum > max_sum {
                max_sum = current_sum;
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