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
/* helper modified by LLM (iteration 5): fixed syntax error by adding proof keyword */
proof fn lemma_subarray_sum_single(sequence: Seq<i32>, i: int)
    requires 0 <= i < sequence.len(),
    ensures spec_subarray_sum(sequence, i, i + 1) == sequence[i] as int
{
}

proof fn lemma_subarray_sum_extend(sequence: Seq<i32>, start: int, mid: int, end: int)
    requires 0 <= start <= mid < end <= sequence.len(),
    ensures spec_subarray_sum(sequence, start, end) == spec_subarray_sum(sequence, start, mid) + spec_subarray_sum(sequence, mid, end)
    decreases end - start
{
    if start + 1 == mid {
        lemma_subarray_sum_single(sequence, start);
    } else {
        lemma_subarray_sum_extend(sequence, start + 1, mid, end);
    }
}

proof fn lemma_subarray_sum_monotonic(sequence: Seq<i32>, start: int, end1: int, end2: int)
    requires 0 <= start <= end1 <= end2 <= sequence.len(),
    ensures spec_subarray_sum(sequence, start, end1) <= spec_subarray_sum(sequence, start, end2)
{
    if end1 < end2 {
        lemma_subarray_sum_extend(sequence, start, end1, end2);
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
    /* code modified by LLM (iteration 5): use ghost variable for int conversion */
    let mut max_sum = sequence[0];
    let mut current_sum = sequence[0];
    let ghost mut best_start = 0int;
    let ghost mut best_end = 1int;
    let ghost mut current_start = 0int;
    
    let mut i = 1;
    while i < sequence.len()
        invariant
            1 <= i <= sequence.len(),
            0 <= current_start < i,
            0 <= best_start < best_end <= i,
            current_sum as int == spec_subarray_sum(sequence@, current_start, i as int),
            max_sum as int == spec_subarray_sum(sequence@, best_start, best_end),
            forall|s: int, e: int| (0 <= s < e <= i) ==> spec_subarray_sum(sequence@, s, e) <= max_sum as int,
    {
        if current_sum < 0 {
            current_sum = sequence[i];
            proof {
                current_start = i as int;
            }
        } else {
            current_sum = current_sum + sequence[i];
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
            proof {
                best_start = current_start;
                best_end = (i + 1) as int;
            }
        }
        
        i = i + 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}