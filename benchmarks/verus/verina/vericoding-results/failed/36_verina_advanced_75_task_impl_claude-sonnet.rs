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
/* helper modified by LLM (iteration 5): added triggers to quantifiers to fix verification */
proof fn subarray_sum_lemma(sequence: Seq<i32>, start: int, end: int)
    requires 0 <= start <= end <= sequence.len()
    ensures spec_subarray_sum(sequence, start, end) == spec_subarray_sum(sequence, start, end)
{
}

proof fn max_subarray_exists(sequence: Seq<i32>)
    requires sequence.len() > 0
    ensures exists|start: int, end: int| #[trigger] spec_subarray_sum(sequence, start, end) && 0 <= start < end <= sequence.len() && 
        forall|s: int, e: int| #[trigger] spec_subarray_sum(sequence, s, e) && (0 <= s < e <= sequence.len()) ==> 
            spec_subarray_sum(sequence, s, e) <= spec_subarray_sum(sequence, start, end)
{
    assert(0 <= 0 < 1 <= sequence.len());
}

fn compute_subarray_sum(sequence: &Vec<i32>, start: usize, end: usize) -> (result: i32)
    requires 
        0 <= start < end <= sequence.len(),
        end - start <= sequence.len()
    ensures 
        result as int == spec_subarray_sum(sequence@, start as int, end as int)
{
    let mut sum = 0i32;
    let mut i = start;
    while i < end
        invariant
            start <= i <= end,
            sum as int == spec_subarray_sum(sequence@, start as int, i as int)
        decreases end - i
    {
        sum = sum + sequence[i];
        i = i + 1;
    }
    sum
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
/* code modified by LLM (iteration 5): using triggers in quantifiers */
{
    let mut max_sum = sequence[0];
    let mut current_sum = sequence[0];
    let mut start = 0;
    let mut end = 1;
    let mut temp_start = 0;
    
    let mut i = 1;
    while i < sequence.len()
        invariant 
            0 <= i <= sequence.len(),
            0 <= start < end <= i,
            max_sum as int == spec_subarray_sum(sequence@, start as int, end as int),
            forall|s: int, e: int| #[trigger] spec_subarray_sum(sequence@, s, e) && (0 <= s < e <= i) ==> 
                spec_subarray_sum(sequence@, s, e) <= max_sum as int,
        decreases sequence.len() - i
    {
        if current_sum < 0 {
            current_sum = sequence[i];
            temp_start = i;
        } else {
            current_sum = current_sum + sequence[i];
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
            start = temp_start;
            end = i + 1;
        }
        
        i = i + 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}