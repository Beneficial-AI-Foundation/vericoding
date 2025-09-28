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
/* helper modified by LLM (iteration 5): Fixed max_subarray_sum spec function syntax and improved monotonic lemma */
proof fn lemma_subarray_sum_monotonic(sequence: Seq<i32>, s1: int, e1: int, s2: int, e2: int)
    requires 0 <= s1 < e1 <= sequence.len(), 0 <= s2 < e2 <= sequence.len(), s1 <= s2, e1 <= e2
    ensures spec_subarray_sum(sequence, s1, e1) <= spec_subarray_sum(sequence, s2, e2)
decreases e2 - s2 {
    if s2 == s1 && e2 == e1 {
        // Base case: same subarray
    } else {
        let next_s = if s2 > s1 { s2 - 1 } else { s2 };
        let next_e = if e2 < e1 { e2 + 1 } else { e2 };
        lemma_subarray_sum_monotonic(sequence, s1, e1, next_s, next_e);
    }
}

spec fn max_subarray_sum(sequence: Seq<i32>, up_to: int) -> int
    requires 0 <= up_to <= sequence.len()
    decreases up_to
{
    if up_to == 0 {
        0
    } else {
        let prev_max = max_subarray_sum(sequence, up_to - 1);
        let mut max_ending_here = 0;
        let mut j: int = up_to - 1;
        while j >= 0
            invariant 0 <= j <= up_to - 1,
            decreases j
        {
            let sum_here = spec_subarray_sum(sequence, j, up_to);
            if sum_here > max_ending_here {
                max_ending_here = sum_here;
            }
            j = j - 1;
        }
        if prev_max > max_ending_here { prev_max } else { max_ending_here }
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
/* code modified by LLM (iteration 5): Fixed comma separator in exists invariant and simplified implementation */
{
    let n = sequence.len();
    let mut max_sum = sequence[0];
    let mut current_sum = sequence[0];
    let mut start_index: usize = 0;
    
    let mut i: usize = 1;
    while i < n
        invariant 
            0 <= i <= n,
            current_sum as int == spec_subarray_sum(sequence@, start_index as int, i as int),
            exists|end: int| 0 <= start_index as int < end <= i as int,  // Fixed: added comma here
            max_sum as int == spec_subarray_sum(sequence@, start_index as int, end),
            forall|s: int, e: int| (0 <= s < e <= i as int) ==> spec_subarray_sum(sequence@, s, e) <= max_sum as int
        decreases n - i
    {
        if current_sum < 0 {
            current_sum = sequence[i];
            start_index = i;
        } else {
            current_sum += sequence[i];
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
        }
        
        i += 1;
    }
    
    max_sum
}
// </vc-code>

}
fn main() {}