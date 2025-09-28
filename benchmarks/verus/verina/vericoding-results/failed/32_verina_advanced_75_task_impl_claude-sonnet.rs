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
proof fn lemma_subarray_sum_single(sequence: Seq<i32>, i: int)
    requires 0 <= i < sequence.len(),
    ensures spec_subarray_sum(sequence, i, i + 1) == sequence[i] as int
{
}

proof fn lemma_subarray_sum_extends(sequence: Seq<i32>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= sequence.len(),
    ensures spec_subarray_sum(sequence, start, end) == spec_subarray_sum(sequence, start, mid) + spec_subarray_sum(sequence, mid, end)
    decreases end - start
{
    if start >= end || start < 0 || end > sequence.len() {
        return;
    }
    if start == mid {
        return;
    }
    if mid == end {
        return;
    }
    lemma_subarray_sum_extends(sequence, start + 1, mid, end);
}

/* helper modified by LLM (iteration 5): simple O(n^2) brute force solution for maximum subarray */
fn max_subarray_sum_simple(sequence: &Vec<i32>) -> (result: i32)
    requires sequence.len() > 0,
    ensures
        exists|start: int, end: int|
            0 <= start < end <= sequence.len() &&
            result as int == spec_subarray_sum(sequence@, start, end) &&
            forall|s: int, e: int| (0 <= s < e <= sequence.len()) ==>
                spec_subarray_sum(sequence@, s, e) <= result as int,
{
    let n = sequence.len();
    let mut max_sum = sequence[0];
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            exists|start: int, end: int|
                0 <= start < end <= sequence.len() &&
                max_sum as int == spec_subarray_sum(sequence@, start, end) &&
                forall|s: int, e: int| (0 <= s < e <= i) ==>
                    spec_subarray_sum(sequence@, s, e) <= max_sum as int,
        decreases n - i
    {
        let mut j = i + 1;
        while j <= n
            invariant
                i < j <= n,
                exists|start: int, end: int|
                    0 <= start < end <= sequence.len() &&
                    max_sum as int == spec_subarray_sum(sequence@, start, end) &&
                    forall|s: int, e: int| ((0 <= s < e < i) || (s == i && i < e < j)) ==>
                        spec_subarray_sum(sequence@, s, e) <= max_sum as int,
            decreases n - j
        {
            let mut sum = 0i32;
            let mut k = i;
            while k < j
                invariant
                    i <= k <= j,
                decreases j - k
            {
                sum = sum + sequence[k];
                k += 1;
            }
            
            if sum > max_sum {
                max_sum = sum;
            }
            j += 1;
        }
        i += 1;
    }
    
    max_sum
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
    /* code modified by LLM (iteration 5): call helper function for simple brute force solution */
    max_subarray_sum_simple(&sequence)
}
// </vc-code>

}
fn main() {}