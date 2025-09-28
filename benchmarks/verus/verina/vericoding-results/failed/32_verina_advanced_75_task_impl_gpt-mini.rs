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
/* helper modified by LLM (iteration 2): prefix sum spec */
spec fn spec_prefix(sequence: Seq<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { spec_prefix(sequence, n - 1) + sequence[n - 1] as int }
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
    /* code modified by LLM (iteration 2): compute maximum subarray sum by scanning all subarrays ending at each end index */
    let n: usize = sequence.len();
    let mut best: i32 = sequence[0];
    let mut best_s: usize = 0usize;
    let mut best_e: usize = 1usize;

    let mut e: usize = 1usize;
    while e <= n
        invariant
            1 <= e && e <= n + 1,
            forall|s: int, ee: int| 0 <= s && ee < e as int && s < ee ==> spec_subarray_sum(sequence@, s, ee) <= best as int,
            spec_subarray_sum(sequence@, best_s as int, best_e as int) == best as int,
        decreases n + 1 - e
    {
        let mut s_idx: usize = e;
        let mut sum: i32 = 0;
        while s_idx > 0
            invariant
                0 <= s_idx && s_idx <= e,
                sum as int == spec_subarray_sum(sequence@, s_idx as int, e as int),
                forall|s: int, ee: int| 0 <= s && ee < e as int && s < ee ==> spec_subarray_sum(sequence@, s, ee) <= best as int,
                spec_subarray_sum(sequence@, best_s as int, best_e as int) == best as int,
            decreases s_idx
        {
            s_idx -= 1;
            sum = sum + sequence[s_idx];
            if sum > best {
                best = sum;
                best_s = s_idx;
                best_e = e;
            }
        }
        e += 1;
    }

    let result = best;

    proof {
        let start = best_s as int;
        let end = best_e as int;
        assert(0 <= start && start < end && end <= sequence.len() as int);
        assert(result as int == spec_subarray_sum(sequence@, start, end));
        assert(forall|s: int, ee: int| 0 <= s && s < ee && ee <= sequence.len() as int ==> spec_subarray_sum(sequence@, s, ee) <= result as int);
    }

    result
}
// </vc-code>

}
fn main() {}