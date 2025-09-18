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
/* helper modified by LLM (iteration 5): removed ensures clause to fix compilation error by avoiding reference to private spec fn */
fn subarray_sum(sequence: &Vec<i32>, start: usize, end: usize) -> (sum: i32)
    requires
        start <= end <= sequence.len(),
    decreases end - start
{
    if start == end {
        0
    } else {
        sequence[start] + subarray_sum(sequence, start + 1, end)
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
/* code modified by LLM (iteration 5): fixed invariant's exists to be <= i for proper maintenance during loop */
{
    let mut max_so_far = sequence[0];
    let mut max_ending_here = sequence[0];
    let mut i = 1;
    while i < sequence.len()
        invariant
            0 < i <= sequence.len(),
            exists |s: int, e: int| 0 <= s < e <= i && (max_so_far as int) == spec_subarray_sum(sequence@, s, e),
            forall |s: int, e: int| 0 <= s < e <= i ==> spec_subarray_sum(sequence@, s, e) <= (max_so_far as int),
    {
        max_ending_here = if max_ending_here + sequence[i] > sequence[i] { max_ending_here + sequence[i] } else { sequence[i] };
        max_so_far = if max_ending_here > max_so_far { max_ending_here } else { max_so_far };
        i = i + 1;
    }
    proof {
        assert(forall |s: int, e: int| 0 <= s < e <= sequence.len() ==> spec_subarray_sum(sequence@, s, e) <= (max_so_far as int));
    }
    max_so_far
}
// </vc-code>

}
fn main() {}