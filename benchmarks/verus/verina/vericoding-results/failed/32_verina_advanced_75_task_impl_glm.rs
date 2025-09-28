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
/* helper modified by LLM (iteration 4): removed requires clauses and made functions total by handling out-of-bound indices */
spec fn spec_max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

spec fn max_ending_at(sequence: Seq<i32>, j: int) -> int
    decreases if j < 0 || j >= sequence.len() { 0 } else { j }
{
    if j < 0 || j >= sequence.len() || sequence.len() == 0 {
        0
    } else if j == 0 {
        sequence[0] as int
    } else {
        sequence[j] as int + spec_max(0, max_ending_at(sequence, j-1))
    }
}

spec fn max_so_far_up_to(sequence: Seq<i32>, j: int) -> int
    decreases if j < 0 || j >= sequence.len() { 0 } else { j }
{
    if j < 0 || j >= sequence.len() || sequence.len() == 0 {
        0
    } else if j == 0 {
        sequence[0] as int
    } else {
        spec_max(max_so_far_up_to(sequence, j-1), max_ending_at(sequence, j))
    }
}

/* helper modified by LLM (iteration 5): added executable max function to replace std::cmp::max */
fn max(a: i32, b: i32) -> (result: i32)
    ensures result == if a > b { a } else { b }
{
    if a > b { a } else { b }
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
    /* code modified by LLM (iteration 5): replaced std::cmp::max with custom max function */
    let mut max_so_far = sequence[0];
    let mut max_ending_here = sequence[0];
    for i in 1..sequence.len()
        invariant
            1 <= i <= sequence.len(),
            max_ending_here as int == max_ending_at(sequence@, i-1),
            max_so_far as int == max_so_far_up_to(sequence@, i-1),
    {
        max_ending_here = max(sequence[i], max_ending_here + sequence[i]);
        max_so_far = max(max_so_far, max_ending_here);
    }
    max_so_far
}
// </vc-code>

}
fn main() {}