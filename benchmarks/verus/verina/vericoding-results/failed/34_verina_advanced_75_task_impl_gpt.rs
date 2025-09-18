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
/* helper modified by LLM (iteration 2): simplified to a pure max helper for ints */
spec fn int_max(a: int, b: int) -> int { if a >= b { a } else { b } }
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
    /* code modified by LLM (iteration 2): add decreases clause to while loop for termination */
    let n = sequence.len();
    let mut max_ending_here: i32 = sequence[0];
    let mut max_so_far: i32 = sequence[0];

    let mut i: usize = 1;
    while i < n
        invariant
            sequence.len() == n,
            0 < n,
            1 <= i <= n
        decreases (n - i) as int
    {
        let x = sequence[i];
        let candidate = max_ending_here + x;
        if candidate < x {
            max_ending_here = x;
        } else {
            max_ending_here = candidate;
        }
        if max_ending_here > max_so_far {
            max_so_far = max_ending_here;
        }
        i = i + 1;
    }
    max_so_far
}
// </vc-code>

}
fn main() {}