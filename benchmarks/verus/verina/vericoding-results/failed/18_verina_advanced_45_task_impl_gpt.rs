// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_sum(xs: &Vec<i32>, start: int, len: int) -> int 
    decreases len
{
    if len <= 0 {
        0
    } else {
        xs[start] + spec_sum(xs, start + 1, len - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added max function for i32 */
fn max_i32(a: i32, b: i32) -> i32 { if a > b { a } else { b } }
/* helper modified by LLM (iteration 2): predicate for valid subarray bounds */
spec fn is_valid_subarray(xs: &Vec<i32>, start: int, len: int) -> bool { 0 <= start && start < xs.len() && 1 <= len && len <= xs.len() - start }
// </vc-helpers>

// <vc-spec>
fn max_subarray_sum(xs: &Vec<i32>) -> (result: i32)
    ensures
        xs.len() == 0 ==> result == 0,
        xs.len() > 0 ==> (
            exists|start: int, len: int| 
                0 <= start < xs.len() && 
                1 <= len <= xs.len() - start &&
                result == spec_sum(xs, start, len) as i32
        ) &&
        (forall|start: int, len: int|
            0 <= start < xs.len() && 
            1 <= len <= xs.len() - start
            ==> spec_sum(xs, start, len) <= result as int
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix while-loop invariant placement to satisfy parser */
    let n = xs.len();
    if n == 0 {
        return 0;
    }
    let mut best: i32 = xs[0];
    let mut start: usize = 0;
    while start < n
        invariant start <= n && n == xs.len()
    {
        let mut run: i32 = 0;
        let mut end: usize = start;
        while end < n
            invariant start <= end && end <= n && n == xs.len()
        {
            run = run + xs[end];
            if run > best {
                best = run;
            }
            end = end + 1;
        }
        start = start + 1;
    }
    best
}
// </vc-code>

}
fn main() {}