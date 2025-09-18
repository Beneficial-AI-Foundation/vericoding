// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize to int for specifications */
spec fn usize_to_int(u: usize) -> int { u as int }
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: &Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == (exists|i: int| 1 <= i < result.0.len() && result.0[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute prefix sums with wrapping_add and maintain invariant relating res and operations */
    let mut res: Vec<i32> = Vec::new();
    res.push(0);
    let mut i: usize = 0;
    let len: usize = operations.len();
    let mut negative: bool = false;
    while i < len
        invariant
            res.len() == i + 1,
            forall|k: int| 0 <= k && k < (usize_to_int(i) + 1) ==> res.view()[k] == if k == 0 { 0 } else { res.view()[k - 1] + operations.view()[k - 1] },
        decreases
            len - i
    {
        // prove index precondition for safe access
        assert(i < operations.len());
        let op: i32 = operations[i];
        let last: i32 = res[res.len() - 1];
        let next: i32 = last.wrapping_add(op);
        res.push(next);
        if next < 0 {
            negative = true;
        }
        i = i + 1;
    }
    (res, negative)
}
// </vc-code>

}
fn main() {}