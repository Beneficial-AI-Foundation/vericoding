// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple add function for i32 */
fn add_i32(a: i32, b: i32) -> i32 { a + b }
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
    /* code modified by LLM (iteration 3): compute prefix sums and track negative entries */
    let mut res: Vec<i32> = Vec::new();
    res.push(0);
    let mut any_neg: bool = false;
    let mut i: nat = 0;
    while i < operations.len()
        invariant res.len() == i + 1
        invariant res@[0] == 0
        invariant forall|t: nat| t < i ==> res@[t + 1] == res@[t] + operations@[t]
        invariant any_neg == (exists|t: nat| 1 <= t && t <= i && res@[t] < 0)
        decreases operations.len() - i
    {
        let last = res.index(i);
        let op = operations.index(i);
        let new = last + op;
        res.push(new);
        if new < 0 {
            any_neg = true;
        }
        i = i + 1;
    }
    (res, any_neg)
}
// </vc-code>

}
fn main() {}