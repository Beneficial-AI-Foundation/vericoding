// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): min helper */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement array summation with correct loop invariants */
    let mut res: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < a.len()
        invariant i <= a.len(),
        invariant res.len() == i,
        invariant forall|j: nat| j < i ==> res@[j] == a@[j] + b@[j],
        decreases a.len() - i
    {
        let x: i32 = a@[i] + b@[i];
        res.push(x);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}