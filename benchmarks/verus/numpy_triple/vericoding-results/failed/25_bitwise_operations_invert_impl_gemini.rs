// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn invert(x: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == -(x[i] + 1),
        forall|i: int| 0 <= i < x.len() && x[i] == 0 ==> result[i] == -1,
        forall|i: int| 0 <= i < x.len() && x[i] == -1 ==> result[i] == 0,
        forall|i: int| 0 <= i < x.len() && x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): replaced bitwise NOT with equivalent arithmetic to satisfy loop invariants */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == -(x@[j] + 1),
        decreases x.len() - i
    {
        result.push(-(x[i] + 1));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}