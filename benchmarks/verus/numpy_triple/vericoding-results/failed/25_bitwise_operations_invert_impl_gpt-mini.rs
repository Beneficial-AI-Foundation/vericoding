// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): return inverted element */
fn invert_elem(a: i32) -> (result: i32)
    ensures
        result == -(a + 1),
{
    -(a + 1)
}
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
    /* code modified by LLM (iteration 4): implement loop and maintain spec invariant using explicit formula */
    let mut res = Vec::<i32>::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res@[j] == -(x@[j] + 1),
        decreases x.len() - i
    {
        let xi = *x.get(i).unwrap();
        res.push(invert_elem(xi));
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}