// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): element-wise invert */
fn invert_elem(x: i32) -> i32 { -(x + 1) }
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
    /* code modified by LLM (iteration 5): iterate using usize index and maintain invariant with int quantifier, push inverted elements */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant i <= x.len() && result.len() == i && forall|j: int| 0 <= j && j < i as int ==> result[j as usize] == -(x[j as usize] + 1),
        decreases x.len() - i
    {
        let xi: i32 = x[i];
        let yi: i32 = invert_elem(xi);
        result.push(yi);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}