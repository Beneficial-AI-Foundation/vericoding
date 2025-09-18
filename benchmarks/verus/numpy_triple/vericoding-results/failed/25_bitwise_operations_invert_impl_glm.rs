// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove lemma and rely on direct assert */
fn invert_element(x: i32) -> i32 {
    !x
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
/* code modified by LLM (iteration 5): remove lemma call and use direct assert */
{
    let mut result: Vec<i32> = Vec::new();
    for i in 0..x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == -(x[j] + 1),
            forall|j: int| 0 <= j < i && x[j] == 0 ==> result[j] == -1,
            forall|j: int| 0 <= j < i && x[j] == -1 ==> result[j] == 0,
            forall|j: int| 0 <= j < i && x[j] != -1 ==> (x[j] > 0 <==> result[j] < 0),
    {
        result.push(invert_element(x[i]));
        proof {
            assert(!x[i] == -(x[i] + 1));
        }
    }
    result
}
// </vc-code>

}
fn main() {}