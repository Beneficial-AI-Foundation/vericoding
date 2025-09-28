// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn invert_helper(x: i32) -> (result: i32)
    requires
        true,
    ensures
        result == !x,
        x == 0 ==> result == -1,
        x == -1 ==> result == 0,
        x != -1 ==> (x > 0 <==> result < 0),
{
    /* helper modified by LLM (iteration 5): removed i32::MIN requirement */
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
{
    /* code modified by LLM (iteration 5): fixed to use invert_helper and handle vector invariants */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == !x@[j],
        decreases x.len() - i,
    {
        let elem = x[i];
        let inverted = invert_helper(elem);
        result.push(inverted);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}