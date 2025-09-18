// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_greater_equal(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> (result[i] <==> x1@[i] >= x2@[i]),

        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,

        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true && x2@[i] >= x1@[i]) ==> x1@[i] == x2@[i],

        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added invariant i <= x1.len() to help prove loop termination properties */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (result@[j] <==> x1@[j] >= x2@[j])
        decreases x1.len() - i
    {
        result.push(x1[i] >= x2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}