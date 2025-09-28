// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_greater_equal(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> (result[i] <==> x1@[i] as int >= x2@[i] as int),

        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,

        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true && x2@[i] as int >= x1@[i] as int) ==> x1@[i] as int == x2@[i] as int,

        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed the invariant to use 'as int' for sequence comparisons and added invariant for lengths to ensure bounds for sequence indexing */
    let mut result = Vec::<bool>::new();
    for i in 0..x1.len()
        invariant
            x1.len() == x2.len(),
            result.len() == (i as int),
            forall|j: int| 0 <= j < i ==> (result@[j] <==> ((x1@[j] as int) >= (x2@[j] as int)))
    {
        let cmp = x1[i] >= x2[i];
        result.push(cmp);
    }
    result
}
// </vc-code>

}
fn main() {}