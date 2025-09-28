// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_equal<T>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires 
        x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [removed `view_native` calls and used sequence indexing for comparison] */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < x1.len()
        invariant
            result.len() == i,
            i <= x1.len(),
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x1@[j] == x2@[j]),
            x1.len() == x2.len(),
    {
        let are_equal = x1@[i as int] == x2@[i as int];
        result.push(are_equal);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}