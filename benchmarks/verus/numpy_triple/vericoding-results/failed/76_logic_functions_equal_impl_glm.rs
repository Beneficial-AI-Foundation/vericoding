// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add PartialEq bound to main function */
fn do_equal<T: PartialEq>(a: T, b: T) -> bool {
    a == b
}
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
/* code modified by LLM (iteration 5): add PartialEq bound to main function */
{
    let mut result = Vec::new();
    for i in 0..x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == (x1@[j] == x2@[j]),
            forall|j: int| 0 <= j < (i as int) ==> (result@[j] == true || result@[j] == false)
    {
        result.push(do_equal(x1[i], x2[i]));
    }
    result
}
// </vc-code>

}
fn main() {}