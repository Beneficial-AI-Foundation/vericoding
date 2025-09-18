// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): generic equality spec */
spec fn eq_bool<T>(a: T, b: T) -> bool { a == b }
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
{
    /* code modified by LLM (iteration 5): iterate over indices and push equality results */
    let mut result: Vec<bool> = Vec::new();
    let len = x1.len();
    let mut i = 0;
    while i < len {
        let b = x1[i] == x2[i];
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}