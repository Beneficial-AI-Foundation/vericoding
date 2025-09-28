// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
fn contains(vec: &Vec<i8>, elem: i8) -> (ret: bool)
    ensures
        ret == exists|i:int| 0 <= i < vec@.len() && vec@[i] == elem,
{
    let mut i = 0;
    while i < vec.len()
        invariant
            i <= vec@.len(),
            forall|j:int| 0 <= j < i ==> vec@[j] != elem,
        decreases vec@.len() - i
    {
        if vec[i] == elem {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn intersect(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() < a.len() && result.len() < b.len(),
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < b@.len() ==> (
            (a@[i] == b@[j] ==> exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i]) &&
            (a@[i] != b@[j] ==> !exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i])
        )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): changed condition to avoid adding elements present in b */
    let mut result = Vec::new();
    for i in 0..a.len() {
        if !contains(&b, a[i]) && !contains(&result, a[i]) {
            result.push(a[i]);
        }
    }
    result
}
// </vc-code>


}
fn main() {}