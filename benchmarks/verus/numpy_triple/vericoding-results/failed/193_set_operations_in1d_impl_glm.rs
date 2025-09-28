// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed early return logic with proper proof */
fn contains<T: PartialEq>(vec: &Vec<T>, elem: &T) -> (result: bool)
    ensures result == exists|j: int| 0 <= j < vec@.len() && vec@[j] == *elem
{
    let mut i = 0;
    while i < vec.len()
        invariant 0 <= i <= vec.len(),
        forall|j: int| 0 <= j < i ==> vec@[j] != *elem
        decreases vec.len() - i
    {
        if vec[i] == *elem {
            proof {
                assert(vec@[i] == *elem);
            }
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn in1d<T: PartialEq>(ar1: Vec<T>, ar2: Vec<T>) -> (result: Vec<bool>)
    ensures 
        result.len() == ar1.len(),
        forall|i: int| 0 <= i < ar1@.len() ==> 
            result@[i] == exists|j: int| 0 <= j < ar2@.len() && ar1@[i] == ar2@[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed - fixed helper function */
    let mut result = Vec::new();
    let mut i = 0;
    while i < ar1.len()
        invariant 0 <= i <= ar1.len(),
        result@.len() == i,
        forall|k: int| 0 <= k < i ==> 
            result@[k] == exists|j: int| 0 <= j < ar2@.len() && ar1@[k] == ar2@[j]
        decreases ar1.len() - i
    {
        let found = contains(&ar2, &ar1[i]);
        result.push(found);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}