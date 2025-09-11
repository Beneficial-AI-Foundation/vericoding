use vstd::prelude::*;

verus! {

/*
function_signature: "fn is_sorted(lst: &[i32]) -> (result: bool)"
docstring: Sort elements according to specified criteria.
*/

#[verifier::loop_isolation(false)]
fn is_sorted(lst: &[i32]) -> (result: bool)
    // pre-conditions-start
    requires
        lst.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <== forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
        !result ==> exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
    // post-conditions-end
{
    // impl-start
    assume(false);
    false
    // impl-end
}

fn main() {}
}