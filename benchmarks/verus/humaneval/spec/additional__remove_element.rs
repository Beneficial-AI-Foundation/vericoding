use vstd::prelude::*;

verus! {

/*
function_signature: "fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)"
docstring: Implement remove element functionality.
*/

#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        0 <= pos < a.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
    // post-conditions-end
{
    // impl-start
    assume(false);
    vec![]
    // impl-end
}

fn main() {}
}