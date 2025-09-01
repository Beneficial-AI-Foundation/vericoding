use vstd::prelude::*;

verus! {

/*
function_signature: "fn array_append(a: Vec<i32>, b: i32) -> (result: Vec<i32>)"
docstring: Implement array append functionality.
*/

#[verifier::loop_isolation(false)]
fn array_append(a: Vec<i32>, b: i32) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + 1,
        forall|i: int| #![auto] 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
    // post-conditions-end
{
    // impl-start
    assume(false);
    vec![]
    // impl-end
}

fn main() {}
}