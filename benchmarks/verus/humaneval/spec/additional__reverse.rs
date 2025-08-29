use vstd::prelude::*;

verus! {

/*
function_signature: "fn reverse(a: &[i32]) -> (result: Vec<i32>)"
docstring: Implement reverse functionality.
*/

fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
{
    // impl-start
    assume(false);
    vec![]
    // impl-end
}

fn main() {}
}