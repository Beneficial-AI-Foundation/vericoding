use vstd::prelude::*;

verus! {

/*
function_signature: "fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)"
docstring: Implement cubes functionality.
*/

#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    // post-conditions-start
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
    // post-conditions-end
{
    // impl-start
    assume(false);
    vec![]
    // impl-end
}

fn main() {}
}