use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn add(a: i32, b: i32) -> (result: i32)
    ensures
        result == a + b,
{
    return 0;  // TODO: Remove this line and implement the function body
}

#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    // post-conditions-start
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {}
}
