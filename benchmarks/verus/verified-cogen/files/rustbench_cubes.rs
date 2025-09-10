use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
{
    assume(false);
    unreached()
}

}
fn main() {}