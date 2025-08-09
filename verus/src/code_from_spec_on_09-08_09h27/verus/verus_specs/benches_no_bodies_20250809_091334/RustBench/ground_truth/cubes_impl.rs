use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn add(a: i32, b: i32) -> (result: i32)
    ensures
        result == a + b,
{
    a + b
}

#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while idx < len
        invariant
            result.len() == idx,
            forall|i: int| 0 <= i && i < idx ==> result[i] == i * i * i
        decreases len - idx
    {
        let cube = (idx as i32) * (idx as i32) * (idx as i32);
        result.push(cube);
        idx += 1;
    }
    
    result
}

fn main() {}
}