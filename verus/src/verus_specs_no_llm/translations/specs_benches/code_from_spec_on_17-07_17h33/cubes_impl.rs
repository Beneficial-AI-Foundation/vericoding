use vstd::prelude::*;

verus! {

//ATOM
#[verifier::external_body]
fn add(a: i32, b: i32) -> (result: i32)
    ensures
        result == a + b,
{
    return 0;  // TODO: Remove this line and implement the function body
}

//IMPL cubes
#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) 
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
{
    /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
    let mut result = Vec::new();
    let mut idx = 0;
    
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