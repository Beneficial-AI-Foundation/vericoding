use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    // post-conditions-start
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == j * j * j
    {
        let cube = (i * i * i) as i32;
        result.push(cube);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}