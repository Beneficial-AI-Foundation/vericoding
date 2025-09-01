use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == j * j * j,
        decreases len - i,
    {
        let cube = (i as i32) * (i as i32) * (i as i32);
        result.push(cube);
        
        assert(result.len() == i + 1);
        assert(result[i as int] == (i as i32) * (i as i32) * (i as i32));
        assert(forall|j: int| 0 <= j && j < i ==> result[j] == j * j * j);
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}