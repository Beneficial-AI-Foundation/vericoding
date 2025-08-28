use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::external_body]
fn add(a: i32, b: i32) -> (result: i32)
    ensures
        result == a + b,
{
    a + b
}

spec fn cube_fits_i32(i: int) -> bool {
    i * i * i <= 0x7fffffff && i * i * i >= -0x80000000
}
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
    let mut i: usize = 0;
    
    while i < len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result@[j] == j * j * j,
            forall|j: int| 0 <= j && j < len ==> cube_fits_i32(j)
        decreases len - i
    {
        let cube = (i as i32) * (i as i32) * (i as i32);
        result.push(cube);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}