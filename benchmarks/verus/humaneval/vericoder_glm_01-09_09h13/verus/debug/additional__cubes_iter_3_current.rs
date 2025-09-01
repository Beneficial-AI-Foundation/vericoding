use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::external_body]
proof fn cube_exact(k: usize)
    ensures
        let cube = (k as int) * (k as int) * (k as int);
        cube as i32 == cube
{
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
    for k in 0..len
        invariant
            k <= len,
            result.len() == k,
            forall|i: usize| i < k ==> result@[i] == (i as int) * (i as int) * (i as int)
    {
        let cube_int = (k as int) * (k as int) * (k as int);
        let cube = cube_int as i32;
        proof {
            cube_exact(k);
        }
        result.push(cube);
    }
    result
}
// </vc-code>

fn main() {}
}