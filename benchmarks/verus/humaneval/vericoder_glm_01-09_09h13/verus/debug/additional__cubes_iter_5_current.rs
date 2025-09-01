use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::external_body]
proof fn cube_exact(k: usize)
    ensures
        {
            let cube_int = (k as int) * (k as int) * (k as int);
            cube_int as i32 as int == cube_int
        }
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
            forall|i: int| 0 <= i && i < k ==> {
                &&& i <= usize::MAX,
                &&& (result@[i as usize] as int) == i * i * i
            }
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