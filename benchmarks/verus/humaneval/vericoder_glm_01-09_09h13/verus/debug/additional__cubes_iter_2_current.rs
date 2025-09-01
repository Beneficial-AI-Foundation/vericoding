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
    for k in 0..len
        invariant
            k <= len,
            result.len() == k,
            forall|i: int| 0 <= i < (k as int) ==> result@[i] == i * i * i
    {
        let cube = (k as i32) * (k as i32) * (k as i32);
        result.push(cube);
        assert(result@[k as int] == cube);
        assert(cube == (k as int) * (k as int) * (k as int));
    }
    result
}
// </vc-code>

fn main() {}
}