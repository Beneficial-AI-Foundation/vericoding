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
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len {
        invariant
            res.len() == i
            forall |j: int| 0 <= j && j < (i as int) ==> #[trigger] (res[j as usize] == j * j * j)
        {
            let cube = (i as i32) * (i as i32) * (i as i32);
            res.push(cube);
            i += 1;
        }
    }
    res
}
// </vc-code>

fn main() {}
}