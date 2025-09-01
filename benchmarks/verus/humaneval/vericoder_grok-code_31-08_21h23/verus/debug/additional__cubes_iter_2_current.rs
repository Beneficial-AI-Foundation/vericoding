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
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            v.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> v@[j] == (j as i32) * (j as i32) * (j as i32),
            i <= len,
    {
        let cube_val: i32 = (i as i32) * (i as i32) * (i as i32);
        v.push(cube_val);
        i = i + 1;
    }
    return v;
}
// </vc-code>

fn main() {}
}