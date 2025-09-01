use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    assert(len <= 1291);
    let mut i: usize = 0;
    while i < len
        invariant
            v.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> v@[j] == (j as i32) * (j as i32) * (j as i32),
            i <= len,
        decreases len - i,
    {
        let ii: int = i as int;
        let cube: int = ii * ii * ii;
        let cube_val: i32 = (i as i32) * (i as i32) * (i as i32);
        assert(cube_val as int == cube);
        v.push(cube_val);
        i = i + 1;
    }
    return v;
}
// </vc-code>

fn main() {}
}