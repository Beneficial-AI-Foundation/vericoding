use vstd::prelude::*;

verus! {

// <vc-helpers>
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
    let mut v = Vec::<i32>::with_capacity(len);
    let mut i: usize = 0;

    while i < len
        invariant
            v.view().len() == i as int,
            forall|#[trigger] j: int| 0 <= j && j < i as int ==> v.view()[j] == (j as i32) * (j as i32) * (j as i32),
            i <= len,
        decreases
            len - i,
    {
        v.push((i as i32) * (i as i32) * (i as i32));
        i += 1;
    }

    v
}
// </vc-code>

fn main() {}
}