use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for HELPERS; leaving empty.
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
    let ghost len_int: int = len as int;
    let mut v = Vec::<i32>::with_capacity(len as usize);
    let mut i: usize = 0;

    while i < len
        invariant
            v.view().len() == i as int,
            forall|j: int| 0 <= j && j < i as int ==> v.view()[j] == (j as i32) * (j as i32) * (j as i32),
            i <= len,
    {
        v.push((i as i32) * (i as i32) * (i as i32));
        i += 1;
    }

    assert(v.view().len() == len as int);
    proof {
        assert forall|i: int| 0 <= i && i < len as int implies v.view()[i] == (i as i32) * (i as i32) * (i as i32) by {
            assert(i < len as int);
        }
    }

    v
}
// </vc-code>

fn main() {}
}