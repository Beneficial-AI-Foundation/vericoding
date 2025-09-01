use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    // impl-start
    let mut v: Vec<i32> = Vec::new();

    while v.len() < len
        invariant { v.len() <= len }
        invariant { forall |i: int| 0 <= i && i < (v.len() as int) ==> (v[i] as int) == i * i * i }
        decreases (len - v.len())
    {
        let k_usize: usize = v.len();
        let k_int: int = k_usize as int;
        let cube: int = k_int * k_int * k_int;
        v.push((cube) as i32);
        // show the newly pushed element satisfies the property
        assert((v[k_usize] as int) == cube);
    }

    v
    // impl-end
}
// </vc-code>

fn main() {}
}