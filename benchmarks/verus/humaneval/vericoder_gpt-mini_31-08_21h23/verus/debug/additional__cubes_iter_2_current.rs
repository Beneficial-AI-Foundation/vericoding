use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let mut i: usize = 0;
    while i < len
        invariant v.len() == i,
        invariant forall|j: int| 0 <= j && j < i as int ==> (v[j as usize] as int) == j * j * j
    {
        let ii: int = i as int;
        // compute cube as mathematical int, then cast to i32 for storage
        let val_int: int = ii * ii * ii;
        v.push(val_int as i32);
        i += 1;
    }
    v
    // impl-end
}
// </vc-code>

fn main() {}
}