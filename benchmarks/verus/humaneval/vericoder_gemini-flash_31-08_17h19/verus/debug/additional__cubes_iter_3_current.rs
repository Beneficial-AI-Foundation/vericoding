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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|k: int| 0 <= k && (k as usize) < i ==> result[k as usize] == k * k * k,
    {
        let val: i32 = (i as i32) * (i as i32) * (i as i32);
        proof {
            assert((i as i32) * (i as i32) * (i as i32) == (i * i * i) as i32); // This assertion helps Verus understand the relationship between i as i32 and i
        }
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}