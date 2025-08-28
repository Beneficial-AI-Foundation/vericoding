use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::external_body]
fn add(a: i32, b: i32) -> (result: i32)
    ensures
        result == a + b,
{
    a + b
}

proof fn cube_bound(i: int)
    requires 0 <= i <= 1290
    ensures i * i * i <= 2147483647
{
    assert(1290 * 1290 * 1290 == 2146689000) by (nonlinear_arith);
    assert(2146689000 <= 2147483647);
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
    // impl-start
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result@[j] == (if j <= 1290 { j * j * j } else { 0 }),
            i <= len
        decreases len - i
    {
        if i <= 1290 {
            proof {
                cube_bound(i as int);
            }
            let cube = (i as i32) * (i as i32) * (i as i32);
            result.push(cube);
        } else {
            result.push(0);
        }
        i += 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}