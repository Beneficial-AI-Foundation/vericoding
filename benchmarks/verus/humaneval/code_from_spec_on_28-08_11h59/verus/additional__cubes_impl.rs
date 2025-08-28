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
    let mut i: usize = 0;
    while i < len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result@[j] == j * j * j,
            i <= len,
            i < 1291
        decreases len - i
    {
        proof {
            assert(i < 1291);
            assert((i as i32) < 1291);
            assert((i as i32) * (i as i32) <= 1666681);
            assert((i as i32) * (i as i32) * (i as i32) <= 2147395841);
            assert((i as i32) * (i as i32) * (i as i32) < 2147483648);
        }
        let cube = (i as i32) * (i as i32) * (i as i32);
        result.push(cube);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}