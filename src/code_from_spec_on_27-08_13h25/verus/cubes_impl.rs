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

spec fn cube(n: int) -> int {
    n * n * n
}

spec fn fits_i32(n: int) -> bool {
    i32::MIN as int <= n && n <= i32::MAX as int
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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|k: int| 0 <= k && k < i ==> result[k] == cube(k),
            forall|k: int| 0 <= k && k < i ==> fits_i32(cube(k)),
        decreases
            len - i
    {
        let i32_val = i as i32;
        let val = i32_val * i32_val * i32_val;
        proof {
            assert(fits_i32(cube(i as int)) by {
                assert(i as int <= i32::MAX as int);
            });
        }
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}