use vstd::prelude::*;

verus! {

// <vc-helpers>
fn make_cubes(n: usize) -> Vec<i32>
    decreases n
    ensures
        result.len() == n,
        forall|i: int| 0 <= i && i < n as int ==> result[i as usize] == i * i * i
{
    if n == 0 {
        Vec::new()
    } else {
        let mut v = make_cubes(n - 1);
        proof {
            assert(v.len() == n - 1);
            assert(forall|j: int| 0 <= j && j < (n - 1) as int ==>
                v[j as usize] == j * j * j);
        }
        let ii: int = (n - 1) as int;
        let val_int: int = ii * ii * ii;
        v.push(val_int as i32);
        v
    }
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
    make_cubes(len)
    // impl-end
}
// </vc-code>

fn main() {}
}