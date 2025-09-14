// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use spec conversion for int computation */
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            v.len() == i,
            forall|j: int| 0 <= j && j < i ==> v[j] == j * j * j,
            i <= len
        decreases len - i
    {
        let cube_value = i * i * i;
        v.push(cube_value as i32);
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}