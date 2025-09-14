// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple cube spec function for use in specifications and invariants */
spec fn cube(x: int) -> int { x * x * x }
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
    /* code modified by LLM (iteration 3): compute cubes without ghost ints in exec code */
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            v.len() == i,
            i <= len,
            forall|j: int| 0 <= j && j < i ==> v@[j] == j * j * j
        decreases len - i
    {
        let ii32: i32 = i as i32;
        let c_i32: i32 = ii32 * ii32 * ii32;
        v.push(c_i32);
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}