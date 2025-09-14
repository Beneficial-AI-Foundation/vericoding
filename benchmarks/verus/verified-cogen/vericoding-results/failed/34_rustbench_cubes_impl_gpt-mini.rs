// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec cube_i returning cube of int */
spec fn cube_i(i: int) -> int { i * i * i }
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
    /* code modified by LLM (iteration 5): build vector using i32 arithmetic to avoid ghost int in runtime */
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            v.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> v@[j] == (cube_i(j) as i32),
        decreases
            len - i
    {
        let ii: i32 = i as i32;
        let val: i32 = ii * ii * ii;
        v.push(val);
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}