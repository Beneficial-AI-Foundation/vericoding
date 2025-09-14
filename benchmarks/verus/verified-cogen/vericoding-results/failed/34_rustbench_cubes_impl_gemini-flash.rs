// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused import */
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced `reserve_exact` with `reserve_at_least` for Verus compatibility. */
{
    let mut v: Vec<i32> = Vec::new();
    v.reserve_at_least(len);
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i && i <= len as int,
            v.len() == i,
            v.capacity() >= len,
            forall|j: int| 0 <= j && j < i ==> v[j] == j * j * j
    {
        v.push((i as i32) * (i as i32) * (i as i32));
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}