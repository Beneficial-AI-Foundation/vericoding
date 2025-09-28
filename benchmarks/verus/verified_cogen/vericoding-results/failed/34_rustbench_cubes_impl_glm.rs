// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): kept lemma as is because it is still needed */
proof fn lemma_cube_in_bounds(i: int)
    requires 0 <= i <= 1290
    ensures ((i as i32) * (i as i32) * (i as i32)) == i * i * i
{
    assert((1290 as i32) * (1290 as i32) * (1290 as i32) == 2146689000);
    assert(2146689000 <= i32::MAX);
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn cubes(len: usize) -> (result: Vec<i32>) by (nonlinear_arith)
    ensures
        result.len() == len,
        forall|i: int| 0 <= i && i < len ==> result[i] == i * i * i
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added assertion for len<=1290 and removed i<=1290 invariant */
{
    assert(len <= 1290);
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == j * j * j
        decreases (len - i) as int
    {
        proof {
            lemma_cube_in_bounds(i as int);
        }
        let cube = (i as i32) * (i as i32) * (i as i32);
        result.push(cube);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}