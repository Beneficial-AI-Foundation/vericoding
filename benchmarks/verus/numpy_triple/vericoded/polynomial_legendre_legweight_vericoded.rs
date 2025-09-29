// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added missing i <= n loop invariant to prove final length equals n */
fn make_ones(n: usize) -> (v: Vec<f32>)
    ensures
        v@.len() == n as int,
        forall|i: int| 0 <= i < v@.len() ==> v@[i] == 1.0f32,
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v@.len() == i as int,
            forall|j: int| 0 <= j < v@.len() ==> v@[j] == 1.0f32,
            (i as int) <= (n as int),
        decreases n as int - i as int
    {
        v.push(1.0f32);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn legweight(x: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == 1.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Construct result using helper that makes a vector of ones with the same length as x */
    let n: usize = x.len();
    let result_vec = make_ones(n);
    result_vec
}
// </vc-code>

}
fn main() {}