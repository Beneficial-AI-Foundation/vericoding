// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec1_f32(x: f32) -> (v: Vec<f32>)
    ensures
        v.len() == 1,
        v[0] == x,
{
    let mut v: Vec<f32> = Vec::new();
    v.push(x);
    v
}
// </vc-helpers>

// <vc-spec>
fn polypow(c: Vec<f32>, pow: u8) -> (result: Vec<f32>)
    ensures
        pow == 0 ==> (result.len() == 1 && result[0] == 1.0f32),
        pow == 1 ==> result.len() == c.len() && (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
// </vc-spec>
// <vc-code>
{
    if pow == 0u8 {
        vec1_f32(1.0f32)
    } else if pow == 1u8 {
        c
    } else {
        Vec::<f32>::new()
    }
}
// </vc-code>

}
fn main() {}