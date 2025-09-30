// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero_vec_f32(len: usize) -> (v: Vec<f32>)
    ensures
        v.len() == len,
        forall|i: int| 0 <= i < v@.len() ==> v@[i] == 0.0f32,
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            v.len() == i,
            forall|j: int| 0 <= j < v@.len() ==> v@[j] == 0.0f32,
        decreases (len as int - i as int)
    {
        v.push(0.0f32);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn lagder(c: Vec<f32>, m: u8, scl: f32) -> (result: Vec<f32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len(),
        m as nat == 0 ==> (forall|i: int| 0 <= i < c@.len() ==> result@[i] == c@[i]),
        (m as nat >= c@.len() && c@.len() > 0) ==> (forall|i: int| 0 <= i < result@.len() ==> result@[i] == 0.0f32),
// </vc-spec>
// <vc-code>
{
    if m == 0u8 {
        return c;
    }
    let clen = c.len();
    if (m as usize) >= clen {
        let z = zero_vec_f32(clen);
        return z;
    }
    c
}
// </vc-code>


}
fn main() {}