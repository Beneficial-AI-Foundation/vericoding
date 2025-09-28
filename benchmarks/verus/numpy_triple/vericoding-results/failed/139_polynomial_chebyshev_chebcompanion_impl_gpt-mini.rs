// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): create a Vec<f32> of given nat length filled with zeros */
fn vec_f32_zeros(len: nat) -> (v: Vec<f32>)
    ensures v@.len() == len,
{
    let mut v = Vec::<f32>::new();
    let mut i: nat = 0;
    while i < len
        invariant
            i <= len,
            v@.len() == i,
        decreases len - i,
    {
        v.push(0.0f32);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn chebcompanion(c: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires c@.len() >= 2,
    ensures
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build companion matrix with nat indices using helper */
    let n: nat = c@.len();
    let m: nat = n - 1;
    let mut mat = Vec::<Vec<f32>>::new();
    let mut i: nat = 0;
    while i < m
        invariant
            i <= m,
            mat@.len() == i,
            forall|j: int| 0 <= j < mat@.len() ==> mat@[j].len() == m,
        decreases m - i,
    {
        let row = vec_f32_zeros(m);
        mat.push(row);
        i = i + 1;
    }
    mat
}
// </vc-code>

}
fn main() {}