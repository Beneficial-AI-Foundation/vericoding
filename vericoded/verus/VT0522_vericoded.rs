// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma relating Vec length and Seq length */
proof fn vec_len_agrees<T>(v: &Vec<T>)
    ensures
        v@.len() == v.len() as int,
{
}

// </vc-helpers>

// <vc-spec>
fn polymulx(c: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0f32,
        forall|i: int| 0 <= i < c@.len() ==> result[i + 1] == c[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate with usize index to avoid casts from int; maintain invariants over j as int */
    let mut result: Vec<f32> = Vec::new();
    result.push(0.0f32);
    let mut j: usize = 0usize;
    while j < c.len()
        invariant
            0 <= j as int <= c@.len(),
            result@.len() == j as int + 1,
            result.len() == j + 1usize,
            result@[0] == 0.0f32,
            forall|k: int| 0 <= k < j as int ==> result@[k + 1] == c@[k],
        decreases c@.len() as int - j as int
    {
        let v = c[j];
        result.push(v);
        j = j + 1usize;
    }
    result
}
// </vc-code>

}
fn main() {}