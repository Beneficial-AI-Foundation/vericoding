// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate Vec len to sequence view length */
proof fn vec_len_view_eq(c: &Vec<f32>)
    ensures
        (c.len() as int) == c@.len(),
{
    assert((c.len() as int) == c@.len());
}

/* helper modified by LLM (iteration 5): convert a usize < bound into an int < bound */
proof fn usize_lt_to_int_lt(i: usize, c: &Vec<f32>)
    requires
        i < c.len(),
    ensures
        (i as int) < c@.len(),
{
    vec_len_view_eq(c);
    assert((i as int) < (c.len() as int));
    assert((c.len() as int) == c@.len());
    assert((i as int) < c@.len());
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
    /* code modified by LLM (iteration 5): build result by pushing zero then each coefficient with invariants ensuring result[0]==0.0 and mapping coefficients */
    let mut result: Vec<f32> = Vec::new();
    result.push(0.0f32);
    let mut i: usize = 0;
    while i < c.len()
        invariant
            result.len() == i + 1,
            result@[0] == 0.0f32,
            forall |k: int| 0 <= k < (i as int) ==> result@[k + 1] == c@[k],
            i <= c.len(),
        decreases c.len() - i,
    {
        let x: f32 = c[i];
        result.push(x);
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}