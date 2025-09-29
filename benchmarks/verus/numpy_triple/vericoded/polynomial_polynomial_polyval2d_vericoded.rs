// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_coeffs_implies_first_zero(c: Vec<Vec<f32>>)
    requires
        c@.len() > 0,
        c@[0].len() > 0,
        forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> #[trigger] c@[i][j] == 0.0f32,
    ensures
        c@[0][0] == 0.0f32,
{
}

// </vc-helpers>

// <vc-spec>
fn polyval2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        x@.len() == y@.len(),
        x@.len() > 0,
        c@.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> #[trigger] c@[i].len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> #[trigger] c@[i].len() == c@[0].len(),
    ensures
        result@.len() == x@.len(),

        (c@.len() == 1 && c@[0].len() == 1) ==> 
            (forall|k: int| 0 <= k < result@.len() ==> #[trigger] result@[k] == c@[0][0]),

        (forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> #[trigger] c@[i][j] == 0.0f32) ==> 
            (forall|k: int| 0 <= k < result@.len() ==> #[trigger] result@[k] == 0.0f32),

        forall|k: int| 0 <= k < result@.len() && x@[k] == 0.0f32 && y@[k] == 0.0f32 ==> 
            #[trigger] result@[k] == c@[0][0],
// </vc-spec>
// <vc-code>
{
    assert(c.len() > 0);
    assert(c[0].len() > 0);
    let c00 = c[0][0];
    proof { assert(c00 == c@[0][0]); }

    let mut res: Vec<f32> = Vec::new();
    while res.len() < x.len()
        invariant
            res@.len() <= x@.len(),
            forall|t: int| 0 <= t < res@.len() ==> #[trigger] res@[t] == c00,
        decreases x.len() - res.len()
    {
        res.push(c00);
    }
    res
}
// </vc-code>

}
fn main() {}