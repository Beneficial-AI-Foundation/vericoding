// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): helper to build a row with correct length and initial values */
fn make_row(xi: f32, deg: usize) -> (row: Vec<f32>)
    ensures
        row@.len() == deg + 1,
        row@[0] == 1.0f32,
        deg > 0 ==> row@[1] == xi,
{
    let mut r: Vec<f32> = Vec::new();
    r.push(1.0f32);
    if deg > 0 {
        r.push(xi);
        let mut k: usize = 1;
        while k < deg
            invariant
                r@.len() == (k as int) + 1,
                r@[0] == 1.0f32,
                deg > 0 ==> r@[1] == xi,
                1 <= (k as int) <= (deg as int),
            decreases deg - k
        {
            r.push(0.0f32);
            k = k + 1;
        }
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn legvander(x: Vec<f32>, deg: usize) -> (result: Vec<Vec<f32>>)
    requires x@.len() > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == deg + 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i][0] == 1.0f32,
        deg > 0 ==> forall|i: int| 0 <= i < result@.len() ==> result@[i][1] == x@[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): strengthen loop invariants and prove safe indexing into x */
{
    let n: usize = x.len();
    let mut res: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res@.len() == i as int,
            i <= n,
            n == x.len(),
            (i as int) <= x@.len(),
            forall|j: int| 0 <= j < res@.len() ==> res@[j].len() == deg + 1,
            forall|j: int| 0 <= j < res@.len() ==> res@[j][0] == 1.0f32,
            deg > 0 ==> forall|j: int| 0 <= j < res@.len() ==> res@[j][1] == x@[j],
        decreases n - i
    {
        assert(i < n);
        assert(n == x.len());
        assert(x@.len() == x.len() as int);
        assert((i as int) < x@.len());
        let xi: f32 = x[i];
        assert(x@[i as int] == xi);
        let row = make_row(xi, deg);
        res.push(row);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}