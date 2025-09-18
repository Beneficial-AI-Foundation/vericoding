// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): build a zero-filled row of given length using a simple loop with invariants */
fn zeros_row(len: usize) -> (row: Vec<i32>)
    ensures row.len() == len
{
    let mut r: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            r.len() == i,
            i <= len
        decreases len - i
    {
        r.push(0i32);
        i = i + 1;
    }
    assert(r.len() == len);
    r
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_basis(k: nat, t: int) -> int
    decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        t * hermite_basis((k - 1) as nat, t) - (k - 1) as int * hermite_basis((k - 2) as nat, t)
    }
}

fn hermevander2d(x: Vec<i32>, y: Vec<i32>, x_deg: usize, y_deg: usize) -> (result: Vec<Vec<i32>>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|point_idx: int| 0 <= point_idx < result.len() ==> 
            result[point_idx].len() == (x_deg + 1) * (y_deg + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build zero-filled matrix with per-row length (x_deg+1)*(y_deg+1) using loops and invariants */
    let n = x.len();
    let prod: usize = (x_deg + 1) * (y_deg + 1);
    let mut res: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            i <= n,
            forall|k: int| 0 <= k && k < res.len() ==> res[k].len() == prod
        decreases n - i
    {
        let row = zeros_row(prod);
        assert(row.len() == prod);
        res.push(row);
        i = i + 1;
    }
    assert(res.len() == n);
    res
}
// </vc-code>

}
fn main() {}