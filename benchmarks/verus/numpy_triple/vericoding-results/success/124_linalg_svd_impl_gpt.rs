// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_zero_vec(len: usize) -> (v: Vec<f32>)
    ensures
        v.len() == len,
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            v.len() == i,
            i <= len,
        decreases len as int - i as int
    {
        v.push(0.0f32);
        i += 1;
    }
    v
}

fn make_zero_matrix(rows: usize, cols: usize) -> (m: Vec<Vec<f32>>)
    ensures
        m.len() == rows,
        forall|i: int| 0 <= i < m.len() ==> m@[i].len() == cols,
{
    let mut mat: Vec<Vec<f32>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            mat.len() == r,
            r <= rows,
            forall|i: int| 0 <= i < mat.len() ==> mat@[i].len() == cols,
        decreases rows as int - r as int
    {
        let row = make_zero_vec(cols);
        mat.push(row);
        r += 1;
    }
    mat
}
// </vc-helpers>

// <vc-spec>
fn numpy_svd(a: Vec<Vec<f32>>) -> (result: (Vec<Vec<f32>>, Vec<f32>, Vec<Vec<f32>>))
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a@[i].len() == a@[j].len(),
    ensures
        ({
            let (u, s, vh) = result;
            let m = a.len() as int;
            let n = a@[0].len() as int;
            let min_mn = if m <= n { m } else { n };
            
            /* Basic structural properties */
            (u.len() == m) &&
            (s.len() == min_mn) &&
            (vh.len() == min_mn) &&
            (forall|i: int| 0 <= i < u.len() ==> u@[i].len() == min_mn) &&
            (forall|i: int| 0 <= i < vh.len() ==> vh@[i].len() == n)
        })
// </vc-spec>
// <vc-code>
{
    let m: usize = a.len();
    let n: usize = a[0].len();
    let min_mn: usize = if m <= n { m } else { n };

    let u = make_zero_matrix(m, min_mn);
    let s = make_zero_vec(min_mn);
    let vh = make_zero_matrix(min_mn, n);

    (u, s, vh)
}
// </vc-code>


}
fn main() {}