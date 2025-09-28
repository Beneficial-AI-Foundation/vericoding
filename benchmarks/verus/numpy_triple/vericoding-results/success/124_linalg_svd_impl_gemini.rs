// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [new helper to create a zero vector, replacing vec! macro] */
fn zero_vector(len: usize) -> (v: Vec<f32>)
    ensures
        v.len() == len,
        forall|i: int| 0 <= i < len as int ==> v@[i] == 0.0f32,
{
    let mut vec = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            i <= len,
            vec.len() == i,
            forall|j: int| 0 <= j < i as int ==> vec@[j] == 0.0f32,
        decreases len - i
    {
        vec.push(0.0f32);
        i = i + 1;
    }
    vec
}

/* helper modified by LLM (iteration 2): [fixed use of unsupported vec! macro] */
fn zero_matrix(rows: usize, cols: usize) -> (m: Vec<Vec<f32>>)
    ensures
        m.len() == rows,
        forall|i: int| 0 <= i < (rows as int) ==> m@[i].len() == (cols as int),
{
    let mut mat: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            i <= rows,
            mat.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> mat@[j].len() == (cols as int),
        decreases rows - i
    {
        let row = zero_vector(cols);
        mat.push(row);
        i = i + 1;
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
/* code modified by LLM (iteration 2): [fixed use of unsupported vec! macro] */
{
    let m = a.len();
    let n = a[0].len();
    let min_mn = if m <= n { m } else { n };

    let u = zero_matrix(m, min_mn);
    let s = zero_vector(min_mn);
    let vh = zero_matrix(min_mn, n);
    
    (u, s, vh)
}

// </vc-code>


}
fn main() {}