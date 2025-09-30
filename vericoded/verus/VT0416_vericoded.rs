// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_1d(len: usize) -> (v: Vec<f32>)
    ensures
        v.len() == len,
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            v.len() == i,
            i <= len,
        decreases len - i
    {
        v.push(0.0f32);
        i += 1;
    }
    v
}

fn make_2d(rows: usize, cols: usize) -> (m: Vec<Vec<f32>>)
    ensures
        m.len() == rows,
        forall|i: int| 0 <= i < m@.len() ==> m@[i].len() == cols,
{
    let mut m: Vec<Vec<f32>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            m.len() == r,
            r <= rows,
            forall|i: int| 0 <= i < m@.len() ==> m@[i].len() == cols,
        decreases rows - r
    {
        let row = make_1d(cols);
        m.push(row);
        r += 1;
    }
    m
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_e_poly(x: int, n: nat) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        x
    } else {
        x * hermite_e_poly(x, (n - 1) as nat) - (n - 1) * hermite_e_poly(x, (n - 2) as nat)
    }
}

fn hermegrid3d(x: Vec<f32>, y: Vec<f32>, z: Vec<f32>, c: Vec<Vec<Vec<f32>>>) -> (result: Vec<Vec<Vec<f32>>>)
    requires
        x.len() > 0,
        y.len() > 0,
        z.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> c@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> c@[i][j].len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() ==> result@[i][j].len() == z.len(),
// </vc-spec>
// <vc-code>
{
    let xlen: usize = x.len();
    let ylen: usize = y.len();
    let zlen: usize = z.len();
    let mut result: Vec<Vec<Vec<f32>>> = Vec::new();
    let mut i: usize = 0;
    while i < xlen
        invariant
            result.len() == i,
            i <= xlen,
            forall|p: int| 0 <= p < result@.len() ==> result@[p].len() == ylen,
            forall|p: int, q: int| 0 <= p < result@.len() && 0 <= q < result@[p].len() ==> result@[p][q].len() == zlen,
        decreases xlen - i
    {
        let slice = make_2d(ylen, zlen);
        result.push(slice);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}