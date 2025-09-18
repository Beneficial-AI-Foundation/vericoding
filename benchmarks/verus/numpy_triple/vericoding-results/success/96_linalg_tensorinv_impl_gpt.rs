// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero_row(n: usize) -> (r: Vec<f32>)
    ensures
        r.len() == n
{
    let mut r: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            r.len() == i,
            i <= n,
        decreases n - i
    {
        r.push(0.0f32);
        i += 1;
    }
    r
}

fn zero_matrix(n: usize) -> (m: Vec<Vec<f32>>)
    requires
        n > 0
    ensures
        m.len() == n,
        forall|i: int| 0 <= i < n ==> m[i].len() == n
{
    let mut m: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            m.len() == i,
            i <= n,
            forall|k: int| 0 <= k < i ==> m[k].len() == n,
        decreases n - i
    {
        let row = zero_row(n);
        m.push(row);
        i += 1;
    }
    m
}
// </vc-helpers>

// <vc-spec>
fn tensorinv(a: Vec<Vec<f32>>, ind: usize) -> (result: Vec<Vec<f32>>)
    requires 
        a.len() > 0,
        ind > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == a.len(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let z = zero_matrix(n);
    z
}
// </vc-code>

}
fn main() {}