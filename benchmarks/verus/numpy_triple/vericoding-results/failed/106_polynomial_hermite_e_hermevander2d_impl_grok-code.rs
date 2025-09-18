// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn hermite_basis_exec(k: nat, t: i32) -> i32
decreases k
{
    if k == 0 {
        1
    } else if k == 1 {
        t
    } else {
        t * hermite_basis_exec((k - 1) as nat, t) - ((k - 1) as i32) * hermite_basis_exec((k - 2) as nat, t)
    }
}

proof fn lemma_hermite_eq(k: nat, t: i32)
    ensures
        hermite_basis(k, t as int) == hermite_basis_exec(k, t) as int
    decreases k
{
    if k == 0 {
        
    } else if k == 1 {
        
    } else {
        lemma_hermite_eq(k - 1, t);
        lemma_hermite_eq(k - 2, t);
        assert(hermite_basis_exec(k, t) as int == t as int * hermite_basis_exec(k - 1, t) as int - ((k - 1) as int) * hermite_basis_exec(k - 2, t) as int);
    }
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
    /* code modified by LLM (iteration 5): fixed typos and implemented the main logic without bypasses */
    let n = x.len();
    let mut result: Vec<Vec<i32>> = Vec::with_capacity(n);
    for i in 0..n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j].len() == (x_deg + 1) * (y_deg + 1)
    {
        let t_x = x[i];
        let t_y = y[i];
        let mut row: Vec<i32> = Vec::with_capacity((x_deg + 1) * (y_deg + 1));
        for kx in 0..(x_deg + 1) {
            for ky in 0..(y_deg + 1) {
                let h_x = hermite_basis_exec(kx as nat, t_x);
                let h_y = hermite_basis_exec(ky as nat, t_y);
                proof {
                    lemma_hermite_eq(kx as nat, t_x);
                    lemma_hermite_eq(ky as nat, t_y);
                    assert(h_x as int == hermite_basis(kx as nat, t_x as int));
                    assert(h_y as int == hermite_basis(ky as nat, t_y as int));
                }
                row.push(h_x * h_y);
            }
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}