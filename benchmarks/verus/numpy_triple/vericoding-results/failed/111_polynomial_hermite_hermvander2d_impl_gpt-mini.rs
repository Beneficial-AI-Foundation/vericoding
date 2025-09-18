// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): hermite polynomial for i32 */
fn hermite_i32(n: nat, t: i32) -> i32
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        2 * t
    } else {
        2 * t * hermite_i32(n - 1, t) - 2 * ((n - 1) as i32) * hermite_i32(n - 2, t)
    }
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_polynomial(n: nat, t: int) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        2 * t
    } else {
        2 * t * hermite_polynomial((n - 1) as nat, t) - 2 * (n - 1) * hermite_polynomial((n - 2) as nat, t)
    }
}

fn hermvander2d(x: Vec<i32>, y: Vec<i32>, xdeg: usize, ydeg: usize) -> (result: Vec<Vec<i32>>)
    requires x.len() == y.len(),
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == (xdeg + 1) * (ydeg + 1),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k][0] == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build hermvander2d using hermite_i32 with loop invariants */
    let m = x.len();
    let cols = (xdeg + 1) * (ydeg + 1);
    let mut result: Vec<Vec<i32>> = Vec::new();

    let mut k: usize = 0;
    while k < m
        invariant k <= m,
        invariant result.len() == k,
        invariant forall|i: int| 0 <= i < (result.len() as int) ==> result[i as usize].len() == cols,
        invariant forall|i: int| 0 <= i < (result.len() as int) ==> result[i as usize][0] == 1
    {
        let xi = x[k];
        let yi = y[k];
        let mut row: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < cols
            invariant idx <= cols,
            invariant row.len() == idx
        {
            let i_idx = idx / (ydeg + 1);
            let j_idx = idx % (ydeg + 1);
            let hi = hermite_i32(i_idx as nat, xi);
            let hj = hermite_i32(j_idx as nat, yi);
            row.push(hi * hj);
            idx += 1;
        }
        proof {
            assert(row.len() == cols);
            assert(row[0] == hermite_i32(0, xi) * hermite_i32(0, yi));
            assert(hermite_i32(0, xi) == 1);
            assert(hermite_i32(0, yi) == 1);
            assert(row[0] == 1);
        }
        result.push(row);
        k += 1;
    }

    result
}
// </vc-code>

}
fn main() {}