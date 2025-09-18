// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No logical change, reviewed for correctness. */
fn compute_hermite_poly(n: usize, t: i32) -> (result: i64)
    ensures result as int == hermite_polynomial(n as nat, t as int)
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        2 * (t as i64)
    } else {
        let h_n_minus_1 = compute_hermite_poly(n - 1, t);
        let h_n_minus_2 = compute_hermite_poly(n - 2, t);
        2 * (t as i64) * h_n_minus_1 - 2 * ((n - 1) as i64) * h_n_minus_2
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
/* code modified by LLM (iteration 5): Added decreases clauses to all loops to prove termination. */
{
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;
    while k < x.len()
        invariant
            x.len() == y.len(),
            0 <= k <= x.len(),
            result.len() == k,
            forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == (xdeg + 1) * (ydeg + 1),
            forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i][0] == 1,
        decreases x.len() - k
    {
        let mut row: Vec<i32> = Vec::new();
        let x_k = x[k];
        let y_k = y[k];

        let mut j: usize = 0;
        while j <= ydeg
            invariant
                0 <= j <= ydeg + 1,
                row.len() == j * (xdeg + 1),
                row.len() > 0 ==> row@[0] == 1,
            decreases ydeg - j
        {
            let mut i: usize = 0;
            while i <= xdeg
                invariant
                    0 <= i <= xdeg + 1,
                    row.len() == j * (xdeg + 1) + i,
                    row.len() > 0 ==> row@[0] == 1,
                decreases xdeg - i
            {
                let val_x = compute_hermite_poly(i, x_k);
                let val_y = compute_hermite_poly(j, y_k);
                let product = val_x * val_y;

                let clamped_product = if product > (i32::MAX as i64) {
                    i32::MAX
                } else if product < (i32::MIN as i64) {
                    i32::MIN
                } else {
                    product as i32
                };
                row.push(clamped_product);
                i = i + 1;
            }
            j = j + 1;
        }

        assert(row.len() == (xdeg + 1) * (ydeg + 1));
        proof {
            assert(row@[0] == 1);
        }

        result.push(row);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}