// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add decreases clause to fix compilation error */
fn compute_hermite_polynomial(n: usize, t: i8) -> (result: i8)
    ensures result as int == hermite_polynomial(n as nat, t as int)
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        2 * t
    } else {
        let h_n_minus_1 = compute_hermite_polynomial(n - 1, t);
        let h_n_minus_2 = compute_hermite_polynomial(n - 2, t);
        2 * t * h_n_minus_1 - 2 * (n as i8 - 1) * h_n_minus_2
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

fn hermvander2d(x: Vec<i8>, y: Vec<i8>, xdeg: usize, ydeg: usize) -> (result: Vec<Vec<i8>>)
    requires x.len() == y.len(),
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result@[k].len() == (xdeg + 1) * (ydeg + 1),
        forall|k: int| 0 <= k < result.len() ==> #[trigger] result@[k]@[0] as int == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add decreases clause to outer while loop */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k].len() == (xdeg + 1) * (ydeg + 1),
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k]@[0] as int == 1,
        decreases x.len() - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j = 0;
        while j <= xdeg
            invariant
                j <= xdeg + 1,
                row.len() == j * (ydeg + 1),
                j == 0 || row@[0] as int == 1,
            decreases xdeg + 1 - j
        {
            let mut k = 0;
            while k <= ydeg
                invariant
                    k <= ydeg + 1,
                    row.len() == j * (ydeg + 1) + k,
                    j == 0 && k == 0 ==> row.len() == 0,
                    j == 0 && k == 1 ==> row.len() == 1 && row@[0] as int == 1,
                    j > 0 || k > 0 ==> row.len() > 0,
                    row.len() > 0 ==> row@[0] as int == 1,
                decreases ydeg + 1 - k
            {
                let herm_x = compute_hermite_polynomial(j, x[i]);
                let herm_y = compute_hermite_polynomial(k, y[i]);
                let value = herm_x * herm_y;
                row.push(value);
                k += 1;
            }
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}