// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add executable hermite function matching spec */
fn hermite(n: usize, t: i8) -> (res: i8)
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        2 * t
    } else {
        2 * t * hermite(n - 1, t) - 2 * ((n - 1) as i8) * hermite(n - 2, t)
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
/* code modified by LLM (iteration 2): fix indexing to use exec syntax, remove assume */
{
    let mut result = Vec::<Vec<i8>>::new();
    let xlen = x.len();
    let mut k = 0;
    while k < xlen
        invariant
            k >= 0,
            k <= xlen,
            result.len() == k,
            forall|ii: int| 0 <= ii < k ==> #[trigger] result@[ii].len() == (xdeg + 1) * (ydeg + 1),
        decreases xlen - k
    {
        let mut row = Vec::<i8>::new();
        let mut i = 0;
        let xdeg1 = xdeg + 1;
        let ydeg1 = ydeg + 1;
        while i < xdeg1
            invariant
                i >= 0,
                i <= xdeg1,
                row.len() == i * ydeg1,
            decreases xdeg1 - i
        {
            let hx = hermite(i, x[k]);
            let mut j = 0;
            while j < ydeg1
                invariant
                    j >= 0,
                    j <= ydeg1,
                decreases ydeg1 - j
            {
                let hy = hermite(j, y[k]);
                row.push(hx * hy);
                j = j + 1;
            }
            i = i + 1;
        }
        result.push(row);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}