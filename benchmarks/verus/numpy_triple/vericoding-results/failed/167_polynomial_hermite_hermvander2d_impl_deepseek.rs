// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix indexing to use usize instead of int in ghost contexts */
fn hermvander1d(w: Vec<i8>, deg: usize) -> (v: Vec<i8>)
    requires w.len() > 0
    ensures v.len() == (deg + 1) * w.len(),
            forall|k: int| 0 <= k < w.len() ==> v@[k * (deg + 1)] as int == 1
{
    let n = w.len();
    let mut v = Vec::<i8>::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            v.len() == i * (deg + 1),
            forall|k: int| 0 <= k < i ==> v@[k * (deg + 1)] as int == 1
    {
        v.push(1);
        let mut j: usize = 1;
        while j <= deg
            invariant
                1 <= j <= deg + 1,
                v.len() == i * (deg + 1) + j,
                v@[i * (deg + 1)] as int == 1
        {
            let t = w@[i] as i16;
            let hermite_val = if j == 1 {
                2 * t
            } else {
                2 * t * (v@[i * (deg + 1) + j - 1] as i16) - 2 * (j - 1) as i16 * (if j > 1 { v@[i * (deg + 1) + j - 2] as i16 } else { 0 })
            };
            v.push(hermite_val as i8);
            j += 1;
        }
        i += 1;
    }
    v
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
/* code modified by LLM (iteration 5): Fix indexing to use usize instead of int in ghost contexts */
{
    let m = x.len();
    let xv = hermvander1d(x, xdeg);
    let yv = hermvander1d(y, ydeg);
    
    let mut result = Vec::<Vec<i8>>::new();
    let mut k: usize = 0;
    while k < m
        invariant
            result.len() == k,
            forall|i: int| 0 <= i < k ==> result@[i].len() == (xdeg + 1) * (ydeg + 1),
            forall|i: int| 0 <= i < k ==> result@[i]@[0] as int == 1
    {
        let mut row = Vec::<i8>::new();
        let mut i: usize = 0;
        while i <= xdeg
            invariant
                row.len() == i * (ydeg + 1),
                i <= xdeg + 1
        {
            let mut j: usize = 0;
            while j <= ydeg
                invariant
                    row.len() == i * (ydeg + 1) + j,
                    j <= ydeg + 1
            {
                let x_index = k * (xdeg + 1) + i;
                let y_index = k * (ydeg + 1) + j;
                let val = xv@[x_index] as i16 * yv@[y_index] as i16;
                row.push(val as i8);
                j += 1;
            }
            i += 1;
        }
        result.push(row);
        k += 1;
    }
    result
}
// </vc-code>

}
fn main() {}