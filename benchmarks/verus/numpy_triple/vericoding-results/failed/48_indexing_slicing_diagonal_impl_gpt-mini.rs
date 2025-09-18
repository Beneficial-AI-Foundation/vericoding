// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute diagonal length as usize */
fn diagonal_len(n: usize, m: usize, offset: i32) -> usize {
    if offset >= 0 {
        let off = offset as usize;
        if n <= m - off { n } else { m - off }
    } else {
        let off = (-offset) as usize;
        if n + off <= m { n + off } else { m }
    }
}
// </vc-helpers>

// <vc-spec>
fn diagonal(a: Vec<Vec<f64>>, offset: i32) -> (result: Vec<f64>)
    requires 
        a.len() > 0,
        a.len() > 0 ==> a[0].len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a[0].len(),
        if offset >= 0 { 
            offset as int <= a[0].len() as int
        } else { 
            (-offset) as int <= a.len() as int
        },
    ensures
        result.len() == (if offset >= 0 { 
            if a.len() as int <= (a[0].len() as int - offset as int) { a.len() as int } else { a[0].len() as int - offset as int }
        } else { 
            if (a.len() as int + (-offset) as int) <= a[0].len() as int { a.len() as int + (-offset) as int } else { a[0].len() as int }
        }) as usize,
        forall|i: int| 0 <= i < result.len() ==> {
            if offset >= 0 {
                #[trigger] result[i] == a[i][i + offset as int]
            } else {
                #[trigger] result[i] == a[i + (-offset) as int][i]
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct diagonal using usize indices and helper */
    let n = a.len();
    let m = a[0].len();
    let res_len = diagonal_len(n, m, offset);
    let mut res: Vec<f64> = Vec::with_capacity(res_len);
    let mut k: usize = 0;
    while k < res_len
        invariant k <= res_len;
        invariant res.len() == k;
        invariant forall|j: int| 0 <= j && j < k as int ==> {
            if offset >= 0 {
                res[j as usize] == a[j as usize][j as usize + offset as usize]
            } else {
                res[j as usize] == a[j as usize + (-offset) as usize][j as usize]
            }
        };
        decreases res_len - k;
    {
        if offset >= 0 {
            res.push(a[k][k + offset as usize]);
        } else {
            res.push(a[k + (-offset) as usize][k]);
        }
        k += 1;
    }
    res
}
// </vc-code>

}
fn main() {}