// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): avoid negation overflow by widening to i64 before negation */
fn diag_col(r: usize, offset: i32) -> (opt: Option<usize>) {
    if offset >= 0 {
        let off = offset as usize;
        match r.checked_add(off) {
            Some(c) => Some(c),
            None => None,
        }
    } else {
        let off_i64: i64 = -(offset as i64);
        let off: usize = off_i64 as usize;
        if r >= off {
            Some(r - off)
        } else {
            None
        }
    }
}

fn get2d(a: &Vec<Vec<f32>>, r: usize, c: usize) -> (res: Option<f32>) {
    if r < a.len() {
        let row = &a[r];
        if c < row.len() {
            Some(row[c])
        } else {
            None
        }
    } else {
        None
    }
}
// </vc-helpers>

// <vc-spec>
fn trace(a: Vec<Vec<f32>>, offset: i32) -> (result: f32)
    ensures true
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): iterate rows and sum elements on the specified diagonal using safe column computation */
    let mut sum: f32 = 0.0;
    let n = a.len();
    let mut r: usize = 0;
    while r < n
        invariant
            r <= n,
        decreases n - r
    {
        match diag_col(r, offset) {
            Some(c) => {
                match get2d(&a, r, c) {
                    Some(v) => { sum += v; }
                    None => { }
                }
            }
            None => { }
        }
        r += 1;
    }
    sum
}
// </vc-code>


}
fn main() {}