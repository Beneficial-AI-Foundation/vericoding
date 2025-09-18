// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed requires/ensures from spec function */
spec fn interpolate_value(x_val: i32, xp: Vec<i32>, fp: Vec<i32>) -> i32
{
    if x_val <= xp[0] {
        fp[0]
    } else if x_val >= xp[xp.len() - 1] {
        fp[fp.len() - 1]
    } else {
        let i = choose|i: int| 0 <= i < xp.len() - 1 && xp[i] <= x_val < xp[i + 1];
        let x0 = xp[i];
        let x1 = xp[i + 1];
        let y0 = fp[i];
        let y1 = fp[i + 1];
        (y0 + ((y1 - y0) * (x_val - x0)) / (x1 - x0)) as i32
    }
}
// </vc-helpers>

// <vc-spec>
fn interp(x: Vec<i32>, xp: Vec<i32>, fp: Vec<i32>) -> (result: Vec<i32>)
    requires 
        xp.len() > 0,
        fp.len() == xp.len(),
        x.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < x.len() ==> (
            (x[k] <= xp[0] ==> result[k] == fp[0]) &&
            (x[k] >= xp[xp.len() - 1] ==> result[k] == fp[fp.len() - 1])
        )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added decreases clause to fix compilation error */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> (
                (x[k] <= xp[0] ==> result[k] == fp[0]) &&
                (x[k] >= xp[xp.len() - 1] ==> result[k] == fp[fp.len() - 1])
            )
        decreases x.len() - i
    {
        let x_val = x[i];
        let interp_val = if x_val <= xp[0] {
            fp[0]
        } else if x_val >= xp[xp.len() - 1] {
            fp[fp.len() - 1]
        } else {
            let mut j = 0;
            while j < xp.len() - 1
                invariant
                    0 <= j < xp.len(),
                    forall|k: int| 0 <= k < j ==> xp[k] < x_val
                decreases xp.len() - 1 - j
            {
                if xp[j] <= x_val && x_val < xp[j + 1] {
                    break;
                }
                j += 1;
            }
            let x0 = xp[j];
            let x1 = xp[j + 1];
            let y0 = fp[j];
            let y1 = fp[j + 1];
            (y0 + ((y1 - y0) * (x_val - x0)) / (x1 - x0)) as i32
        };
        result.push(interp_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}