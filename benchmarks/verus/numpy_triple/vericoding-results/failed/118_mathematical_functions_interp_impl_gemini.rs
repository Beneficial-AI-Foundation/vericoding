// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by using unreachable() which returns a value */
fn find_interval_idx(xp: &Vec<i32>, x: i32) -> (idx: usize)
    requires
        xp.len() >= 2,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
        xp[0] <= x < xp[xp.len() - 1],
    ensures
        0 <= idx < xp.len() - 1,
        xp[idx as int] <= x,
        x < xp[(idx as int) + 1],
{
    let mut i: usize = 0;
    while i < xp.len() - 1
        invariant
            xp.len() >= 2,
            forall|a: int, b: int| 0 <= a < b < xp.len() ==> xp[a] < xp[b],
            xp[0] <= x < xp[xp.len() - 1],
            0 <= i < xp.len(),
            forall|j: int| 0 <= j < i ==> xp[j + 1] <= x,
        decreases xp.len() - 1 - i
    {
        if x < xp[i + 1] {
            return i;
        }
        i = i + 1;
    }
    assert(false);
    unreachable();
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
    /* code modified by LLM (iteration 5): fixed a typo and added a clarifying assertion */
    let mut result: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < x.len()
        invariant
            0 <= k <= x.len(),
            result.len() == k,
            xp.len() > 0,
            fp.len() == xp.len(),
            forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
            forall|i: int| 0 <= i < k ==> (
                (x[i] <= xp[0] ==> result[i] == fp[0]) &&
                (x[i] >= xp[xp.len() - 1] ==> result[i] == fp[fp.len() - 1])
            ),
        decreases x.len() - k
    {
        let x_k = x[k];
        let y_k: i32;

        if x_k <= xp[0] {
            y_k = fp[0];
        } else if x_k >= xp[xp.len() - 1] {
            y_k = fp[fp.len() - 1];
        } else {
            assert(xp.len() >= 2);
            let i = find_interval_idx(&xp, x_k);
            
            let x1 = xp[i] as i64;
            let y1 = fp[i] as i64;
            let x2 = xp[i+1] as i64;
            let y2 = fp[i+1] as i64;
            let xk_64 = x_k as i64;

            let denominator = x2 - x1;
            assert(denominator > 0);
            
            let numerator = (xk_64 - x1) * (y2 - y1);
            
            let interp_val = y1 + numerator / denominator;
            y_k = interp_val as i32;
        }

        result.push(y_k);
        k = k + 1;
    }
    result
}

// </vc-code>

}
fn main() {}