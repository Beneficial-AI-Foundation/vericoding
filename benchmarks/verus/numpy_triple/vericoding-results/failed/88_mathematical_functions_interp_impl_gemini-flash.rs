// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed the return type syntax for `proof fn` */
proof fn find_interval(x_val: i32, xp: &Vec<i32>) -> (lo: usize, hi: usize)
    requires 
        xp.len() >= 2,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
        xp[0] < x_val < xp[xp.len() - 1]
    ensures 
        0 <= lo < xp.len(),
        0 <= hi < xp.len(),
        lo < hi,
        hi == lo + 1,
        xp[lo] <= x_val < xp[hi]
{
    // Binary search to find the interval [xp[lo], xp[hi]] such that xp[lo] <= x_val < xp[hi]
    let mut low: usize = 0;
    let mut high: usize = xp.len() - 1;

    while low + 1 < high
        invariant 
            0 <= low < xp.len(),
            0 <= high < xp.len(),
            low < high,
            xp[low] <= x_val < xp[high],
            high - low >= 1
    {
        let mid = low + (high - low) / 2;
        if x_val < xp[mid] {
            high = mid;
        } else {
            low = mid;
        }
    }
    (low, high)
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
/* code modified by LLM (iteration 5): The proof for `find_interval` required a return type, updated the definition. The main `interp` function had a compilation error due to `assume(false)` and `unreached()`, which were removed and replaced with the actual implementation logic from previous iterations. */
{
    let mut result: Vec<i32> = Vec::new();
    result.reserve(x.len());

    let xp_len = xp.len();
    let fp_len = fp.len();

    for i in 0..x.len()
        invariant 
            result.len() == i,
            result.spec_len() == i,
            xp_len == xp.len(),
            fp_len == fp.len(),
            forall|j: int, k: int| 0 <= j < k < xp.len() ==> xp[j] < xp[k],
            forall|k: int| 0 <= k < i ==> (
                (x[k] <= xp[0]) ==> result[k] == fp[0]
            ),
            forall|k: int| 0 <= k < i ==> (
                (x[k] >= xp[xp.len() - 1]) ==> result[k] == fp[fp.len() - 1]
            ),
            forall|k: int| 0 <= k < i && xp[0] < x[k] < xp[xp.len() - 1] ==> {
                let (lo, hi) = find_interval(x[k], &xp);
                let val_lo = xp[lo];
                let val_hi = xp[hi];
                let f_lo = fp[lo];
                let f_hi = fp[hi];

                let numerator = (x[k] - val_lo) as i64 * (f_hi - f_lo) as i64;
                let denominator = (val_hi - val_lo) as i64;

                result[k] == (f_lo as i64 + numerator / denominator) as i32
            },
    {
        let x_val = x[i];

        let mut current_res: i32;

        if x_val <= xp[0] {
            current_res = fp[0];
        } else if x_val >= xp[xp_len - 1] {
            current_res = fp[fp_len - 1];
        } else {
            let (lo, hi) = find_interval(x_val, &xp);

            let val_lo = xp[lo];
            let val_hi = xp[hi];
            let f_lo = fp[lo];
            let f_hi = fp[hi];

            let numerator = (x_val - val_lo) as i64 * (f_hi - f_lo) as i64;
            let denominator = (val_hi - val_lo) as i64;

            current_res = (f_lo as i64 + numerator / denominator) as i32;
        }
        result.push(current_res);
    }
    result
}
// </vc-code>

}
fn main() {}