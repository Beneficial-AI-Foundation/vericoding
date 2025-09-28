// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_segment(x_val: i32, xp: &Vec<i32>) -> (idx: usize)
    requires
        xp.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
    ensures
        0 <= idx < xp.len(),
        idx == 0 ==> x_val <= xp[0],
        idx == xp.len() - 1 ==> x_val >= xp[xp.len() - 1],
        0 < idx < xp.len() ==> (xp@[idx - 1] <= x_val && x_val <= xp@[idx])
{
    let mut low: usize = 0;
    let mut high: usize = xp.len() - 1;
    let mut result_idx: usize = 0;

    if x_val <= xp[0] {
        return 0;
    }
    if x_val >= xp[xp.len() - 1] {
        return xp.len() - 1;
    }

    while low <= high
        invariant
            0 <= low <= xp.len(),
            (high == (xp.len() as int - 1) as usize || high < xp.len()) && (high as int >= -1),
            (low == 0 || xp@[low - 1] <= x_val),
            (high >= xp.len() - 1 || x_val <= xp@[high + 1]),
            low <= high + 1,
            (result_idx < xp.len() || result_idx == 0)
        decreases high as int - low as int
    {
        let mid: usize = low + (high - low) / 2;

        if mid < xp.len() && x_val < xp@[mid] {
            high = mid - 1;
        } else {
            low = mid + 1;
            result_idx = mid;
        }
    }
    result_idx
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
/* code modified by LLM (iteration 5): fixed indexing expression in invariant (xp[segment_idx] to xp@[segment_idx]) */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < x.len()
        invariant 
            0 <= i <= x.len(),
            result.len() == i,
            xp.len() > 0,
            fp.len() == xp.len(),
            x.len() > 0,
            forall|k: int, l: int| 0 <= k < l < xp.len() ==> xp[k] < xp[l],
            forall|k: int| 0 <= k < i ==> (
                (x[k] <= xp[0] ==> result[k] == fp[0]) &&
                (x[k] >= xp[xp.len() - 1] ==> result[k] == fp[fp.len() - 1]) &&
                (xp[0] < x[k] && x[k] < xp[xp.len() - 1] ==> (
                    {
                        let segment_idx = find_segment(x[k], &xp);
                        0 < segment_idx && segment_idx < xp.len() ==> (xp@[segment_idx - 1] <= x[k] && x[k] <= xp@[segment_idx])
                    }
                ))
            ),
        decreases x.len() - i
    {
        let x_val = x[i];

        let idx = find_segment(x_val, &xp);

        if idx == 0 {
            result.push(fp[0]);
        } else if idx == xp.len() - 1 {
            result.push(fp[xp.len() - 1]);
        } else {
            let x0 = xp@[idx - 1];
            let x1 = xp@[idx];
            let y0 = fp@[idx - 1];
            let y1 = fp@[idx];
            
            let range_x = (x1 - x0) as i64;
            let range_y = (y1 - y0) as i64;
            let x_diff = (x_val - x0) as i64;

            let interpolated_val: i32;

            if range_x == 0 {
                interpolated_val = y0;
            } else {
                interpolated_val = (y0 as i64 + (x_diff * range_y / range_x)) as i32;
            }
            result.push(interpolated_val);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}