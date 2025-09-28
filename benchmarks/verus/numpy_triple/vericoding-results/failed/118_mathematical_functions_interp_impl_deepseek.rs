// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix compilation error by removing 'exec' keyword */
fn find_interval(x: int, xp: Seq<int>) -> (idx: int)
    requires
        xp.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
    ensures
        0 <= idx < xp.len(),
        idx == xp.len() - 1 ==> x >= xp[idx],
        idx < xp.len() - 1 ==> x >= xp[idx] && x < xp[idx + 1]
{
    let mut idx: int = 0;
    let mut i: int = 0;
    while i < xp.len() - 1
        invariant
            0 <= i <= xp.len() - 1,
            0 <= idx <= i,
            x >= xp[idx],
            idx == xp.len() - 1 ==> x >= xp[idx],
            idx < xp.len() - 1 ==> x >= xp[idx] && x < xp[idx + 1]
        decreases xp.len() - i - 1
    {
        if x < xp[i + 1] {
            idx = i;
            break;
        }
        i = i + 1;
        idx = i;
    }
    idx
}

/* helper modified by LLM (iteration 5): Maintain linear interpolation logic with proper types */
fn linear_interpolate(x: int, x0: int, x1: int, f0: int, f1: int) -> (result: int)
    requires
        x0 <= x <= x1,
        x0 < x1
    ensures
        result == f0 + ((x - x0) * (f1 - f0)) / (x1 - x0)
{
    let numerator = (x - x0) * (f1 - f0);
    let denominator = x1 - x0;
    let result = f0 + numerator / denominator;
    result
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
/* code modified by LLM (iteration 5): Remove 'exec' keyword and fix indexing */
{
    let mut result = Vec::new();
    let n: usize = x.len();
    let xp_seq = xp@;
    let fp_seq = fp@;
    
    let mut k: usize = 0;
    while k < n
        invariant
            result.len() == k,
            forall|i: int| 0 <= i < k ==> (
                (x@[i] <= xp_seq[0] ==> result@[i] == fp_seq[0]) &&
                (x@[i] >= xp_seq[xp_seq.len() - 1] ==> result@[i] == fp_seq[fp_seq.len() - 1])
            )
        decreases n - k
    {
        let x_val: i32 = x[k];
        let ghost x_val_ghost: int = x@[k as int];
        
        if x_val <= xp[0] {
            result.push(fp[0]);
        } else if x_val >= xp[xp.len() - 1] {
            result.push(fp[fp.len() - 1]);
        } else {
            let ghost idx = find_interval(x_val_ghost, xp_seq);
            let x0: i32 = xp[idx as usize];
            let x1: i32 = xp[(idx as usize) + 1];
            let f0: i32 = fp[idx as usize];
            let f1: i32 = fp[(idx as usize) + 1];
            let ghost interpolated = linear_interpolate(x_val_ghost, x0 as int, x1 as int, f0 as int, f1 as int);
            result.push(interpolated as i32);
        }
        
        k = k + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}