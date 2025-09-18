// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversions and indexing using @ operator for sequences */
proof fn lemma_vec_sorted_suffix_has_min_index(xp: Seq<i32>, i: int, j: int) 
    requires 
        0 <= i <= j < xp.len(),
        forall|k: int, l: int| 0 <= k < l < xp.len() ==> xp[k] < xp[l]
    ensures 
        xp[i] <= xp[j]
{
    if i < j {
        lemma_vec_sorted_suffix_has_min_index(xp, i+1, j);
    }
}

proof fn lemma_vec_sorted_prefix_has_max_index(xp: Seq<i32>, i: int, j: int) 
    requires 
        0 <= i <= j < xp.len(),
        forall|k: int, l: int| 0 <= k < l < xp.len() ==> xp[k] < xp[l]
    ensures 
        xp[i] <= xp[j]
{
    if i < j {
        lemma_vec_sorted_prefix_has_max_index(xp, i, j-1);
    }
}

spec fn find_interval(x: i32, xp: Seq<i32>) -> (idx: int)
    recommends 
        xp.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j]
    ensures 
        0 <= idx <= xp.len() - 1,
        (idx == 0 ==> x <= xp[0]) || xp[idx] <= x,
        (idx == xp.len() - 1 ==> x >= xp[xp.len() - 1]) || x < xp[idx + 1]
{
    if x <= xp[0] {
        0
    } else if x >= xp[xp.len() - 1] {
        xp.len() - 1
    } else {
        let mut lo: int = 0;
        let mut hi: int = xp.len() - 1;
        while lo < hi
            invariant 
                0 <= lo < hi <= xp.len() - 1,
                xp[lo] <= x < xp[hi] || xp[lo] < x <= xp[hi],
                hi - lo > 0
            decreases hi - lo
        {
            let mid = lo + (hi - lo) / 2;
            if x < xp[mid] {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        lo
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
/* code modified by LLM (iteration 5): Fixed indexing to use @ operator instead of usize casts */
{
    let mut result = Vec::new();
    let n = x.len();
    let mut k: usize = 0;
    while k < n
        invariant 
            result.len() == k,
            forall|i: int| 0 <= i < k ==> (
                (x[i] <= xp[0] ==> result[i] == fp[0]) &&
                (x[i] >= xp[xp.len() - 1] ==> result[i] == fp[fp.len() - 1])
            )
        decreases n - k
    {
        let x_val = x[k];
        let idx = find_interval(x_val, xp@);
        let res_val = 
            if x_val <= xp@[0] {
                fp@[0]
            } else if x_val >= xp@[xp.len() - 1] {
                fp@[fp.len() - 1]
            } else {
                let x0 = xp@[idx];
                let x1 = xp@[idx + 1];
                let y0 = fp@[idx];
                let y1 = fp@[idx + 1];
                (y0 * (x1 - x_val) + y1 * (x_val - x0)) / (x1 - x0)
            };
        result.push(res_val);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}