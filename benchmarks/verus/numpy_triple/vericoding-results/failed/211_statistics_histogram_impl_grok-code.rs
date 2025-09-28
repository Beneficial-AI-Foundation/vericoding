// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_seq(s: Seq<usize>) -> nat 
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        (s[0] as nat) + sum_seq(s.drop_first())
    }
}
// </vc-preamble>

// <vc-helpers>
fn compute_idx(d: i8, min_val: i8, max_val: i8, n_bins: usize) -> (result: usize)
    requires
        n_bins > 0,
        (min_val as int) < (max_val as int),
        (min_val as int) <= (d as int),
        (d as int) <= (max_val as int),
    ensures
        result < n_bins,
{
    /* helper modified by LLM (iteration 5): Use u128 for idx calculation to avoid overflow */
    let pos: i64 = (d as i64 - min_val as i64);
    let diff: i64 = (max_val as i64 - min_val as i64);
    let idx_u128: u128 = ((pos as u128) * (n_bins as u128)) / (diff as u128);
    let idx: usize = if idx_u128 == (n_bins as u128) {
        n_bins - 1
    } else {
        idx_u128 as usize
    };
    idx
}
// </vc-helpers>

// <vc-spec>
fn histogram(data: Vec<i8>, n_bins: usize, min_val: i8, max_val: i8) -> (result: (Vec<usize>, Vec<i8>))
    requires
        n_bins > 0,
        (min_val as int) < (max_val as int),
    ensures

        result.1.len() == n_bins + 1,
        result.1[0] == min_val,
        result.1[(n_bins as int)] == max_val,

        result.0.len() == n_bins,

        sum_seq(result.0@) == data@.filter(|x: i8| (min_val as int) <= (x as int) && (x as int) <= (max_val as int)).len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use i128 for edge calculation to avoid overflow */
    let mut edges: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let diff: i64 = (max_val as i64 - min_val as i64);
    while i <= n_bins
        invariant
            edges.len() == i,
            i <= n_bins + 1,
        decreases (n_bins + 1 - i)
    {
        let edge_val: i8 = if i == 0 {
            min_val
        } else if i == n_bins {
            max_val
        } else {
            let edge_val_i128: i128 = min_val as i128 + (((i as i128) * (diff as i128)) / (n_bins as i128));
            #[verifier::truncate] (edge_val_i128 as i8)
        };
        edges.push(edge_val);
        i += 1;
    }
    let mut counts: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < n_bins 
        invariant
            counts.len() == k,
            k <= n_bins,
        decreases (n_bins - k)
    {
        counts.push(0);
        k += 1;
    }
    let mut j: usize = 0;
    while j < data.len()
        invariant
            j <= data.len(),
        decreases (data.len() - j)
    {
        let d: i8 = data[j];
        if (min_val as i64) <= (d as i64) && (d as i64) <= (max_val as i64) {
            let idx = compute_idx(d, min_val, max_val, n_bins);
            counts[idx] = counts[idx] + 1;
        }
        j += 1;
    }
    (counts, edges)
}
// </vc-code>

}
fn main() {}