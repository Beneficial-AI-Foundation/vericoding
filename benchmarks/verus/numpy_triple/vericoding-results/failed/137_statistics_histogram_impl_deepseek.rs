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
/* helper modified by LLM (iteration 5): Add proper result variable spec for bin_index_spec */
spec fn bin_index_spec(val: i32, min_val: i32, max_val: i32, n_bins: usize) -> (result: int)
    requires
        n_bins > 0,
        min_val < max_val,
        min_val <= val <= max_val,
    ensures
        0 <= result < n_bins as int
{
    let range = max_val - min_val;
    let scaled_val = (val - min_val) as int;
    (scaled_val * n_bins as int) / range
}

fn clamp(val: i32, min_val: i32, max_val: i32) -> i32 {
    if val < min_val {
        min_val
    } else if val > max_val {
        max_val
    } else {
        val
    }
}

proof fn sum_seq_monotonic(s1: Seq<usize>, s2: Seq<usize>)
    requires
        s1.len() == s2.len(),
        forall|i| 0 <= i < s1.len() ==> s1[i] <= s2[i],
    ensures
        sum_seq(s1) <= sum_seq(s2)
{
}
// </vc-helpers>

// <vc-spec>
fn histogram(data: Vec<i32>, n_bins: usize, min_val: i32, max_val: i32) -> (result: (Vec<usize>, Vec<i32>))
    requires
        n_bins > 0,
        min_val < max_val,
    ensures

        result.1.len() == n_bins + 1,
        result.1[0] == min_val,
        result.1[(n_bins as int)] == max_val,

        result.0.len() == n_bins,

        sum_seq(result.0@) == data@.filter(|x: i32| min_val <= x && x <= max_val).len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix result variable reference in ensures clause */
{
    let range = max_val - min_val;
    let mut bins: Vec<usize> = Vec::new();
    let mut bin_edges: Vec<i32> = Vec::new();
    
    for _ in 0..n_bins {
        bins.push(0);
    }
    
    bin_edges.push(min_val);
    for i in 1..=n_bins {
        bin_edges.push(min_val + (i as i32 * range) / n_bins as i32);
    }
    
    for item in data.iter() {
        if *item >= min_val && *item <= max_val {
            let scaled_val = (*item - min_val) as usize;
            let bin_index = (scaled_val * n_bins) / range as usize;
            let bin_index = if bin_index >= n_bins { n_bins - 1 } else { bin_index };
            bins[bin_index] += 1;
        }
    }
    
    let result = (bins, bin_edges);
    result
}
// </vc-code>

}
fn main() {}