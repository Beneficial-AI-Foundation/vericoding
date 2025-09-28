// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [added explicit invariant] */
fn find_and_update_bin(val: f32, bins: &Vec<f32>, hist: Vec<i8>) -> (res: Vec<i8>)
    requires
        bins.len() >= 2,
        hist.len() == bins.len() - 1,
    ensures
        res.len() == bins.len() - 1,
{
    let mut new_hist = hist;
    let mut j: usize = 0;
    let num_bins = bins.len() - 1;
    while j < num_bins
        invariant
            0 <= j <= num_bins,
            num_bins == bins.len() - 1,
            new_hist.len() == num_bins,
            bins.len() >= 2,
        decreases num_bins - j
    {
        if val >= bins[j] && val < bins[j+1] {
            if new_hist[j] < 127i8 {
                new_hist.set(j, new_hist[j] + 1);
            }
            break;
        }
        j = j + 1;
    }
    new_hist
}
// </vc-helpers>

// <vc-spec>
fn histogram(data: Vec<f32>, bins: Vec<f32>) -> (result: Vec<i8>)
    requires 
        bins.len() >= 2,
    ensures
        result.len() == bins.len() - 1,
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn histogram_helper(data: Vec<f32>, bins: Vec<f32>, hist: Vec<i8>, index: i8) -> (result: Vec<i8>)
    requires 
        bins.len() >= 2,
        hist.len() == bins.len() - 1,
    ensures
        result.len() == bins.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): [fixed loop initialization and invariants] */
    let mut new_hist = hist;
    let mut i: usize = 0;
    while i < data.len()
        invariant
            0 <= i <= data.len(),
            new_hist.len() == bins.len() - 1,
            bins.len() >= 2,
        decreases data.len() - i
    {
        let val = data[i];
        new_hist = find_and_update_bin(val, &bins, new_hist);
        i = i + 1;
    }
    new_hist
}
// </vc-code>


}
fn main() {}