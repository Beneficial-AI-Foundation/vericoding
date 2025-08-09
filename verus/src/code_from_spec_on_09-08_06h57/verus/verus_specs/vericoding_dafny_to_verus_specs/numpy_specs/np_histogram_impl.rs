use vstd::prelude::*;

verus! {

// SPEC
fn histogram(data: &[i32], bins: &[i32]) -> (hist: Vec<i32>)
    requires 
        bins.len() >= 2,
        forall|i: int| 1 <= i < bins.len() ==> bins[i] > bins[#[trigger](i-1)],
    ensures
        hist.len() == bins.len() - 1,
        data.len() >= 0,
{
    let mut hist = Vec::new();
    
    // Initialize histogram with zeros
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while i < bins.len() - 1
        invariant
            i <= bins.len() - 1,
            hist.len() == i,
        decreases bins.len() - 1 - i
    {
        hist.push(0);
        i += 1;
    }
    
    // Count data points in each bin
    let mut data_idx = 0;
    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while data_idx < data.len()
        invariant
            data_idx <= data.len(),
            hist.len() == bins.len() - 1,
        decreases data.len() - data_idx
    {
        histogram_helper(data, bins, &mut hist, data_idx);
        data_idx += 1;
    }
    
    hist
}

// SPEC
fn histogram_helper(data: &[i32], bins: &[i32], hist: &mut Vec<i32>, index: usize)
    requires
        bins.len() >= 2,
        forall|i: int| 1 <= i < bins.len() ==> bins[i] > bins[#[trigger](i-1)],
        index < data.len(),
        old(hist).len() == bins.len() - 1,
    ensures
        hist.len() == bins.len() - 1,
{
    let value = data[index];
    
    // Find which bin this value belongs to
    let mut bin_idx = 0;
    /* code modified by LLM (iteration 1): added decreases clause and fixed vector operations */
    while bin_idx < bins.len() - 1
        invariant
            bin_idx <= bins.len() - 1,
            hist.len() == bins.len() - 1,
        decreases bins.len() - 1 - bin_idx
    {
        if value >= bins[bin_idx] && (bin_idx == bins.len() - 2 || value < bins[bin_idx + 1]) {
            /* code modified by LLM (iteration 1): fixed vector indexing and assignment operations */
            let current_count = hist[bin_idx];
            hist.set(bin_idx, current_count + 1);
            return;
        }
        bin_idx += 1;
    }
}

fn main() {}

}