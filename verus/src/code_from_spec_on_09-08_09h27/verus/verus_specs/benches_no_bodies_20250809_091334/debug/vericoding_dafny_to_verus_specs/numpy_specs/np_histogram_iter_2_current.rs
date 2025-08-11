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
    while i < bins.len() - 1
        invariant
            hist.len() == i,
            i <= bins.len() - 1,
            bins.len() >= 2,
    {
        hist.push(0);
        i += 1;
    }
    
    // Count data points in each bin
    let mut data_idx = 0;
    while data_idx < data.len()
        invariant
            hist.len() == bins.len() - 1,
            data_idx <= data.len(),
            bins.len() >= 2,
    {
        let value = data[data_idx];
        
        // Find which bin this value belongs to
        let mut bin_idx = 0;
        while bin_idx < bins.len() - 1
            invariant
                bin_idx <= bins.len() - 1,
                hist.len() == bins.len() - 1,
                bins.len() >= 2,
        {
            if value >= bins[bin_idx] && value < bins[bin_idx + 1] {
                /* code modified by LLM (iteration 1): fix borrowing conflict by storing current value before mutation */
                let current_count = hist[bin_idx];
                hist.set(bin_idx, current_count + 1);
                break;
            }
            bin_idx += 1;
        }
        
        data_idx += 1;
    }
    
    hist
}

// SPEC
fn histogram_helper(data: &[i32], bins: &[i32], hist: &mut Vec<i32>, index: usize)
    requires
        bins.len() >= 2,
        forall|i: int| 1 <= i < bins.len() ==> bins[i] > bins[#[trigger](i-1)],
{
    // This helper function could be used to process data incrementally
    // For now, implementing as a no-op since the main histogram function
    // handles the complete logic
}

fn main() {}

}