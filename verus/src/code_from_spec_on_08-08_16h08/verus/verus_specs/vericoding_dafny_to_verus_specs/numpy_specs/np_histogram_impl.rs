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
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < bins.len() - 1
        invariant
            hist.len() == i,
            i <= bins.len() - 1,
        decreases bins.len() - 1 - i
    {
        hist.push(0);
        i += 1;
    }
    
    // Count data points in each bin
    let mut data_idx = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while data_idx < data.len()
        invariant
            hist.len() == bins.len() - 1,
            data_idx <= data.len(),
        decreases data.len() - data_idx
    {
        let value = data[data_idx];
        
        // Find which bin this value belongs to
        let mut bin_idx = 0;
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        while bin_idx < bins.len() - 1
            invariant
                hist.len() == bins.len() - 1,
                bin_idx <= bins.len() - 1,
            decreases bins.len() - 1 - bin_idx
        {
            if value >= bins[bin_idx] && (bin_idx == bins.len() - 2 || value < bins[bin_idx + 1]) {
                /* code modified by LLM (iteration 1): fix borrowing conflict by reading current value before setting */
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
    // Helper function implementation - could be used for recursive approach
    // For now, implementing as empty since main histogram function is complete
}

fn main() {}

}