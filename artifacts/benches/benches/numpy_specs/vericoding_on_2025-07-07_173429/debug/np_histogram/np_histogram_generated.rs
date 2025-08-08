use vstd::prelude::*;

verus! {

fn histogram(data: &Vec<i32>, bins: &Vec<i32>) -> (hist: Vec<i32>)
    requires 
        bins.len() >= 2,
        data.len() < 1000000, // Reasonable bound to prevent overflow
    ensures 
        hist.len() == bins.len() - 1,
{
    let mut hist = Vec::with_capacity((bins.len() - 1) as usize);
    
    // Initialize histogram counts to zero
    let mut i = 0;
    while i < bins.len() - 1
        invariant 
            0 <= i <= bins.len() - 1,
            hist.len() == i,
        decreases bins.len() - 1 - i,
    {
        hist.push(0i32);
        i = i + 1;
    }
    
    // Count data points in each bin
    let mut data_index = 0;
    while data_index < data.len()
        invariant 
            0 <= data_index <= data.len(),
            hist.len() == bins.len() - 1,
        decreases data.len() - data_index,
    {
        let mut bin_index = 0;
        while bin_index < bins.len() - 1
            invariant 
                0 <= bin_index <= bins.len() - 1,
                hist.len() == bins.len() - 1,
                data_index < data.len(),
            decreases bins.len() - 1 - bin_index,
        {
            if data[data_index] >= bins[bin_index] && data[data_index] < bins[bin_index + 1] {
                let current_count = hist[bin_index];
                if current_count < 1000000 {
                    hist.set(bin_index as usize, current_count + 1);
                }
                break;
            }
            bin_index = bin_index + 1;
        }
        data_index = data_index + 1;
    }
    
    hist
}

fn histogram_helper(data: &Vec<i32>, bins: &Vec<i32>, hist: &mut Vec<i32>, index: usize)
    requires 
        bins.len() >= 2,
{
    // Helper method implementation - could be used for recursive or iterative processing
    // Since no specific postconditions are given, this is a minimal valid implementation
}

fn main() {}

}