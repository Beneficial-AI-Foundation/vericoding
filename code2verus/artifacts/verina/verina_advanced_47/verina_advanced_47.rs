use vstd::prelude::*;

verus! {

// Precondition for mergeIntervals
spec fn merge_intervals_precond(intervals: Seq<(int, int)>) -> bool {
    true
}

// Helper function to insert an interval into a sorted list
fn insert(x: (int, int), sorted: Vec<(int, int)>) -> (result: Vec<(int, int)>)
{
    let mut result = Vec::new();
    let mut inserted = false;
    
    for i in 0..sorted.len() {
        if !inserted && x.0 <= sorted[i].0 {
            result.push(x);
            inserted = true;
        }
        result.push(sorted[i]);
    }
    
    if !inserted {
        result.push(x);
    }
    
    result
}

// Helper function to sort intervals by start time
fn sort_intervals(intervals: Vec<(int, int)>) -> (result: Vec<(int, int)>)
{
    let mut result = Vec::new();
    
    for i in 0..intervals.len() {
        result = insert(intervals[i], result);
    }
    
    result
}

// Main merge intervals function
fn merge_intervals(intervals: Vec<(int, int)>) -> (result: Vec<(int, int)>)
    requires merge_intervals_precond(intervals@)
{
    if intervals.len() == 0 {
        return Vec::new();
    }
    
    // Sort intervals by start time
    let sorted = sort_intervals(intervals);
    
    // Merge overlapping intervals
    let mut merged = Vec::new();
    
    if sorted.len() > 0 {
        merged.push(sorted[0]);
        
        let mut i = 1;
        while i < sorted.len()
            invariant 
                merged.len() >= 1,
                1 <= i <= sorted.len()
            decreases sorted.len() - i
        {
            let current = sorted[i];
            
            if merged.len() > 0 {
                let last_idx = (merged.len() - 1) as usize;
                let last = merged[last_idx];
                
                if current.0 <= last.1 {
                    // Overlapping intervals - merge them
                    let new_end = if current.1 > last.1 { current.1 } else { last.1 };
                    merged.set(last_idx, (last.0, new_end));
                } else {
                    // Non-overlapping interval - add it
                    merged.push(current);
                }
            }
            i = i + 1;
        }
    }
    
    merged
}

// Helper function to check if all original intervals are covered
spec fn all_covered(intervals: Seq<(int, int)>, result: Seq<(int, int)>) -> bool {
    forall|i: int| 
        #![trigger intervals[i]]
        0 <= i < intervals.len() ==> 
        exists|j: int| 
            #![trigger result[j]]
            0 <= j < result.len() && 
            result[j].0 <= intervals[i].0 && intervals[i].1 <= result[j].1
}

// Helper function to check if no intervals overlap  
spec fn no_overlap(result: Seq<(int, int)>) -> bool {
    forall|i: int, j: int| 
        #![trigger result[i], result[j]]
        0 <= i < j < result.len() ==> result[i].1 < result[j].0
}

// Postcondition for mergeIntervals
spec fn merge_intervals_postcond(intervals: Seq<(int, int)>, result: Seq<(int, int)>) -> bool {
    all_covered(intervals, result) && no_overlap(result)
}

}

fn main() {
    // Main function for compilation
}