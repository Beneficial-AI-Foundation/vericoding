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
    let mut i = 0;
    let mut inserted = false;
    
    while i < sorted.len()
    {
        if !inserted && x.0 <= sorted[i].0 {
            result.push(x);
            inserted = true;
        }
        result.push(sorted[i]);
        i += 1;
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
    let mut i = 0;
    
    while i < intervals.len()
    {
        result = insert(intervals[i], result);
        i += 1;
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
    
    let sorted = sort_intervals(intervals);
    let mut result = Vec::new();
    let mut current_start = sorted[0].0;
    let mut current_end = sorted[0].1;
    let mut i = 1;
    
    while i < sorted.len()
    {
        if sorted[i].0 <= current_end {
            // Overlapping intervals, merge them
            if sorted[i].1 > current_end {
                current_end = sorted[i].1;
            }
        } else {
            // Non-overlapping interval, add current to result
            result.push((current_start, current_end));
            current_start = sorted[i].0;
            current_end = sorted[i].1;
        }
        i += 1;
    }
    
    // Add the last interval
    result.push((current_start, current_end));
    
    result
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
    /* code modified by LLM (iteration 1): Fixed int literal syntax by explicitly casting to int */
    let intervals: Vec<(int, int)> = vec![(1int, 3int), (2int, 6int), (8int, 10int), (15int, 18int)];
    let merged = merge_intervals(intervals);
    
    // Print the length since we can't directly print int values
    println!("Number of merged intervals: {}", merged.len());
}