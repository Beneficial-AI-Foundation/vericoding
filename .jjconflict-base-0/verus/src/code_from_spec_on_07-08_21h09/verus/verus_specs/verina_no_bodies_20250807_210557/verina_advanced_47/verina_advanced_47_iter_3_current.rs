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
    let mut i = 0;
    
    while i < sorted.len() {
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
    
    while i < intervals.len() {
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
    
    if sorted.len() > 0 {
        let mut current = sorted[0];
        let mut i = 1;
        
        while i < sorted.len() {
            if current.1 >= sorted[i].0 {
                // Overlapping intervals, merge them
                current = (current.0, if current.1 > sorted[i].1 { current.1 } else { sorted[i].1 });
            } else {
                // No overlap, add current to result and start new interval
                result.push(current);
                current = sorted[i];
            }
            i += 1;
        }
        
        result.push(current);
    }
    
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
    /* code modified by LLM (iteration 1): Fixed type annotations and debug printing */
    let intervals = vec![(1, 3), (2, 6), (8, 10), (15, 18)];
    let merged = merge_intervals(intervals);
    
    // Convert to regular integers for printing since vstd::prelude::int doesn't implement Debug
    let printable_merged: Vec<(i32, i32)> = merged.iter().map(|&(start, end)| (start.to_i32(), end.to_i32())).collect();
    println!("Merged intervals: {:?}", printable_merged);
}