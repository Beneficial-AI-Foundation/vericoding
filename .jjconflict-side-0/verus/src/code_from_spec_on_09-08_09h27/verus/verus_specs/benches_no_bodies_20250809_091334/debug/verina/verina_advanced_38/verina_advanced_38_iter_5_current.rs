use vstd::prelude::*;

verus! {

fn example_function(intervals: &mut Vec<i32>, i: usize, min_idx: usize) 
    requires 
        i < intervals.len(),
        min_idx < intervals.len(),
{
    /* code modified by LLM (iteration 1): Fixed method call syntax and added proper indexing */
    intervals.set(i, intervals[min_idx]);
}

fn main() {}

}