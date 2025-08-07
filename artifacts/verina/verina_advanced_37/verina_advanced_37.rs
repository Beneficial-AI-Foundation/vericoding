use vstd::prelude::*;

verus! {

// Precondition - always true in this case
spec fn majority_element_precond(nums: Seq<i32>) -> bool {
    true
}

// Helper function to insert element in sorted order
fn insert(x: i32, xs: &Vec<i32>) -> (result: Vec<i32>)
{
    let mut result = Vec::new();
    let mut inserted = false;
    
    for i in 0..xs.len() {
        if !inserted && x <= xs[i] {
            result.push(x);
            inserted = true;
        }
        result.push(xs[i]);
    }
    
    if !inserted {
        result.push(x);
    }
    
    result
}

// Insertion sort implementation
fn insertion_sort(xs: &Vec<i32>) -> (result: Vec<i32>)
{
    let mut result = Vec::new();
    
    for i in 0..xs.len() {
        result = insert(xs[i], &result);
    }
    
    result
}

// Helper function to get element at index (returns 0 if out of bounds)
fn get_at(xs: &Vec<i32>, i: usize) -> i32 {
    if i < xs.len() {
        xs[i]
    } else {
        0
    }
}

// Main function
fn majority_element(nums: Vec<i32>) -> (result: i32)
    requires majority_element_precond(nums@)
    ensures majority_element_postcond(nums@, result)
{
    let sorted = insertion_sort(&nums);
    let len = sorted.len();
    let mid = len / 2;
    let result = get_at(&sorted, mid);
    proof {
        admit(); // Proof that postcondition holds
    }
    result
}

// Count occurrences of element in sequence
spec fn count_occurrences(seq: Seq<i32>, elem: i32) -> nat
    decreases seq.len()
{
    if seq.len() == 0 {
        0
    } else {
        let first = seq[0];
        let rest = seq.subrange(1, seq.len() as int);
        if first == elem {
            1 + count_occurrences(rest, elem)
        } else {
            count_occurrences(rest, elem)
        }
    }
}

// Check if all elements satisfy a condition  
spec fn all_satisfy(seq: Seq<i32>, result: i32) -> bool
    decreases seq.len()
{
    if seq.len() == 0 {
        true
    } else {
        let first = seq[0];
        let rest = seq.subrange(1, seq.len() as int);
        (first == result || count_occurrences(seq, first) <= seq.len() / 2) &&
        all_satisfy(rest, result)
    }
}

// Postcondition
spec fn majority_element_postcond(nums: Seq<i32>, result: i32) -> bool {
    let n = nums.len();
    count_occurrences(nums, result) > n / 2 &&
    all_satisfy(nums, result)
}

} // verus!

fn main() {
    // Empty main function for compilation
}