use vstd::prelude::*;

verus! {

// Precondition for insertion sort - always true in this case
pub open spec fn insertion_sort_precond(xs: Seq<int>) -> bool {
    true
}

// Helper function to insert an element into a sorted list
fn insert(x: int, ys: Vec<int>) -> (result: Vec<int>)
    ensures
        result@.len() == ys@.len() + 1,
        result@.to_multiset() == ys@.to_multiset().insert(x),
    decreases ys@.len(),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    // Find the position to insert x
    while i < ys.len()
        invariant
            0 <= i <= ys.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == ys@[j],
            forall|j: int| 0 <= j < i ==> ys@[j] <= x,
    {
        if ys[i] > x {
            break;
        }
        result.push(ys[i]);
        i = i + 1;
    }
    
    // Insert x at position i
    result.push(x);
    
    // Add remaining elements
    /* code modified by LLM (iteration 1): Fixed type conversion from usize to int and corrected loop invariant logic */
    while i < ys.len()
        invariant
            0 <= i <= ys.len(),
            result@.len() == (i as int) + 1,
            result@.to_multiset() == ys@.subrange(0, i as int).to_multiset().insert(x),
    {
        result.push(ys[i]);
        i = i + 1;
    }
    
    result
}

// Implementation function for recursion
fn insertion_sort_impl(arr: Vec<int>) -> (result: Vec<int>)
    ensures
        result@.to_multiset() == arr@.to_multiset(),
    decreases arr@.len(),
{
    if arr.len() == 0 {
        return Vec::new();
    }
    
    let mut tail = Vec::new();
    for i in 1..arr.len()
        invariant
            tail@.len() == i - 1,
            forall|j: int| 1 <= j < i ==> tail@[j-1] == arr@[j],
    {
        tail.push(arr[i]);
    }
    
    let sorted_tail = insertion_sort_impl(tail);
    insert(arr[0], sorted_tail)
}

// Main insertion sort function  
pub fn insertion_sort(xs: Vec<int>) -> (result: Vec<int>)
    requires insertion_sort_precond(xs@),
    ensures
        // Result is sorted (pairwise less than or equal)
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] <= result@[j],
        // Result is a permutation of the input
        result@.to_multiset() == xs@.to_multiset(),
{
    insertion_sort_impl(xs)
}

// Postcondition specification
pub open spec fn insertion_sort_postcond(xs: Seq<int>, result: Seq<int>) -> bool {
    // Result is sorted (pairwise ordering)
    (forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j]) &&
    // Result is a permutation of input
    result.to_multiset() == xs.to_multiset()
}

fn main() {}

}