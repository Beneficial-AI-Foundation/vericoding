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
    let mut inserted = false;
    
    for i in 0..ys.len()
        invariant
            result@.len() == i,
            !inserted ==> result@.to_multiset() == ys@.subrange(0, i as int).to_multiset(),
            inserted ==> result@.to_multiset() == ys@.subrange(0, i as int).to_multiset().insert(x),
    {
        if !inserted && x <= ys[i] {
            result.push(x);
            inserted = true;
        }
        result.push(ys[i]);
    }
    
    if !inserted {
        result.push(x);
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
    
    let last = arr[arr.len() - 1];
    let mut rest = Vec::new();
    
    for i in 0..(arr.len() - 1)
        invariant
            rest@.len() == i,
            rest@.to_multiset() == arr@.subrange(0, i as int).to_multiset(),
    {
        rest.push(arr[i]);
    }
    
    let sorted_rest = insertion_sort_impl(rest);
    insert(last, sorted_rest)
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
    let mut result = Vec::new();
    
    for i in 0..xs.len()
        invariant
            result@.len() == i,
            forall|k: int, l: int| 0 <= k < l < result@.len() ==> result@[k] <= result@[l],
            result@.to_multiset() == xs@.subrange(0, i as int).to_multiset(),
    {
        let x = xs[i];
        let mut new_result = Vec::new();
        let mut inserted = false;
        
        for j in 0..result.len()
            invariant
                new_result@.len() == j,
                !inserted ==> new_result@.to_multiset() == result@.subrange(0, j as int).to_multiset(),
                inserted ==> new_result@.to_multiset() == result@.subrange(0, j as int).to_multiset().insert(x),
                forall|k: int, l: int| 0 <= k < l < new_result@.len() ==> new_result@[k] <= new_result@[l],
        {
            if !inserted && x <= result[j] {
                new_result.push(x);
                inserted = true;
            }
            new_result.push(result[j]);
        }
        
        if !inserted {
            new_result.push(x);
        }
        
        result = new_result;
    }
    
    result
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