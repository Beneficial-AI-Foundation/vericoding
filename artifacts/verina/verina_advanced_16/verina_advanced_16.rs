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
    if ys.len() == 0 {
        vec![x]
    } else {
        let y = ys[0];
        if x <= y {
            let mut result = vec![x];
            for i in 0..ys.len() {
                result.push(ys[i]);
            }
            result
        } else {
            let mut ys_tail = Vec::new();
            for i in 1..ys.len() {
                ys_tail.push(ys[i]);
            }
            let mut result = vec![y];
            let inserted = insert(x, ys_tail);
            for i in 0..inserted.len() {
                result.push(inserted[i]);
            }
            result
        }
    }
}

// Implementation function for recursion
fn insertion_sort_impl(arr: Vec<int>) -> (result: Vec<int>)
    ensures
        result@.to_multiset() == arr@.to_multiset(),
    decreases arr@.len(),
{
    if arr.len() == 0 {
        vec![]
    } else {
        let x = arr[0];
        let mut xs = Vec::new();
        for i in 1..arr.len() {
            xs.push(arr[i]);
        }
        let sorted_xs = insertion_sort_impl(xs);
        insert(x, sorted_xs)
    }
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