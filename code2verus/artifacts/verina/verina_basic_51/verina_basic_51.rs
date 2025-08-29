use vstd::prelude::*;

verus! {

// Precondition: array is sorted
spec fn binary_search_precond(a: Seq<i32>, key: i32) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// Helper function for the loop  
fn binary_search_loop(a: &Vec<i32>, key: i32, lo: usize, hi: usize) -> (result: usize)
    requires
        lo <= hi <= a.len(),
        binary_search_precond(a@, key),
        // Invariant: all elements before lo are < key, all elements >= hi are >= key
        forall|i: int| 0 <= i < lo ==> a[i] < key,
        forall|i: int| hi <= i < a.len() ==> a[i] >= key,
    ensures
        result <= a.len(),
        forall|i: int| 0 <= i < result ==> a[i] < key,
        forall|i: int| result <= i < a.len() ==> a[i] >= key,
    decreases hi - lo
{
    if lo < hi {
        let mid = lo + (hi - lo) / 2;
        if a[mid] < key {
            binary_search_loop(a, key, mid + 1, hi)
        } else {
            binary_search_loop(a, key, lo, mid)
        }
    } else {
        lo
    }
}

// Main binary search function
fn binary_search(a: &Vec<i32>, key: i32) -> (result: usize)
    requires
        binary_search_precond(a@, key),
    ensures
        result <= a.len(),
        forall|i: int| 0 <= i < result ==> a[i] < key,
        forall|i: int| result <= i < a.len() ==> a[i] >= key,
{
    binary_search_loop(a, key, 0, a.len())
}

// Postcondition specification
spec fn binary_search_postcond(a: Seq<i32>, key: i32, result: usize) -> bool {
    result <= a.len() &&
    (forall|i: int| 0 <= i < result ==> a[i] < key) &&
    (forall|i: int| result <= i < a.len() ==> a[i] >= key)
}

}

fn main() {}