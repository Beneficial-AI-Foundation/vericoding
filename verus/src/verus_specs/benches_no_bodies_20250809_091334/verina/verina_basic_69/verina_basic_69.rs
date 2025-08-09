use vstd::prelude::*;

verus! {

// Precondition: there exists an index i where a[i] equals e
spec fn linear_search_precond(a: &Vec<i32>, e: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i as int] == e
}

// Postcondition specification
spec fn linear_search_postcond(a: &Vec<i32>, e: i32, result: usize) -> bool {
    result < a.len() && 
    a[result as int] == e && 
    forall|k: int| 0 <= k < result ==> a[k] != e
}

// Auxiliary function for linear search
fn linear_search_aux(a: &Vec<i32>, e: i32, n: usize) -> (result: usize)
    requires
        n <= a.len(),
        linear_search_precond(a, e),
        forall|k: int| 0 <= k < n ==> a[k] != e,
    ensures
        linear_search_postcond(a, e, result),
    decreases a.len() - n,
{
    return 0;  // TODO: Remove this line and implement the function body
}

// Main linear search function
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires
        linear_search_precond(a, e),
    ensures
        linear_search_postcond(a, e, result),
{
    return 0;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}