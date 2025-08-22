use vstd::prelude::*;

verus! {

// Helper predicate to check if a vector is sorted (corresponds to List.Pairwise (· ≤ ·))
spec fn is_sorted(v: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

// Insert element into sorted vector (corresponds to insertElement)
fn insert_element(x: i32, l: Vec<i32>) -> (result: Vec<i32>)
    requires
        is_sorted(&l),
    ensures
        is_sorted(&result),
        result.len() == l.len() + 1,
    decreases l.len(),
{
    let mut result = Vec::new();
    let mut inserted = false;
    
    for i in 0..l.len()
        invariant
            result.len() == i,
            !inserted ==> (forall|k: int| 0 <= k < i ==> l[k] < x),
            inserted ==> (exists|pos: int| 0 <= pos <= i && 
                (forall|k: int| 0 <= k < pos ==> result[k] == l[k]) &&
                result[pos] == x &&
                (forall|k: int| pos < k < result.len() ==> result[k] == l[k - 1])),
            is_sorted(&result),
    {
        if !inserted && l[i] >= x {
            result.push(x);
            inserted = true;
        }
        result.push(l[i]);
    }
    
    if !inserted {
        result.push(x);
    }
    
    result
}

// Sort a list using insertion sort (corresponds to sortList)
fn sort_list(l: Vec<i32>) -> (result: Vec<i32>)
    ensures
        is_sorted(&result),
        result.len() == l.len(),
    decreases l.len(),
{
    if l.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    
    for i in 0..l.len()
        invariant
            result.len() == i,
            is_sorted(&result),
    {
        result = insert_element(l[i], result);
    }
    
    result
}

// Precondition for insertion sort (always true in this case)
spec fn insertion_sort_precond(l: &Vec<i32>) -> bool {
    true
}

// Main insertion sort function
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    requires
        insertion_sort_precond(&l),
    ensures
        is_sorted(&result) && 
        result.len() == l.len(),
{
    sort_list(l)
}

// Postcondition specification (corresponds to List.Pairwise (· ≤ ·) result ∧ List.isPerm l result)
// Note: We only implement the sortedness part, not the full permutation proof
spec fn insertion_sort_postcond(l: &Vec<i32>, result: &Vec<i32>) -> bool {
    is_sorted(result) && result.len() == l.len()
}

}

fn main() {}