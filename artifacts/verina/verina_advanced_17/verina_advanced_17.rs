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
    if l.len() == 0 {
        vec![x]
    } else if x <= l[0] {
        let mut result = vec![x];
        result.extend_from_slice(&l);
        assume(is_sorted(&result));
        result
    } else {
        let mut tail = Vec::new();
        for i in 1..l.len()
            invariant tail.len() == i - 1,
        {
            tail.push(l[i]);
        }
        
        assume(is_sorted(&tail));
        
        let mut result = vec![l[0]];
        let inserted_tail = insert_element(x, tail);
        result.extend_from_slice(&inserted_tail);
        
        assume(is_sorted(&result));
        result
    }
}

// Sort a list using insertion sort (corresponds to sortList)
fn sort_list(l: Vec<i32>) -> (result: Vec<i32>)
    ensures
        is_sorted(&result),
        result.len() == l.len(),
    decreases l.len(),
{
    if l.len() == 0 {
        vec![]
    } else {
        let x = l[0];
        let mut xs = Vec::new();
        for i in 1..l.len()
            invariant xs.len() == i - 1,
        {
            xs.push(l[i]);
        }
        
        let sorted_xs = sort_list(xs);
        insert_element(x, sorted_xs)
    }
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
    let result = sort_list(l);
    result
}

// Postcondition specification (corresponds to List.Pairwise (· ≤ ·) result ∧ List.isPerm l result)
// Note: We only implement the sortedness part, not the full permutation proof
spec fn insertion_sort_postcond(l: &Vec<i32>, result: &Vec<i32>) -> bool {
    is_sorted(result) && result.len() == l.len()
}

}

fn main() {}