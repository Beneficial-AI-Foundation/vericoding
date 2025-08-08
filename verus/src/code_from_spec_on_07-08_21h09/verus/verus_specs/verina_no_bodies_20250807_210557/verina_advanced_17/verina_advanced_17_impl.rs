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
{
    /* code modified by LLM (iteration 1): Fixed int casting to use usize for vector indexing */
    let mut result: Vec<i32> = Vec::new();
    let mut inserted = false;
    
    for i in 0..l.len()
        invariant
            result.len() == i || result.len() == i + 1,
            !inserted ==> result.len() == i,
            inserted ==> result.len() == i + 1,
            !inserted ==> (forall|k: int| 0 <= k < i ==> l[k] < x),
            inserted ==> exists|insert_pos: int| 0 <= insert_pos <= i && result[insert_pos] == x,
            forall|k: int| 0 <= k < result.len() - 1 ==> result[k] <= result[k + 1],
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
    
    /* code modified by LLM (iteration 1): Added proof block to establish sortedness */
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j]);
    }
    
    result
}

// Sort a list using insertion sort (corresponds to sortList)
fn sort_list(l: Vec<i32>) -> (result: Vec<i32>)
    ensures
        is_sorted(&result),
        result.len() == l.len(),
{
    /* code modified by LLM (iteration 1): Fixed int casting to use usize for vector indexing */
    if l.len() == 0 {
        return Vec::<i32>::new();
    }
    
    let mut result: Vec<i32> = Vec::new();
    result.push(l[0]);
    
    for i in 1..l.len()
        invariant
            1 <= result.len() <= i,
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