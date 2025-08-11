use vstd::prelude::*;

verus! {

// Precondition definition - equivalent to Lean's List.Pairwise (· ≤ ·)
spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn merge_sorted_lists_precond(arr1: Seq<i32>, arr2: Seq<i32>) -> bool {
    is_sorted(arr1) && is_sorted(arr2)
}

// Postcondition definition - equivalent to Lean's List.Pairwise (· ≤ ·) result ∧ List.isPerm (arr1 ++ arr2) result
spec fn merge_sorted_lists_postcond(arr1: Seq<i32>, arr2: Seq<i32>, result: Seq<i32>) -> bool {
    is_sorted(result) && result.to_multiset() =~= arr1.add(arr2).to_multiset()
}

// Main function that implements merge sort using iterative approach
fn merge_sorted_lists(arr1: Vec<i32>, arr2: Vec<i32>) -> (result: Vec<i32>)
    requires
        merge_sorted_lists_precond(arr1@, arr2@),
    ensures
        merge_sorted_lists_postcond(arr1@, arr2@, result@),
{
    let mut result = Vec::new();
    let mut i = 0usize;
    let mut j = 0usize;
    
    while i < arr1.len() || j < arr2.len()
        invariant
            i <= arr1.len(),
            j <= arr2.len(),
            is_sorted(result@),
            result@.to_multiset() =~= arr1@.subrange(0, i as int).add(arr2@.subrange(0, j as int)).to_multiset(),
            forall|k: int| 0 <= k < result@.len() ==> {
                &&& (i < arr1.len() ==> result@[k] <= arr1@[i as int])
                &&& (j < arr2.len() ==> result@[k] <= arr2@[j as int])
            }
    {
        if i >= arr1.len() {
            result.push(arr2[j]);
            j += 1;
        } else if j >= arr2.len() {
            result.push(arr1[i]);
            i += 1;
        } else if arr1[i] <= arr2[j] {
            result.push(arr1[i]);
            i += 1;
        } else {
            result.push(arr2[j]);
            j += 1;
        }
    }
    
    result
}

// Helper function to convert Seq to Vec
fn seq_to_vec(s: Seq<i32>) -> (result: Vec<i32>)
    ensures result@ == s
{
    /* code modified by LLM (iteration 1): Added helper function to convert Seq to Vec */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == s[k]
    {
        result.push(s[i as int]);
        i += 1;
    }
    
    result
}

// Proof function corresponding to mergeSortedLists_spec_satisfied
proof fn merge_sorted_lists_spec_satisfied(arr1: Seq<i32>, arr2: Seq<i32>)
    requires merge_sorted_lists_precond(arr1, arr2)
    ensures exists|result: Vec<i32>| merge_sorted_lists_postcond(arr1, arr2, result@)
{
    /* code modified by LLM (iteration 1): Fixed Vec::from_seq calls by using helper function */
    let arr1_vec = seq_to_vec(arr1);
    let arr2_vec = seq_to_vec(arr2);
    let result = merge_sorted_lists(arr1_vec, arr2_vec);
    assert(merge_sorted_lists_postcond(arr1, arr2, result@));
}

fn main() {}

} // verus!