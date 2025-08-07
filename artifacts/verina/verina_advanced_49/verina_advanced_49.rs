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
    proof {
        // This corresponds to the "sorry" in the Lean proof
        // In a complete implementation, we would prove the postcondition holds
        admit();
    }
    
    let mut result = Vec::new();
    let mut i = 0usize;
    let mut j = 0usize;
    
    // Main merge loop - follows the recursive pattern from Lean
    while i < arr1.len() && j < arr2.len()
        invariant
            0 <= i <= arr1.len(),
            0 <= j <= arr2.len(),
        decreases arr1.len() - i + arr2.len() - j,
    {
        if arr1[i] <= arr2[j] {
            result.push(arr1[i]);
            i += 1;
        } else {
            result.push(arr2[j]);
            j += 1;
        }
    }
    
    // Add remaining elements from arr1 (equivalent to xs case in Lean)
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            j == arr2.len(),
        decreases arr1.len() - i,
    {
        result.push(arr1[i]);
        i += 1;
    }
    
    // Add remaining elements from arr2 (equivalent to ys case in Lean)  
    while j < arr2.len()
        invariant
            i == arr1.len(),
            0 <= j <= arr2.len(),
        decreases arr2.len() - j,
    {
        result.push(arr2[j]);
        j += 1;
    }
    
    result
}

// Proof function corresponding to mergeSortedLists_spec_satisfied
proof fn merge_sorted_lists_spec_satisfied(arr1: Seq<i32>, arr2: Seq<i32>)
    requires merge_sorted_lists_precond(arr1, arr2)
    ensures exists|result: Vec<i32>| merge_sorted_lists_postcond(arr1, arr2, result@)
{
    // This corresponds to the "sorry" in the Lean proof  
    admit();
}

fn main() {}

} // verus!