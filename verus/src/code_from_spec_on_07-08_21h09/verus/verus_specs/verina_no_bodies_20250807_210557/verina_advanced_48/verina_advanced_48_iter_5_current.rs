use vstd::prelude::*;

verus! {

// Precondition for mergeSort - always true in this case
spec fn merge_sort_precond(list: Seq<int>) -> bool {
    true
}

// Helper function to check if a sequence is sorted
spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Helper function to check if two sequences are permutations
spec fn is_permutation(s1: Seq<int>, s2: Seq<int>) -> bool {
    s1.to_multiset() =~= s2.to_multiset()
}

// Helper function to merge two sorted sequences
fn merge(left: Vec<int>, right: Vec<int>) -> (result: Vec<int>)
    requires 
        is_sorted(left@),
        is_sorted(right@),
    ensures 
        is_sorted(result@),
        is_permutation(result@, left@ + right@),
{
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < left.len() && j < right.len()
        invariant
            0 <= i <= left.len(),
            0 <= j <= right.len(),
            is_sorted(result@),
            is_permutation(result@, left@.subrange(0, i as int) + right@.subrange(0, j as int)),
            forall|k: int| 0 <= k < result.len() ==> 
                (i < left.len() ==> result@[k] <= left@[i as int]) &&
                (j < right.len() ==> result@[k] <= right@[j as int]),
    {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    
    while i < left.len()
        invariant
            0 <= i <= left.len(),
            j == right.len(),
            is_sorted(result@),
            is_permutation(result@, left@.subrange(0, i as int) + right@),
            forall|k: int| 0 <= k < result.len() && i < left.len() ==> result@[k] <= left@[i as int],
    {
        result.push(left[i]);
        i += 1;
    }
    
    while j < right.len()
        invariant
            i == left.len(),
            0 <= j <= right.len(),
            is_sorted(result@),
            is_permutation(result@, left@ + right@.subrange(0, j as int)),
            forall|k: int| 0 <= k < result.len() && j < right.len() ==> result@[k] <= right@[j as int],
    {
        result.push(right[j]);
        j += 1;
    }
    
    result
}

// Simple stub implementation
fn merge_sort(list: Vec<int>) -> (result: Vec<int>)
    requires merge_sort_precond(list@),
    ensures 
        is_sorted(result@),
        is_permutation(result@, list@),
    decreases list.len(),
{
    if list.len() <= 1 {
        return list;
    }
    
    let mid = list.len() / 2;
    let mut left = Vec::new();
    let mut right = Vec::new();
    
    let mut i = 0;
    while i < mid
        invariant
            0 <= i <= mid,
            mid <= list.len(),
            left.len() == i,
            is_permutation(left@, list@.subrange(0, i as int)),
    {
        left.push(list[i]);
        i += 1;
    }
    
    while i < list.len()
        invariant
            mid <= i <= list.len(),
            left.len() == mid,
            right.len() == i - mid,
            is_permutation(left@, list@.subrange(0, mid as int)),
            is_permutation(right@, list@.subrange(mid as int, i as int)),
    {
        right.push(list[i]);
        i += 1;
    }
    
    let sorted_left = merge_sort(left);
    let sorted_right = merge_sort(right);
    
    merge(sorted_left, sorted_right)
}

// Postcondition specification
spec fn merge_sort_postcond(list: Seq<int>, result: Seq<int>) -> bool {
    is_sorted(result) && is_permutation(list, result)
}

fn main() {
    /* code modified by LLM (iteration 1): Fixed int literal syntax by removing invalid suffixes and using proper int conversion */
    let test_vec: Vec<int> = vec![3, 1, 4, 1, 5, 9, 2, 6];
    let sorted = merge_sort(test_vec);
    
    // Convert to i32 vector for printing since int doesn't implement Debug
    let mut sorted_i32: Vec<i32> = Vec::new();
    for i in 0..sorted.len() {
        let val: int = sorted[i];
        sorted_i32.push(val as i32);
    }
    println!("Sorted vector: {:?}", sorted_i32);
}

}