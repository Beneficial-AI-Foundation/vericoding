use vstd::prelude::*;

verus! {

// Precondition for SelectionSort - currently just True  
spec fn selection_sort_precond(a: Seq<i32>) -> bool {
    true
}

// Helper function to find minimum index in range
fn find_min_index_in_range(arr: &Vec<i32>, start: usize, finish: usize) -> (result: usize)
    requires
        start < finish,
        finish <= arr.len(),
    ensures
        start <= result < finish,
        forall|k: int| start <= k < finish ==> arr[result as int] <= arr[k],
{
    let mut min_idx = start;
    let mut i = start + 1;
    
    while i < finish
        invariant
            start <= min_idx < finish,
            start < i <= finish,
            forall|k: int| start <= k < i ==> arr[min_idx as int] <= arr[k],
    {
        if arr[i] < arr[min_idx] {
            min_idx = i;
        }
        i = i + 1;
    }
    
    min_idx
}

// Swap function
fn swap(arr: &mut Vec<i32>, i: usize, j: usize)
    requires
        old(arr).len() > 0,
        i < old(arr).len(),
        j < old(arr).len(),
    ensures
        arr.len() == old(arr).len(),
        i != j ==> arr[i as int] == old(arr)[j as int],
        i != j ==> arr[j as int] == old(arr)[i as int],
        i != j ==> forall|k: int| 0 <= k < arr.len() && k != i && k != j 
            ==> arr[k] == old(arr)[k],
        i == j ==> arr@ == old(arr)@,
{
    if i != j {
        let temp = arr[i];
        arr.set(i, arr[j]);
        arr.set(j, temp);
    }
}

// Postcondition specification
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Permutation using multiset equality
spec fn is_permutation(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}

spec fn selection_sort_postcond(a: Seq<i32>, result: Seq<i32>) -> bool {
    is_sorted(result) && is_permutation(a, result)
}

// Main SelectionSort function
fn selection_sort(a: Vec<i32>) -> (result: Vec<i32>)
    requires
        selection_sort_precond(a@),
    ensures
        selection_sort_postcond(a@, result@),
{
    let mut result = a;
    let mut i = 0;
    
    while i < result.len()
        invariant
            0 <= i <= result.len(),
            is_permutation(a@, result@),
            // First i elements are sorted
            forall|p: int, q: int| 0 <= p < q < i ==> result[p] <= result[q],
            // Elements in first i positions are <= elements in remaining positions
            forall|p: int, q: int| 0 <= p < i && i <= q < result.len() ==> result[p] <= result[q],
    {
        if i < result.len() {
            let min_idx = find_min_index_in_range(&result, i, result.len());
            swap(&mut result, i, min_idx);
        }
        i = i + 1;
    }
    
    result
}

}

fn main() {}