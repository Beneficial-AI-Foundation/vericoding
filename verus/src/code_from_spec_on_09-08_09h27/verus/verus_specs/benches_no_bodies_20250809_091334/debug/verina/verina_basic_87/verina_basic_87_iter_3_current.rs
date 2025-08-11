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
{
    let mut min_idx = start;
    let mut i = start + 1;
    
    /* code modified by LLM (iteration 1): Added decreases clause to fix termination verification */
    while i < finish
        invariant
            start <= min_idx < finish,
            start < i <= finish,
        decreases finish - i
    {
        if arr[i] < arr[min_idx] {
            min_idx = i;
        }
        i += 1;
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
    /* code modified by LLM (iteration 1): Fixed borrow checker issue by storing arr[j] in temp before mutation */
    if i != j {
        let temp = arr[i];
        let temp_j = arr[j];
        arr.set(i, temp_j);
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
    let mut arr = a;
    let n = arr.len();
    
    if n <= 1 {
        return arr;
    }
    
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): Added decreases clause to fix termination verification */
    while i < n - 1
        invariant
            i <= n,
            n == arr.len(),
            arr.len() == a.len(),
            is_permutation(a@, arr@),
            forall|k1: int, k2: int| 0 <= k1 < i && i <= k2 < arr.len() ==> arr[k1] <= arr[k2],
            forall|k1: int, k2: int| 0 <= k1 < k2 < i ==> arr[k1] <= arr[k2],
        decreases n - i
    {
        let min_idx = find_min_index_in_range(&arr, i, n);
        
        proof {
            assert(arr@.to_multiset() == arr@.to_multiset());
        }
        
        swap(&mut arr, i, min_idx);
        
        proof {
            assert(is_permutation(a@, arr@));
        }
        
        i += 1;
    }
    
    arr
}

}

fn main() {}