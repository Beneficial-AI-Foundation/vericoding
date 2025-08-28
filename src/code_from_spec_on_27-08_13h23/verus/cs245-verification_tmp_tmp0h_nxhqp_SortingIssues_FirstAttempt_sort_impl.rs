use vstd::prelude::*;

verus! {

// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

// <vc-helpers>
// Helper function to check if a segment of the vector is sorted
spec fn is_sorted_segment(v: Vec<i32>, start: int, end: int) -> bool
    decreases end - start
{
    if start >= end {
        true
    } else {
        forall|i: int, j: int| start <= i <= j < end ==> v[i] <= v[j]
    }
}

// Helper function for swap invariant
spec fn swap_preserves_multiset(v1: Vec<i32>, v2: Vec<i32>) -> bool {
    v1.len() == v2.len() && forall|x: i32| v1.count(x) == v2.count(x)
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sort(A: &mut Vec<i32>, n: usize)
    requires 
        n == old(A).len(),
        n >= 0,  // This is always true for usize, but kept for consistency
    ensures
        forall|i: int, j: int| 0 <= i <= j < n ==> A[i] <= A[j],  // This states that A is sorted.

//Can we write code that does not sort A that still satisfies the requirements? 
//Consider the following program:
// </vc-spec>
// </vc-spec>

// <vc-code>
fn sort(A: &mut Vec<i32>, n: usize)
    requires
        n == old(A).len(),
    ensures
        forall|i: int, j: int| 0 <= i <= j < n ==> A[i] <= A[j],
{
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|k: int, l: int| 0 <= k <= l < i as int ==> A[k] <= A[l],
            swap_preserves_multiset(*old(A), *A),
    {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        
        while j < n
            invariant
                i < n,
                min_idx >= i,
                min_idx < n,
                j <= n,
                forall|k: int| i as int <= k < j as int ==> A[min_idx as int] <= A[k],
                forall|k: int, l: int| 0 <= k <= l < i as int ==> A[k] <= A[l],
                swap_preserves_multiset(*old(A), *A),
        {
            if A[j] < A[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let tmp = A[i];
            A.set(i, A[min_idx]);
            A.set(min_idx, tmp);
        }
        
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}