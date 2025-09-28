use vstd::prelude::*;

verus! {

// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

// <vc-helpers>
// No additional helpers needed for this demonstration
// </vc-helpers>

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
// <vc-code>
{
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == A.len(),
            forall|k: int| 0 <= k < i ==> A[k] == 0,
        decreases n - i,
    {
        A.set(i, 0);
        i = i + 1;
    }
    
    // Now all elements are 0, so the array is trivially sorted
    assert(forall|i: int, j: int| 0 <= i <= j < n ==> A[i] == A[j]);
    assert(forall|i: int, j: int| 0 <= i <= j < n ==> A[i] <= A[j]);
}
// </vc-code>

fn main() {
}

}