use vstd::prelude::*;

verus! {

// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

// <vc-helpers>
proof fn lemma_all_zero_sorted(A: &Vec<i32>)
    requires
        forall |i: int| 0 <= i < A.len() ==> A[i] == 0,
    ensures
        forall |i: int, j: int| 0 <= i <= j < A.len() ==> A[i] <= A[j]
{
    assert forall |i: int, j: int| 0 <= i <= j < A.len() implies A[i] <= A[j]
    by {
        assert(A[i] == 0);
        assert(A[j] == 0);
    }
}
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
    for i in 0..n
        invariant 
            A.len() == n,
            forall |j: int| 0 <= j < i ==> A[j] == 0
    {
        A[i] = 0;
    }
    proof {
        lemma_all_zero_sorted(A);
    }
}
// </vc-code>

fn main() {
}

}