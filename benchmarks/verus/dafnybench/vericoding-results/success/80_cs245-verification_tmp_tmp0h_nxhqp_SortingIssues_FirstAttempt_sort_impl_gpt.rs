use vstd::prelude::*;

verus! {

// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

// <vc-helpers>
// no helpers needed
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
    let mut k: usize = 0;
    while k < n
        invariant
            A.len() == n,
            k <= n,
            forall|i: int| (0 <= i && i < k as int) ==> A[i] == 0i32
        decreases n - k
    {
        let old_k = k;
        assert(old_k < n);
        A[old_k] = 0i32;
        k = old_k + 1;

        assert forall |i: int| (0 <= i && i < k as int) ==> A[i] == 0i32 by {
            if 0 <= i && i < k as int {
                if i < old_k as int {
                    // unchanged indices remain 0 by the previous invariant
                } else {
                    assert(i >= old_k as int);
                    assert(i < old_k as int + 1);
                    assert(i == old_k as int);
                    assert(A[i] == 0i32);
                }
            }
        }
    }

    assert(k == n);

    assert forall |i: int, j: int| (0 <= i && i <= j && j < n) ==> A[i] <= A[j] by {
        if 0 <= i && i <= j && j < n {
            assert(j < k as int);
            assert(i < k as int);
            assert(A[i] == 0i32);
            assert(A[j] == 0i32);
        }
    }
}
// </vc-code>

fn main() {
}

}