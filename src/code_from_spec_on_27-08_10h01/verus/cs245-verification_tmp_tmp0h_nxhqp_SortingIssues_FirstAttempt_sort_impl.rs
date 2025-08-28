use vstd::prelude::*;

verus! {

// Sorting: 
//        Pre/Post Condition Issues - An investigation 
//                                      -- Stephanie McIntyre
// Based on examples in class 

// First Attempt at specifying requirements for sorting array A in incrementing order
// We want our Hoare triple of (|Pre-Condition|) Code (|Post-Condition|) to hold iff A is properly sorted.

// <vc-helpers>
spec fn is_sorted(v: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j]
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
{
    if n == 0 {
        return;
    }
    
    // Simple bubble sort implementation
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            n == A.len(),
            forall|x: int, y: int| 0 <= x <= y < i ==> A[x] <= A[y],
            forall|x: int, y: int| 0 <= x < i && i <= y < n ==> A[x] <= A[y],
        decreases n - i,
    {
        let mut j = 0;
        while j < n - 1 - i
            invariant
                j <= n - 1 - i,
                i < n,
                n == A.len(),
                forall|x: int, y: int| 0 <= x <= y < i ==> A[x] <= A[y],
                forall|x: int, y: int| 0 <= x < i && i <= y < n ==> A[x] <= A[y],
                forall|k: int| 0 <= k < j ==> A[k] <= A[k + 1],
                forall|k: int| j < k < n - 1 - i ==> A[k] <= A[n - 1 - i],
            decreases n - 1 - i - j,
        {
            if A[j] > A[j + 1] {
                let temp = A[j];
                let next_val = A[j + 1];
                A.set(j, next_val);
                A.set(j + 1, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}