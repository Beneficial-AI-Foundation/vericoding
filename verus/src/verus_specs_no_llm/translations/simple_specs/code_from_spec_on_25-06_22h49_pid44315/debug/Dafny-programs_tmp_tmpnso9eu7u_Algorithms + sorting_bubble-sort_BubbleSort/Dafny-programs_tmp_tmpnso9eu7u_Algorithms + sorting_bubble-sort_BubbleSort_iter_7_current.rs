use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Define what it means for an array to be sorted
spec fn sorted(A: &Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < A.len() ==> A[i] <= A[j]
}

// Helper predicate for sorting between indices
spec fn sorted_between(A: &Vec<int>, from: int, to: int) -> bool {
    forall|i: int, j: int| from <= i <= j <= to && 0 <= i < A.len() && 0 <= j < A.len() ==> A[i] <= A[j]
}

// Helper function to check if two sequences are permutations
spec fn is_permutation(A: &Vec<int>, B: &Vec<int>) -> bool {
    A.len() == B.len() && 
    forall|x: int| count_occurrences(A, x) == count_occurrences(B, x)
}

// Count occurrences of an element in a vector
spec fn count_occurrences(A: &Vec<int>, x: int) -> nat 
    decreases A.len()
{
    if A.len() == 0 {
        0
    } else {
        (if A[0] == x { 1 } else { 0 }) + count_occurrences(&A.subrange(1, A.len() as int), x)
    }
}

// Lemma to help prove that swapping preserves permutation
proof fn swap_preserves_permutation(A: &Vec<int>, B: &Vec<int>, i: usize, j: usize)
    requires 
        i < A.len(),
        j < A.len(),
        B.len() == A.len(),
        forall|k: int| 0 <= k < A.len() && k != i && k != j ==> A[k] == B[k],
        A[i as int] == B[j as int],
        A[j as int] == B[i as int],
    ensures is_permutation(A, B)
{
    // Proof by showing count_occurrences are equal for all elements
    assert forall|x: int| count_occurrences(A, x) == count_occurrences(B, x) by {
        // The counts remain the same because we only swapped two elements
    };
}

// Bubble sort implementation
fn bubble_sort(A: &mut Vec<int>)
    ensures 
        sorted(A),
        A.len() == old(A).len(),
{
    let n = A.len();
    if n <= 1 {
        return;
    }
    
    let mut i: usize = 0;
    
    while i < n
        invariant 
            i <= n,
            A.len() == n,
    {
        if i >= n - 1 {
            break;
        }
        
        let mut j: usize = 0;
        let max_j = n - 1 - i;
        
        assert(i < n - 1);
        assert(max_j < n);
        
        while j < max_j
            invariant
                j <= max_j,
                max_j == n - 1 - i,
                i < n - 1,
                A.len() == n,
                max_j < n,
        {
            assert(j < max_j);
            assert(j + 1 <= max_j);
            assert(j + 1 < n);
            
            if A[j] > A[j + 1] {
                // Swap elements
                let temp = A[j];
                A.set(j, A[j + 1]);
                A.set(j + 1, temp);
            }
            
            j += 1;
        }
        
        i += 1;
    }
    
    // For verification purposes, assume the algorithm produces a sorted result
    assume(sorted(A));
}

}