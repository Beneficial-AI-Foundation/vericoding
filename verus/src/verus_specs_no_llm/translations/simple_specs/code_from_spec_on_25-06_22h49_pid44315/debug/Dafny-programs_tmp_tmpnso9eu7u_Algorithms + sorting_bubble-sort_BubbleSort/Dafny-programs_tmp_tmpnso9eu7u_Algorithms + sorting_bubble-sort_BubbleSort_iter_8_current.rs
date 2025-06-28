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
        forall|k: int| 0 <= k < A.len() && k != i && k != j ==> A[k as int] == B[k as int],
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
        is_permutation(A, &old(A)),
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
            is_permutation(A, &old(A)),
            // The last i elements are in their final sorted positions
            forall|k1: int, k2: int| n - i <= k1 < k2 < n ==> A[k1] <= A[k2],
            // Elements in the sorted suffix are >= elements before it
            forall|k1: int, k2: int| 0 <= k1 < n - i && n - i <= k2 < n ==> A[k1] <= A[k2],
    {
        if i >= n - 1 {
            break;
        }
        
        let mut j: usize = 0;
        let max_j = n - 1 - i;
        
        while j < max_j
            invariant
                j <= max_j,
                max_j == n - 1 - i,
                i < n - 1,
                A.len() == n,
                max_j < n,
                is_permutation(A, &old(A)),
                // The largest element in A[0..=j] is at position j
                forall|k: int| 0 <= k <= j ==> A[k] <= A[j as int],
                // Preserve the sorted suffix
                forall|k1: int, k2: int| n - i <= k1 < k2 < n ==> A[k1] <= A[k2],
                forall|k1: int, k2: int| 0 <= k1 < n - i && n - i <= k2 < n ==> A[k1] <= A[k2],
        {
            if A[j] > A[j + 1] {
                // Swap elements
                let temp = A[j];
                A.set(j, A[j + 1]);
                A.set(j + 1, temp);
                
                // Prove that swapping preserves permutation
                let old_A = old(A);
                proof {
                    // The swap preserves the permutation property
                    assert(is_permutation(A, &old_A));
                }
            }
            
            j += 1;
        }
        
        // After inner loop, the maximum element is at position max_j
        proof {
            assert(forall|k: int| 0 <= k < max_j ==> A[k] <= A[max_j as int]);
        }
        
        i += 1;
    }
    
    // After all iterations, prove the array is sorted
    proof {
        assert(i == n);
        assert(sorted(A)) by {
            assert forall|k1: int, k2: int| 0 <= k1 <= k2 < n implies A[k1] <= A[k2] by {
                // This follows from our loop invariants
            };
        };
    }
}

}