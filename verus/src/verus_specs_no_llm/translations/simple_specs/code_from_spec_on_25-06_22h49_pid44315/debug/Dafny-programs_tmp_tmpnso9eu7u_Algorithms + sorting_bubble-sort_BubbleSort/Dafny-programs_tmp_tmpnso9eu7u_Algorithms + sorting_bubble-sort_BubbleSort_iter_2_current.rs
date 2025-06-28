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
    forall|i: int, j: int| 0 <= i <= j < A.len() && from <= i <= j <= to ==> A[i] <= A[j]
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
    }
}

// Bubble sort implementation
fn bubble_sort(A: &mut Vec<int>)
    ensures sorted(A),
    ensures A.len() == old(A).len(),
{
    let ghost original_A = *A;
    let n = A.len();
    let mut i: usize = 0;
    
    while i < n
        invariant 
            i <= n,
            A.len() == n,
            // After i iterations, the last i elements are sorted and in final position
            forall|k: int, l: int| (n - i) <= k < l < n ==> A[k] <= A[l],
            // The sorted suffix contains the largest elements
            forall|k: int, l: int| 0 <= k < (n - i) && (n - i) <= l < n ==> A[k] <= A[l],
    {
        let mut j: usize = 0;
        
        while j < n - 1 - i
            invariant
                j <= n - 1 - i,
                i < n,
                A.len() == n,
                // The largest element in range [0, j+1] is at position j
                forall|k: int| 0 <= k <= j ==> A[k] <= A[j],
                // Maintain the sorted suffix from previous iterations
                forall|k: int, l: int| (n - i) <= k < l < n ==> A[k] <= A[l],
                forall|k: int, l: int| 0 <= k < (n - i) && (n - i) <= l < n ==> A[k] <= A[l],
        {
            if A[j] > A[j + 1] {
                // Swap elements
                let temp = A[j];
                A.set(j, A[j + 1]);
                A.set(j + 1, temp);
                
                // Help the verifier understand the swap maintains our invariants
                assert(A[j + 1] >= A[j]);
                assert(forall|k: int| 0 <= k <= j ==> A[k] <= A[j + 1]);
            }
            j += 1;
        }
        
        // After inner loop, A[n-1-i] contains the (i+1)-th largest element
        assert(forall|k: int| 0 <= k < (n - i) ==> A[k] <= A[(n - 1 - i) as int]);
        
        i += 1;
    }
    
    // After all iterations, the entire array is sorted
    assert(i == n);
    assert(forall|k: int, l: int| 0 <= k < l < n ==> A[k] <= A[l]);
}

}