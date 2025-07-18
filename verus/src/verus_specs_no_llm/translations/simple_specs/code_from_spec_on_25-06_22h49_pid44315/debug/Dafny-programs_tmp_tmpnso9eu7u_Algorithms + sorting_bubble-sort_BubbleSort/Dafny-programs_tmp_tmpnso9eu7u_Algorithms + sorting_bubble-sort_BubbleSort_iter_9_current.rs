use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Define what it means for an array to be sorted
spec fn sorted(A: &Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < A.len() ==> A[i] <= A[j]
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

// Simplified bubble sort implementation
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
            // The last i elements are sorted
            forall|k1: int, k2: int| (n as int) - (i as int) <= k1 <= k2 < n ==> A[k1] <= A[k2],
            // Elements in sorted suffix are >= elements before it
            forall|k1: int, k2: int| 0 <= k1 < (n as int) - (i as int) && (n as int) - (i as int) <= k2 < n ==> A[k1] <= A[k2],
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
                // The largest element in A[0..=j] is at position j
                forall|k: int| 0 <= k <= j ==> A[k] <= A[j as int],
                // Preserve the sorted suffix from outer loop
                forall|k1: int, k2: int| (n as int) - (i as int) <= k1 <= k2 < n ==> A[k1] <= A[k2],
                forall|k1: int, k2: int| 0 <= k1 < (n as int) - (i as int) && (n as int) - (i as int) <= k2 < n ==> A[k1] <= A[k2],
        {
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
    
    // Final assertion that the array is sorted
    assert(sorted(A));
}

}