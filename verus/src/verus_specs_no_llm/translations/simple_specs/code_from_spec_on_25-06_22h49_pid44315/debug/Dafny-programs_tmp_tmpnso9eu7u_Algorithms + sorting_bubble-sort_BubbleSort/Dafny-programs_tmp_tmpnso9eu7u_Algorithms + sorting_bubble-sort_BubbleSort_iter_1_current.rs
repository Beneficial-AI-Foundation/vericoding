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

// Bubble sort implementation
fn bubble_sort(A: &mut Vec<int>)
    ensures sorted(A),
    ensures is_permutation(A, old(A)),
{
    let n = A.len();
    let mut i: usize = 0;
    
    while i < n
        invariant 
            i <= n,
            A.len() == n,
            is_permutation(A, old(A)),
            // Elements from i to n-1 are in their final sorted positions
            forall|k: int, l: int| i <= k < l < n ==> A[k] <= A[l],
            // Elements 0 to i-1 are <= all elements from i to n-1
            forall|k: int, l: int| 0 <= k < i && i <= l < n ==> A[k] <= A[l],
    {
        let mut j: usize = 0;
        
        while j < n - 1 - i
            invariant
                j <= n - 1 - i,
                i < n,
                A.len() == n,
                is_permutation(A, old(A)),
                // Largest element in 0..j+1 has bubbled to position j
                forall|k: int| 0 <= k <= j ==> A[k] <= A[j],
                // Maintain sorted suffix property
                forall|k: int, l: int| i <= k < l < n ==> A[k] <= A[l],
                forall|k: int, l: int| 0 <= k < i && i <= l < n ==> A[k] <= A[l],
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
}

}

The implementation includes:





   - **Outer loop**: Iterates through positions from right to left
   - **Inner loop**: Bubbles the largest remaining element to its correct position
   - **Loop invariants**: Maintain properties about the sorted suffix, permutation preservation, and partial sorting progress
   - **Swapping**: When adjacent elements are out of order, they are swapped

The key insight is that bubble sort works by repeatedly passing through the array, swapping adjacent out-of-order elements, which gradually moves larger elements toward the end. The invariants capture that after each outer loop iteration, the suffix of the array is sorted and contains the largest elements in their final positions.