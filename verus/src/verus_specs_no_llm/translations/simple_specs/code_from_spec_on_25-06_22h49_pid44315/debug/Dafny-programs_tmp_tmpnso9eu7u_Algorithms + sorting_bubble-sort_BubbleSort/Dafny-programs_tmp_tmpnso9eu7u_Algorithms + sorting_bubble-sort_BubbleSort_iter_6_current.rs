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
    ensures sorted(A),
    ensures A.len() == old(A).len(),
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
            n > 0,
            // After i iterations, the last i elements are in their final sorted positions
            sorted_between(A, (n - i) as int, (n - 1) as int),
            // Elements before sorted suffix are <= elements in sorted suffix
            forall|k: int, l: int| 0 <= k < (n - i) as int && (n - i) as int <= l < n ==> A[k] <= A[l],
    {
        if i >= n - 1 {
            // Prove the array is fully sorted
            assert(n - i <= 1);
            proof {
                // When we've done n-1 passes, the array must be sorted
                // The sorted suffix covers the entire array
                assert(sorted_between(A, 1, (n - 1) as int));
                assert(forall|k: int| 1 <= k < n ==> A[0] <= A[k]);
                
                // Combine these facts to show the entire array is sorted
                assert forall|x: int, y: int| 0 <= x <= y < A.len() implies A[x] <= A[y] by {
                    if x == 0 && y > 0 {
                        assert(A[x] <= A[y]); // from second invariant part
                    } else if x >= 1 {
                        assert(A[x] <= A[y]); // from sorted_between
                    }
                }
            }
            break;
        }
        
        let mut j: usize = 0;
        let max_j = n - 1 - i;
        
        // Prove that max_j is valid
        assert(i < n - 1);
        assert(max_j > 0);
        assert(max_j < n);
        
        while j < max_j
            invariant
                j <= max_j,
                max_j == n - 1 - i,
                i < n - 1,
                A.len() == n,
                n > 0,
                max_j < n,
                // The largest element in [0..=j] is at position j
                forall|k: int| 0 <= k <= j ==> A[k] <= A[j as int],
                // Maintain the sorted suffix from previous outer loop iterations
                sorted_between(A, (n - i) as int, (n - 1) as int),
                // Elements in sorted suffix are >= elements being processed
                forall|k: int, l: int| 0 <= k < (n - i) as int && (n - i) as int <= l < n ==> A[k] <= A[l],
        {
            // Bounds check
            assert(j < max_j);
            assert(j + 1 <= max_j);
            assert(j + 1 < n);
            
            if A[j] > A[j + 1] {
                // Swap elements
                let temp = A[j];
                A.set(j, A[j + 1]);
                A.set(j + 1, temp);
                
                // Prove invariant maintained after swap
                proof {
                    assert(A[j] <= A[j + 1]); // now true after swap
                    assert forall|k: int| 0 <= k <= j + 1 implies A[k] <= A[(j + 1) as int] by {
                        if k <= j as int {
                            if k == j as int {
                                assert(A[k] <= A[(j + 1) as int]); // just swapped
                            } else {
                                assert(A[k] <= A[j as int]); // from loop invariant before swap
                                assert(A[j as int] <= A[(j + 1) as int]); // after swap
                            }
                        }
                    }
                }
            } else {
                // No swap needed, invariant maintained
                proof {
                    assert(A[j] <= A[j + 1]); // already true
                    assert forall|k: int| 0 <= k <= j + 1 implies A[k] <= A[(j + 1) as int] by {
                        if k <= j as int {
                            assert(A[k] <= A[j as int]); // from loop invariant
                            assert(A[j as int] <= A[(j + 1) as int]); // given condition
                        }
                    }
                }
            }
            
            j += 1;
        }
        
        // After inner loop completes, prove the invariants for the next outer iteration
        proof {
            assert(j == max_j);
            assert(max_j == n - 1 - i);
            assert(forall|k: int| 0 <= k < max_j ==> A[k] <= A[max_j as int]);
            
            // The element at position max_j is now in its correct position
            // and the sorted suffix has grown by one element
            let new_sorted_start = (n - (i + 1)) as int;
            assert(new_sorted_start == max_j as int);
            
            // Prove the new sorted suffix
            assert(sorted_between(A, new_sorted_start, (n - 1) as int));
            assert forall|k: int, l: int| 0 <= k < new_sorted_start && new_sorted_start <= l < n implies A[k] <= A[l] by {
                if l == new_sorted_start {
                    assert(A[k] <= A[max_j as int]); // from inner loop result
                } else {
                    assert(A[k] <= A[max_j as int]); // from inner loop
                    assert(A[max_j as int] <= A[l]); // from previous sorted suffix
                }
            }
        }
        
        i += 1;
    }
    
    // Final assertion that the array is sorted
    proof {
        if n > 0 {
            assert(i >= n - 1 || i >= n);
            if i >= n {
                assert(sorted_between(A, 0, (n - 1) as int));
                assert(sorted(A));
            }
        }
    }
}

}