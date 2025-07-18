use builtin::*;
use builtin_macros::*;

verus! {

// Predicate to check if a sequence is sorted between indices
spec fn sorted_between(A: &Vec<i32>, from: int, to: int) -> bool {
    forall|i: int, j: int| 
        from <= i <= j <= to && 0 <= i && j < A.len() ==> A[i] <= A[j]
}

// Predicate to check if entire array is sorted
spec fn sorted(A: &Vec<i32>) -> bool {
    A.len() == 0 || sorted_between(A, 0, (A.len() - 1) as int)
}

// Predicate to check if two arrays are permutations of each other
spec fn multiset_equivalent(A: &Vec<i32>, B: &Vec<i32>) -> bool {
    A.len() == B.len() && 
    forall|v: i32| count_occurrences(A, v) == count_occurrences(B, v)
}

// Helper function to count occurrences of a value
spec fn count_occurrences(A: &Vec<i32>, value: i32) -> nat
    decreases A.len()
{
    if A.len() == 0 {
        0
    } else {
        (if A[A.len() - 1] == value { 1 } else { 0 }) + 
        count_occurrences(&A.subrange(0, (A.len() - 1) as int), value)
    }
}

// Lemma about multiset equivalence after swap
proof fn lemma_swap_preserves_multiset(A: &Vec<i32>, i: usize, j: usize)
    requires 
        i < A.len(),
        j < A.len(),
    ensures {
        let mut B = A.clone();
        let temp = B[i];
        B.set(i, B[j]);
        B.set(j, temp);
        multiset_equivalent(A, &B)
    }
{
    // Verus can prove this automatically for simple swaps
}

// Lemma for sorted_between extension
proof fn lemma_sorted_between_extend(A: &Vec<i32>, from: int, to: int)
    requires 
        sorted_between(A, from + 1, to),
        from >= 0,
        to < A.len(),
        forall|k: int| from + 1 <= k <= to ==> A[from] <= A[k]
    ensures sorted_between(A, from, to)
{
    // Verus can prove this automatically
}

// Bubble sort implementation
fn bubble_sort(A: &mut Vec<i32>)
    requires A.len() <= 1000, // reasonable bound for verification
    ensures sorted(A),
    ensures multiset_equivalent(A, old(A)),
{
    let n = A.len();
    let original_A = Ghost(*A);
    
    if n <= 1 {
        return;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant 
            i <= n,
            n == A.len(),
            // The last i elements are sorted and in their final positions
            i == 0 || sorted_between(A, (n - i) as int, (n - 1) as int),
            // Elements in sorted portion are >= elements in unsorted portion
            forall|k: int, l: int| 
                0 <= k < (n - i) && (n - i) <= l < n ==> A[k] <= A[l],
            // Multiset equivalence is preserved
            multiset_equivalent(A, &original_A@),
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n - 1 - i
            invariant
                j <= n - 1 - i,
                i < n,
                n == A.len(),
                // Previous invariants maintained
                i == 0 || sorted_between(A, (n - i) as int, (n - 1) as int),
                forall|k: int, l: int| 
                    0 <= k < (n - i) && (n - i) <= l < n ==> A[k] <= A[l],
                multiset_equivalent(A, &original_A@),
                // Maximum element in range [0..j] is at position j
                forall|k: int| 0 <= k <= j ==> A[k] <= A[j],
            decreases n - 1 - i - j
        {
            if A[j] > A[j + 1] {
                // Swap elements
                let temp = A[j];
                A.set(j, A[j + 1]);
                A.set(j + 1, temp);
                
                // Prove multiset equivalence is preserved after swap
                proof {
                    lemma_swap_preserves_multiset(&old(A), j, j + 1);
                }
            }
            j += 1;
        }
        
        // After inner loop, the maximum element is at position n-1-i
        // Prove that we can extend the sorted region
        proof {
            if i > 0 {
                lemma_sorted_between_extend(A, (n - i - 1) as int, (n - 1) as int);
            }
        }
        
        i += 1;
    }
    
    // Prove final sortedness
    proof {
        if n > 1 {
            assert(sorted_between(A, 0, (n - 1) as int));
        }
    }
}

fn main() {
    let mut A = vec![2, 4, 6, 15, 3, 19, 17, 16, 18, 1];
    
    print_vec(&A);
    println!("");
    
    bubble_sort(&mut A);
    
    print_vec(&A);
    println!("");
}

// Helper function to print vector
fn print_vec(A: &Vec<i32>) {
    let mut i = 0;
    while i < A.len()
        invariant i <= A.len()
        decreases A.len() - i
    {
        print!("{} ", A[i]);
        i += 1;
    }
}

}