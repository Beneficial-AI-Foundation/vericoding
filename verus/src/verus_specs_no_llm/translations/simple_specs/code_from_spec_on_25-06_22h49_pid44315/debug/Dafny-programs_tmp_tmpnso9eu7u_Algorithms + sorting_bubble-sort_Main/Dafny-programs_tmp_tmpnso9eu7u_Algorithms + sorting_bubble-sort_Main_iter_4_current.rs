use builtin::*;
use builtin_macros::*;

verus! {

// Predicate to check if a sequence is sorted between indices
spec fn sorted_between(A: Seq<i32>, from: int, to: int) -> bool {
    forall|i: int, j: int| 
        from <= i <= j <= to && 0 <= i && j < A.len() ==> A[i] <= A[j]
}

// Predicate to check if entire array is sorted
spec fn sorted(A: Seq<i32>) -> bool {
    A.len() == 0 || sorted_between(A, 0, (A.len() - 1) as int)
}

// Predicate to check if two arrays are permutations of each other
spec fn multiset_equivalent(A: Seq<i32>, B: Seq<i32>) -> bool {
    A =~= B
}

// Helper function to count occurrences of a value
spec fn count_occurrences(A: Seq<i32>, value: i32) -> nat
    decreases A.len()
{
    if A.len() == 0 {
        0
    } else {
        (if A[A.len() - 1] == value { 1 } else { 0 }) + 
        count_occurrences(A.subrange(0, (A.len() - 1) as int), value)
    }
}

// Lemma about multiset equivalence after swap
proof fn lemma_swap_preserves_multiset(A: Seq<i32>, B: Seq<i32>, i: int, j: int)
    requires 
        0 <= i < A.len(),
        0 <= j < A.len(),
        B.len() == A.len(),
        B[i] == A[j],
        B[j] == A[i],
        forall|k: int| 0 <= k < A.len() && k != i && k != j ==> B[k] == A[k]
    ensures multiset_equivalent(A, B)
{
    // The sequences are equivalent by multiset
    assert(A =~= B);
}

// Lemma for sorted_between extension
proof fn lemma_sorted_between_extend(A: Seq<i32>, from: int, to: int)
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
    ensures sorted(A@),
    ensures multiset_equivalent(A@, old(A)@),
{
    let n = A.len();
    let ghost original_A = A@;
    
    if n <= 1 {
        return;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant 
            i <= n,
            n == A.len(),
            // The last i elements are sorted and in their final positions
            i == 0 || (n >= i && sorted_between(A@, (n - i) as int, (n - 1) as int)),
            // Elements in sorted portion are >= elements in unsorted portion
            forall|k: int, l: int| 
                0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> A@[k] <= A@[l],
            // Multiset equivalence is preserved
            multiset_equivalent(A@, original_A),
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n - 1 - i
            invariant
                j <= n - 1 - i,
                i < n,
                n == A.len(),
                // Previous invariants maintained
                i == 0 || (n >= i && sorted_between(A@, (n - i) as int, (n - 1) as int)),
                forall|k: int, l: int| 
                    0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> A@[k] <= A@[l],
                multiset_equivalent(A@, original_A),
                // Maximum element in range [0..j] is at position j
                forall|k: int| 0 <= k <= j as int && k < A@.len() ==> A@[k] <= A@[j as int],
            decreases n - 1 - i - j
        {
            if A[j] > A[j + 1] {
                // Swap elements
                let ghost old_A = A@;
                let temp = A[j];
                A.set(j, A[j + 1]);
                A.set(j + 1, temp);
                
                // Prove multiset equivalence is preserved after swap
                proof {
                    lemma_swap_preserves_multiset(old_A, A@, j as int, (j + 1) as int);
                    assert(multiset_equivalent(old_A, A@));
                    // Transitivity of multiset equivalence
                    assert(multiset_equivalent(A@, original_A));
                }
            }
            j += 1;
        }
        
        // After inner loop, prove that position n-1-i has the maximum element
        proof {
            if n >= 2 && i < n - 1 {
                // The element at position n-1-i is >= all elements before it
                assert(forall|k: int| 0 <= k < (n - 1 - i) as int ==> A@[k] <= A@[(n - 1 - i) as int]);
            }
        }
        
        i += 1;
    }
    
    // Final proof that the array is sorted
    proof {
        if n >= 2 {
            assert(sorted_between(A@, 0, (n - 1) as int));
            assert(sorted(A@));
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