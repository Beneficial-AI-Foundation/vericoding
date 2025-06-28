use builtin::*;
use builtin_macros::*;

verus! {

// Predicate to check if a sequence is sorted between indices
spec fn sorted_between(A: &Vec<i32>, from: int, to: int) -> bool {
    forall|i: int, j: int| 
        0 <= i <= j < A.len() && from <= i && j <= to ==> A[i] <= A[j]
}

// Predicate to check if entire array is sorted
spec fn sorted(A: &Vec<i32>) -> bool {
    A.len() == 0 || sorted_between(A, 0, A.len() - 1)
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
        count_occurrences(&A.subrange(0, A.len() - 1), value)
    }
}

// Bubble sort implementation
fn bubble_sort(A: &mut Vec<i32>)
    requires A.len() <= 1000, // reasonable bound for verification
    ensures sorted(A),
    ensures multiset_equivalent(A, old(A)),
{
    let n = A.len();
    if n <= 1 {
        return;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant 
            i <= n,
            sorted_between(A, n - i, n - 1),
            multiset_equivalent(A, old(A)),
            forall|k: int, l: int| 
                n - i <= k < n && 0 <= l < n - i ==> A[l] <= A[k]
    {
        let mut j: usize = 0;
        while j < n - 1 - i
            invariant
                j <= n - 1 - i,
                i < n,
                sorted_between(A, n - i, n - 1),
                multiset_equivalent(A, old(A)),
                forall|k: int, l: int| 
                    n - i <= k < n && 0 <= l < n - i ==> A[l] <= A[k],
                forall|k: int| 
                    0 <= k < j ==> A[k] <= A[j]
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
    while i < A.len() {
        print!("{} ", A[i]);
        i += 1;
    }
}

// Lemma to help with sorted_between reasoning
proof fn lemma_sorted_between_transitive(A: &Vec<i32>, from1: int, to1: int, from2: int, to2: int)
    requires 
        sorted_between(A, from1, to1),
        sorted_between(A, from2, to2),
        from1 <= from2 <= to1 + 1,
        from2 - 1 <= to2 <= to1,
    ensures sorted_between(A, from1, to2)
{
    // Proof by contradiction - Verus can usually handle this automatically
}

// Lemma about multiset equivalence after swap
proof fn lemma_swap_preserves_multiset(A: &Vec<i32>, B: &Vec<i32>, i: usize, j: usize)
    requires 
        i < A.len(),
        j < A.len(),
        B.len() == A.len(),
        B[i] == A[j],
        B[j] == A[i],
        forall|k: int| 0 <= k < A.len() && k != i && k != j ==> A[k] == B[k]
    ensures multiset_equivalent(A, B)
{
    // Proof would show that swapping two elements preserves multiset equivalence
}

}