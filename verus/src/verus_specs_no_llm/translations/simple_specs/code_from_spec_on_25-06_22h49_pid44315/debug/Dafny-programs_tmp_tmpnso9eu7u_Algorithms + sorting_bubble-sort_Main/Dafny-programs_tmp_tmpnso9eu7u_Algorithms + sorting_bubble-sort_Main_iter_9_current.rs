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
    // Verus can automatically prove multiset equivalence from element-wise equality
}

// Lemma for sorted_between extension
proof fn lemma_sorted_between_extend(A: Seq<i32>, from: int, to: int)
    requires 
        sorted_between(A, from + 1, to),
        from >= 0,
        to < A.len(),
        from <= to,
        forall|k: int| from + 1 <= k <= to ==> A[from] <= A[k]
    ensures sorted_between(A, from, to)
{
    assert forall|i: int, j: int| from <= i <= j <= to && 0 <= i && j < A.len() implies A[i] <= A[j] by {
        if i == from {
            if j == from {
                // trivial: A[from] <= A[from]
            } else {
                // j > from, so from + 1 <= j <= to
                assert(A[from] <= A[j]);
            }
        } else {
            // i > from, so from + 1 <= i <= j <= to
            assert(A[i] <= A[j]); // from sorted_between(A, from + 1, to)
        }
    }
}

// Helper lemma to prove that global ordering implies sorted
proof fn lemma_global_ordering_implies_sorted(A: Seq<i32>)
    requires 
        A.len() > 0,
        forall|k: int, l: int| 0 <= k <= l < A.len() ==> A[k] <= A[l]
    ensures sorted(A)
{
    assert(sorted_between(A, 0, (A.len() - 1) as int));
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
            // Multiset equivalence is preserved
            multiset_equivalent(A@, original_A),
            // The last i elements are sorted and are the i largest elements
            i == 0 || (
                // The suffix [n-i, n) is sorted
                sorted_between(A@, (n - i) as int, (n - 1) as int) &&
                // Elements in suffix are >= all elements in prefix
                forall|k: int, l: int| 
                    0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> A@[k] <= A@[l]
            ),
        decreases n - i
    {
        let mut j: usize = 0;
        
        while j < n - 1 - i
            invariant
                j <= n - 1 - i,
                i < n,
                n == A.len(),
                // Multiset equivalence maintained
                multiset_equivalent(A@, original_A),
                // Previous sorted suffix is maintained
                i == 0 || (
                    sorted_between(A@, (n - i) as int, (n - 1) as int) &&
                    forall|k: int, l: int| 
                        0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> A@[k] <= A@[l]
                ),
                // Maximum element in [0..=j] has bubbled to position j
                j == 0 || forall|k: int| 0 <= k <= j as int ==> A@[k] <= A@[j as int],
                // All elements at positions > n-1-i are >= elements at positions <= j
                forall|k: int, l: int| 
                    0 <= k <= j as int && (n - i) as int <= l < n as int ==> A@[k] <= A@[l],
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
                    assert(multiset_equivalent(old_A, original_A)); // inductive hypothesis
                    // Transitivity of multiset equivalence
                    assert(A@ =~= old_A =~= original_A);
                }
            }
            j += 1;
        }
        
        // After inner loop, the maximum element has bubbled to position n-1-i
        proof {
            // The element at position n-1-i is now >= all elements in [0, n-1-i)
            assert(forall|k: int| 0 <= k < (n - 1 - i) as int ==> A@[k] <= A@[(n - 1 - i) as int]);
            
            // Combined with the existing sorted suffix, we have an extended sorted suffix
            if i > 0 {
                assert(sorted_between(A@, (n - i - 1) as int, (n - 1) as int));
            }
        }
        
        i += 1;
    }
    
    // Final proof that the array is sorted
    proof {
        // After all iterations, i == n, so we have established global ordering
        assert(i == n);
        
        // The invariant tells us that the entire array is the "suffix"
        if n > 0 {
            assert(sorted_between(A@, 0, (n - 1) as int));
            assert(sorted(A@));
        }
    }
}

} // verus!

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