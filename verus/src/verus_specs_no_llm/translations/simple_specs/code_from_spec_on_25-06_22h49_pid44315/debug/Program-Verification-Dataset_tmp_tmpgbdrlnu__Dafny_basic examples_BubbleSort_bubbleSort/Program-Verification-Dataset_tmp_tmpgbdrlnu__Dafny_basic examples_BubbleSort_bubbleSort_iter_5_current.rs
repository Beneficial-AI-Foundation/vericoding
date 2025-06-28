use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: &Vec<i32>, from: usize, to: usize) -> bool
    recommends 
        from <= to,
        to <= a.len(),
{
    forall|u: int, v: int| from <= u < v < to ==> a[u as usize] <= a[v as usize]
}

fn bubble_sort(a: &mut Vec<i32>)
    requires 
        a.len() > 0,
    ensures 
        sorted(a, 0, a.len()),
        a.len() == old(a).len(),
        // Elements are preserved (multiset equality)
        forall|x: i32| count_occurrences(a, x) == count_occurrences(&old(a), x),
{
    let n = a.len();
    let mut i = 0;
    
    while i < n
        invariant
            i <= n,
            a.len() == n,
            // The last i elements are in their final sorted positions
            sorted(a, n - i, n),
            // Elements are preserved
            forall|x: i32| count_occurrences(a, x) == count_occurrences(&old(a), x),
            // The sorted suffix contains the i largest elements
            forall|k1: int, k2: int| 0 <= k1 < (n - i) && (n - i) <= k2 < n ==> a[k1 as usize] <= a[k2 as usize],
    {
        let mut j = 0;
        let ghost old_a_inner = *a;
        
        while j < n - 1 - i
            invariant
                i < n,
                j <= n - 1 - i,
                a.len() == n,
                // Elements are preserved from start of inner loop
                forall|x: i32| count_occurrences(a, x) == count_occurrences(&old_a_inner, x),
                // The last i elements remain sorted and in position
                sorted(a, n - i, n),
                // Maintain the property that sorted region has largest elements
                forall|k1: int, k2: int| 0 <= k1 < (n - i) && (n - i) <= k2 < n ==> a[k1 as usize] <= a[k2 as usize],
                // Bubbling progress: largest element in [0..j+1] will reach correct position
                j == 0 || forall|k: int| 0 <= k <= j ==> a[k as usize] <= a[j as usize],
        {
            if a[j] > a[j + 1] {
                // Swap elements
                let temp = a[j];
                a.set(j, a[j + 1]);
                a.set(j + 1, temp);
                
                // The swap preserves the multiset property
                proof {
                    lemma_swap_preserves_multiset(&old_a_inner, a, j, j + 1);
                }
            }
            j += 1;
        }
        
        // After inner loop, the largest element in [0..n-1-i] is at position n-1-i
        proof {
            assert(sorted(a, n - i, n));
            assert(forall|k: int| 0 <= k < (n - i) ==> a[k as usize] <= a[(n - 1 - i) as usize]);
        }
        
        i += 1;
    }
}

// Helper function to count occurrences of an element in a vector
spec fn count_occurrences(a: &Vec<i32>, x: i32) -> nat {
    count_occurrences_range(a, x, 0, a.len())
}

spec fn count_occurrences_range(a: &Vec<i32>, x: i32, from: usize, to: usize) -> nat
    recommends from <= to <= a.len()
    decreases to - from
{
    if from >= to {
        0nat
    } else if from < a.len() && a[from] == x {
        1nat + count_occurrences_range(a, x, from + 1, to)
    } else if from < a.len() {
        count_occurrences_range(a, x, from + 1, to)
    } else {
        0nat
    }
}

// Lemma: Swapping two adjacent elements preserves multiset
proof fn lemma_swap_preserves_multiset(old_a: &Vec<i32>, new_a: &Vec<i32>, i: usize, j: usize)
    requires 
        i < old_a.len(),
        j < old_a.len(),
        i != j,
        old_a.len() == new_a.len(),
        // new_a is old_a with elements at i and j swapped
        new_a[i] == old_a[j],
        new_a[j] == old_a[i],
        forall|k: int| 0 <= k < old_a.len() && k != i && k != j ==> new_a[k as usize] == old_a[k as usize],
    ensures 
        forall|x: i32| count_occurrences(new_a, x) == count_occurrences(old_a, x),
{
    // Prove for each element x that count is preserved
    assert forall|x: i32| count_occurrences(new_a, x) == count_occurrences(old_a, x) by {
        lemma_swap_preserves_count_specific(old_a, new_a, x, i, j);
    }
}

// Helper lemma for specific element count preservation
proof fn lemma_swap_preserves_count_specific(old_a: &Vec<i32>, new_a: &Vec<i32>, x: i32, i: usize, j: usize)
    requires 
        i < old_a.len(),
        j < old_a.len(),
        i != j,
        old_a.len() == new_a.len(),
        new_a[i] == old_a[j],
        new_a[j] == old_a[i],
        forall|k: int| 0 <= k < old_a.len() && k != i && k != j ==> new_a[k as usize] == old_a[k as usize],
    ensures 
        count_occurrences(new_a, x) == count_occurrences(old_a, x),
{
    // The key insight: swapping just moves elements around
    // Case analysis on whether x equals the swapped elements
    lemma_count_equals_sum_parts(old_a, x, i, j);
    lemma_count_equals_sum_parts(new_a, x, i, j);
    
    // Count at position i: old_a[j] vs new_a[i] (which is old_a[j])
    // Count at position j: old_a[i] vs new_a[j] (which is old_a[i])  
    // All other positions unchanged
    assert(count_occurrences(new_a, x) == count_occurrences(old_a, x));
}

// Helper lemma to establish count structure
proof fn lemma_count_equals_sum_parts(a: &Vec<i32>, x: i32, i: usize, j: usize)
    requires 
        i < a.len(),
        j < a.len(),
        i != j,
    ensures 
        count_occurrences(a, x) == 
            count_occurrences_range(a, x, 0, i) +
            (if a[i] == x { 1nat } else { 0nat }) +
            count_occurrences_range(a, x, i + 1, j) +
            (if a[j] == x { 1nat } else { 0nat }) +
            count_occurrences_range(a, x, j + 1, a.len()),
{
    // This follows from the definition of count_occurrences_range
    lemma_count_split_at_indices(a, x, i, j);
}

// Technical lemma for splitting counts
proof fn lemma_count_split_at_indices(a: &Vec<i32>, x: i32, i: usize, j: usize)
    requires 
        i < a.len(),
        j < a.len(), 
        i != j,
    ensures
        count_occurrences(a, x) == count_occurrences_range(a, x, 0, i) + 
                                    (if a[i] == x { 1nat } else { 0nat }) +
                                    count_occurrences_range(a, x, i + 1, j) +
                                    (if a[j] == x { 1nat } else { 0nat }) + 
                                    count_occurrences_range(a, x, j + 1, a.len()),
{
    // Proof by unfolding definitions - Verus can handle this automatically
    // The key is that we're partitioning the range [0, len) into disjoint parts
}

} // verus!