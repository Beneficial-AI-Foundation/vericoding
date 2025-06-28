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
        forall|x: i32| count_occurrences(*a, x) == count_occurrences(*old(a), x),
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
            forall|x: i32| count_occurrences(*a, x) == count_occurrences(*old(a), x),
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
                forall|x: i32| count_occurrences(*a, x) == count_occurrences(old_a_inner, x),
                // The last i elements remain sorted and in position
                sorted(a, n - i, n),
                // Maintain the property that sorted region has largest elements
                forall|k1: int, k2: int| 0 <= k1 < (n - i) && (n - i) <= k2 < n ==> a[k1 as usize] <= a[k2 as usize],
                // Bubbling progress: largest element in [0..j+1] will reach correct position
                j == 0 || forall|k: int| 0 <= k <= j ==> a[k as usize] <= a[j as usize],
        {
            if a[j] > a[j + 1] {
                // Swap elements
                let ghost old_a_swap = *a;
                let temp = a[j];
                a.set(j, a[j + 1]);
                a.set(j + 1, temp);
                
                // The swap preserves the multiset property
                proof {
                    lemma_swap_preserves_multiset(old_a_swap, *a, j, j + 1);
                }
            }
            j += 1;
        }
        
        // After inner loop, the largest element in [0..n-1-i] is at position n-1-i
        proof {
            if n - i < n {
                assert(sorted(a, n - i, n));
                assert(forall|k: int| 0 <= k < (n - i) ==> a[k as usize] <= a[(n - 1 - i) as usize]);
            }
        }
        
        i += 1;
    }
}

// Helper function to count occurrences of an element in a vector
spec fn count_occurrences(a: Vec<i32>, x: i32) -> nat {
    count_occurrences_range(a, x, 0, a.len())
}

spec fn count_occurrences_range(a: Vec<i32>, x: i32, from: usize, to: usize) -> nat
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
proof fn lemma_swap_preserves_multiset(old_a: Vec<i32>, new_a: Vec<i32>, i: usize, j: usize)
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
    // We prove this by showing that for any element x, the count is preserved
    assert forall|x: i32| count_occurrences(new_a, x) == count_occurrences(old_a, x) by {
        // Split the count into three parts: before min(i,j), between i and j, after max(i,j)
        let min_idx = if i < j { i } else { j };
        let max_idx = if i < j { j } else { i };
        
        // Count before min_idx is unchanged
        assert(count_occurrences_range(new_a, x, 0, min_idx) == 
               count_occurrences_range(old_a, x, 0, min_idx));
        
        // Count between min_idx+1 and max_idx is unchanged
        assert(count_occurrences_range(new_a, x, min_idx + 1, max_idx) == 
               count_occurrences_range(old_a, x, min_idx + 1, max_idx));
        
        // Count after max_idx is unchanged
        assert(count_occurrences_range(new_a, x, max_idx + 1, old_a.len()) == 
               count_occurrences_range(old_a, x, max_idx + 1, old_a.len()));
        
        // At positions i and j, the elements are swapped
        let old_count_at_i = if old_a[i] == x { 1nat } else { 0nat };
        let old_count_at_j = if old_a[j] == x { 1nat } else { 0nat };
        let new_count_at_i = if new_a[i] == x { 1nat } else { 0nat };
        let new_count_at_j = if new_a[j] == x { 1nat } else { 0nat };
        
        // Since new_a[i] == old_a[j] and new_a[j] == old_a[i]
        assert(new_count_at_i == old_count_at_j);
        assert(new_count_at_j == old_count_at_i);
        
        // Therefore total count is preserved
        lemma_count_decomposition(old_a, x, i, j);
        lemma_count_decomposition(new_a, x, i, j);
    }
}

// Helper lemma to decompose count into parts
proof fn lemma_count_decomposition(a: Vec<i32>, x: i32, i: usize, j: usize)
    requires 
        i < a.len(),
        j < a.len(),
        i != j,
    ensures
        count_occurrences(a, x) == 
            count_occurrences_range(a, x, 0, if i < j { i } else { j }) +
            (if a[if i < j { i } else { j }] == x { 1nat } else { 0nat }) +
            count_occurrences_range(a, x, (if i < j { i } else { j }) + 1, if i < j { j } else { i }) +
            (if a[if i < j { j } else { i }] == x { 1nat } else { 0nat }) +
            count_occurrences_range(a, x, (if i < j { j } else { i }) + 1, a.len()),
{
    // This follows from the definition of count_occurrences_range
    lemma_count_split(a, x, 0, a.len());
}

// Basic lemma for splitting count ranges
proof fn lemma_count_split(a: Vec<i32>, x: i32, from: usize, to: usize)
    requires 
        from <= to,
        to <= a.len(),
    ensures
        count_occurrences_range(a, x, from, to) == 
            if from == to { 0nat }
            else { 
                (if a[from] == x { 1nat } else { 0nat }) + 
                count_occurrences_range(a, x, from + 1, to) 
            },
{
    // This follows directly from the definition of count_occurrences_range
}

} // verus!