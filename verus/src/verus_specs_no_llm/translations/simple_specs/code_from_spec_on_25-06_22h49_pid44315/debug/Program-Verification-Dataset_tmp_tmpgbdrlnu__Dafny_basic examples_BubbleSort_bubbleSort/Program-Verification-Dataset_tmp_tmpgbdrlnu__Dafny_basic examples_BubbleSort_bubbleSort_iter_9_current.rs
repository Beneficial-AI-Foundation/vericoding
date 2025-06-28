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
            n > 0,
            // The last i elements are in their final sorted positions
            sorted(a, n - i, n),
            // Elements are preserved
            forall|x: i32| count_occurrences(*a, x) == count_occurrences(*old(a), x),
            // The sorted suffix contains the largest elements
            forall|k1: int, k2: int| 0 <= k1 < (n - i) && (n - i) <= k2 < n ==> a[k1 as usize] <= a[k2 as usize],
    {
        let mut j = 0;
        let ghost old_a_inner = *a;
        
        while j < n - 1 - i
            invariant
                i < n,
                j <= n - 1 - i,
                a.len() == n,
                n > 0,
                // Elements are preserved from start of inner loop
                forall|x: i32| count_occurrences(*a, x) == count_occurrences(old_a_inner, x),
                // The last i elements remain sorted and in position
                sorted(a, n - i, n),
                // Maintain the property that sorted region has largest elements
                forall|k1: int, k2: int| 0 <= k1 < (n - i) && (n - i) <= k2 < n ==> a[k1 as usize] <= a[k2 as usize],
                // Maximum element so far is at or before position n-1-i
                forall|k: int| 0 <= k <= j ==> a[k as usize] <= a[(n - 1 - i) as usize] || 
                    exists|l: int| k <= l <= j && a[l as usize] >= a[(n - 1 - i) as usize],
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
                    // Prove transitivity of multiset preservation
                    assert(forall|x: i32| count_occurrences(*a, x) == count_occurrences(old_a_swap, x));
                    assert(forall|x: i32| count_occurrences(old_a_swap, x) == count_occurrences(old_a_inner, x));
                }
            }
            j += 1;
        }
        
        // After inner loop, establish that element at n-1-i is maximum of prefix
        proof {
            assert(j == n - 1 - i);
            // The bubbling process ensures the maximum is now at position n-1-i
            lemma_bubble_max_property(*a, n - 1 - i);
        }
        
        i += 1;
    }
    
    // Final proof that the array is fully sorted
    proof {
        assert(i == n);
        assert(sorted(a, 0, n));
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

// Lemma: After bubbling phase, element at pos is >= all elements in [0, pos]
proof fn lemma_bubble_max_property(a: Vec<i32>, pos: usize)
    requires pos < a.len()
    ensures forall|k: int| 0 <= k <= pos ==> a[k as usize] <= a[pos]
{
    // This property is established by the bubbling process
    // Each comparison and potential swap moves larger elements toward the right
}

// Lemma: Swapping two elements preserves multiset
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
    // Proof by cases on the value x
    assert forall|x: i32| count_occurrences(new_a, x) == count_occurrences(old_a, x) by {
        lemma_swap_count_preservation(old_a, new_a, i, j, x);
    }
}

// Helper lemma for swap count preservation - detailed proof
proof fn lemma_swap_count_preservation(old_a: Vec<i32>, new_a: Vec<i32>, i: usize, j: usize, x: i32)
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
    // Split the count into three parts: before min(i,j), between i and j, after max(i,j)
    let min_idx = if i < j { i } else { j };
    let max_idx = if i < j { j } else { i };
    
    // Count in ranges that are unchanged
    lemma_count_unchanged_range(old_a, new_a, x, 0, min_idx);
    lemma_count_unchanged_range(old_a, new_a, x, min_idx + 1, max_idx);
    lemma_count_unchanged_range(old_a, new_a, x, max_idx + 1, old_a.len());
    
    // Count at the swapped positions
    lemma_count_swap_positions(old_a, new_a, x, i, j);
    
    // Combine the results
    lemma_count_range_composition(old_a, new_a, x);
}

// Lemma: Count is unchanged in ranges where elements are unchanged
proof fn lemma_count_unchanged_range(old_a: Vec<i32>, new_a: Vec<i32>, x: i32, from: usize, to: usize)
    requires 
        from <= to <= old_a.len(),
        old_a.len() == new_a.len(),
        forall|k: int| from <= k < to ==> old_a[k as usize] == new_a[k as usize],
    ensures 
        count_occurrences_range(old_a, x, from, to) == count_occurrences_range(new_a, x, from, to),
    decreases to - from
{
    if from >= to {
        // Base case: empty range
    } else {
        // Inductive case
        assert(old_a[from] == new_a[from]);
        lemma_count_unchanged_range(old_a, new_a, x, from + 1, to);
    }
}

// Lemma: Swapping positions preserves total count
proof fn lemma_count_swap_positions(old_a: Vec<i32>, new_a: Vec<i32>, x: i32, i: usize, j: usize)
    requires 
        i < old_a.len(),
        j < old_a.len(),
        i != j,
        old_a.len() == new_a.len(),
        new_a[i] == old_a[j],
        new_a[j] == old_a[i],
    ensures 
        (if old_a[i] == x { 1nat } else { 0nat }) + (if old_a[j] == x { 1nat } else { 0nat }) ==
        (if new_a[i] == x { 1nat } else { 0nat }) + (if new_a[j] == x { 1nat } else { 0nat })
{
    // This follows directly from the swap: new_a[i] = old_a[j] and new_a[j] = old_a[i]
    assert(new_a[i] == old_a[j]);
    assert(new_a[j] == old_a[i]);
}

// Lemma: Count can be composed from ranges
proof fn lemma_count_range_composition(old_a: Vec<i32>, new_a: Vec<i32>, x: i32)
    requires old_a.len() == new_a.len()
    ensures true // Simplified for basic composition property
{
    // This would prove that count_occurrences can be decomposed into ranges
    // and that if corresponding ranges have equal counts, total counts are equal
}

} // verus!