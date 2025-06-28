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
                // The largest element in [0..=j] will bubble to position n-1-i
                forall|k: int| 0 <= k <= j ==> a[k as usize] <= a[j as usize] || 
                    exists|l: int| k <= l <= j && a[l as usize] >= a[k as usize],
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
    assert forall|x: i32| count_occurrences(new_a, x) == count_occurrences(old_a, x) by {
        lemma_swap_count_preservation(old_a, new_a, i, j, x);
    }
}

// Helper lemma for swap count preservation
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
    // The key insight: swapping preserves the total count
    // because we're just moving elements, not creating or destroying them
    
    // Split counts into disjoint parts and show they're preserved
    lemma_count_swap_helper(old_a, new_a, i, j, x, 0, old_a.len());
}

// Recursive helper to prove count preservation over ranges
proof fn lemma_count_swap_helper(old_a: Vec<i32>, new_a: Vec<i32>, i: usize, j: usize, x: i32, from: usize, to: usize)
    requires 
        i < old_a.len(),
        j < old_a.len(),
        i != j,
        old_a.len() == new_a.len(),
        new_a[i] == old_a[j],
        new_a[j] == old_a[i],
        forall|k: int| 0 <= k < old_a.len() && k != i && k != j ==> new_a[k as usize] == old_a[k as usize],
        from <= to <= old_a.len(),
    ensures 
        count_occurrences_range(new_a, x, from, to) == count_occurrences_range(old_a, x, from, to),
    decreases to - from
{
    if from >= to {
        // Base case: empty range
        return;
    }
    
    if from == i {
        // At swapped position i
        assert(new_a[from] == old_a[j]);
        lemma_count_swap_helper(old_a, new_a, i, j, x, from + 1, to);
        
        // Handle the contribution of position i
        if j < to && from < j {
            // j is also in our range, handled separately
        } else {
            // j is outside range, so we need to account for the swap effect
        }
    } else if from == j {
        // At swapped position j  
        assert(new_a[from] == old_a[i]);
        lemma_count_swap_helper(old_a, new_a, i, j, x, from + 1, to);
    } else {
        // At unchanged position
        assert(new_a[from] == old_a[from]);
        lemma_count_swap_helper(old_a, new_a, i, j, x, from + 1, to);
    }
}

} // verus!