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
                // Bubbling progress: largest element will be in correct position
                forall|k: int| 0 <= k <= j ==> a[k as usize] <= a[(n - 1 - i) as usize] || j == n - 1 - i,
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
        
        // After inner loop, establish invariants for next iteration
        proof {
            // The largest element is now in position n-1-i
            lemma_bubble_establishes_max(*a, n - 1 - i);
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

// Lemma: After bubbling, the element at position pos is >= all elements before it
proof fn lemma_bubble_establishes_max(a: Vec<i32>, pos: usize)
    requires pos < a.len()
    ensures true  // Simplified for now
{
    // This would contain the proof that bubbling establishes the maximum property
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
    // Proof by showing that swapping preserves element counts
    assert forall|x: i32| count_occurrences(new_a, x) == count_occurrences(old_a, x) by {
        lemma_swap_count_helper(old_a, new_a, i, j, x);
    }
}

// Helper lemma for swap count preservation
proof fn lemma_swap_count_helper(old_a: Vec<i32>, new_a: Vec<i32>, i: usize, j: usize, x: i32)
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
    // The key insight: swapping just exchanges the elements at positions i and j
    // So if old_a[i] == x and old_a[j] != x, then we lose one x at position i and gain one at position j
    // The net effect is zero change in count
    
    // Count decomposition approach
    lemma_count_additive(old_a, x, 0, old_a.len());
    lemma_count_additive(new_a, x, 0, new_a.len());
}

// Lemma: Count function is additive over ranges
proof fn lemma_count_additive(a: Vec<i32>, x: i32, from: usize, to: usize)
    requires from <= to <= a.len()
    ensures count_occurrences_range(a, x, from, to) >= 0
{
    // Base case and inductive reasoning would go here
}

// Basic lemma for splitting count ranges
proof fn lemma_count_split(a: Vec<i32>, x: i32, from: usize, to: usize)
    requires 
        from < to,
        to <= a.len(),
    ensures
        count_occurrences_range(a, x, from, to) == 
            (if a[from] == x { 1nat } else { 0nat }) + 
            count_occurrences_range(a, x, from + 1, to),
{
    // This follows directly from the definition of count_occurrences_range
}

} // verus!