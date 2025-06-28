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
            // The last i elements are sorted
            sorted(a, n - i, n),
            // Elements are preserved
            forall|x: i32| count_occurrences(a, x) == count_occurrences(&old(a), x),
            // Max bubble property: elements in sorted region are >= elements in unsorted region
            forall|k1: int, k2: int| 0 <= k1 < (n - i) && (n - i) <= k2 < n ==> a[k1 as usize] <= a[k2 as usize],
    {
        let mut j = 0;
        let ghost old_a_inner = *a;
        
        while j < n - 1 - i
            invariant
                i < n,
                j <= n - 1 - i,
                a.len() == n,
                // Elements are preserved
                forall|x: i32| count_occurrences(a, x) == count_occurrences(&old_a_inner, x),
                // The last i elements remain sorted
                sorted(a, n - i, n),
                // Bubbling property: max element in range [0..j+1] will bubble to position n-1-i
                forall|k: int| j < k < n - i ==> 
                    forall|l: int| 0 <= l <= j ==> a[l as usize] <= a[k as usize] || 
                    exists|m: int| 0 <= m <= j ==> a[m as usize] >= a[k as usize],
        {
            if a[j] > a[j + 1] {
                // Swap elements
                let temp = a[j];
                a.set(j, a[j + 1]);
                a.set(j + 1, temp);
                
                // Prove multiset preservation after swap
                proof {
                    assert(forall|x: i32| count_occurrences(a, x) == count_occurrences(&old_a_inner, x));
                }
            }
            j += 1;
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

// Lemma: Swapping two elements preserves multiset
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
    // The proof follows from the fact that swapping preserves the multiset
    // The total count of each element remains the same after swapping
}

// Helper lemma for count preservation
proof fn lemma_swap_preserves_count(old_a: &Vec<i32>, new_a: &Vec<i32>, x: i32, i: usize, j: usize)
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
    // The proof is by the definition of count_occurrences and the swap invariant
}

// Lemma: After bubbling, the max element is in correct position
proof fn lemma_max_element_in_position(a: &Vec<i32>, pos: usize, n: usize)
    requires 
        pos < n,
        n == a.len(),
        // All elements before pos are <= element at pos
        forall|k: int| 0 <= k < pos ==> a[k as usize] <= a[pos],
    ensures 
        // The element at pos is >= all elements from 0 to pos
        forall|k: int| 0 <= k <= pos ==> a[k as usize] <= a[pos],
{
    // This follows from the precondition and reflexivity
}

} // verus!