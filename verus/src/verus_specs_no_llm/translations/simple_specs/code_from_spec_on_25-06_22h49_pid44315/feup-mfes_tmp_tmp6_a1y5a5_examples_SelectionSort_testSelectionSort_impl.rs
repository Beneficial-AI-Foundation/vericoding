use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSorted(a: &Vec<i32>, from: nat, to: nat) -> bool
    recommends 
        0 <= from <= to <= a.len()
{
    forall|i: int, j: int| from <= i < j < to ==> a[i as int] <= a[j as int]
}

// Finds the position of a minimum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
fn findMin(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len()
    ensures 
        from <= index < to,
        forall|k: int| from <= k < to ==> a[k as int] >= a[index as int]
{
    let mut index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= index < to,
            from < i <= to,
            forall|k: int| from <= k < i ==> a[k as int] >= a[index as int]
        decreases to - i
    {
        if a[i] < a[index] {
            index = i;
        }
        i = i + 1;
    }
    
    index
}

// Helper lemma to prove that swapping preserves sortedness properties
proof fn lemma_swap_preserves_order(a: &Vec<i32>, old_a: &Vec<i32>, i: usize, min_idx: usize, n: usize)
    requires
        0 <= i < min_idx < n <= a.len(),
        a.len() == old_a.len(),
        // After swap: a[i] = old_a[min_idx], a[min_idx] = old_a[i]
        a[i as int] == old_a[min_idx as int],
        a[min_idx as int] == old_a[i as int],
        // All other elements unchanged
        forall|k: int| 0 <= k < n && k != i && k != min_idx ==> a[k as int] == old_a[k as int],
        // min_idx was minimum in range [i, n)
        forall|k: int| i <= k < n ==> old_a[k as int] >= old_a[min_idx as int],
        // Sortedness of prefix [0, i)
        isSorted(old_a, 0, i as nat),
        // Partition property: sorted part <= unsorted part
        forall|x: int, y: int| 0 <= x < i && i <= y < n ==> old_a[x as int] <= old_a[y as int]
    ensures
        isSorted(a, 0, (i + 1) as nat),
        forall|x: int, y: int| 0 <= x <= i && (i + 1) <= y < n ==> a[x as int] <= a[y as int]
{
    // The swapped element a[i] is the minimum of the unsorted part
    assert(forall|k: int| (i + 1) <= k < n ==> a[i as int] <= a[k as int]);
    
    // Elements in [0, i) are unchanged and still sorted
    assert(isSorted(a, 0, i as nat));
    
    // The new element at position i fits with the sorted prefix
    if i > 0 {
        assert(forall|x: int| 0 <= x < i ==> a[x as int] <= a[i as int]);
    }
    
    // Therefore [0, i+1) is sorted
    assert(isSorted(a, 0, (i + 1) as nat));
    
    // Partition property is maintained
    assert(forall|x: int, y: int| 0 <= x <= i && (i + 1) <= y < n ==> a[x as int] <= a[y as int]);
}

// Sorts array 'a' using the selection sort algorithm.
fn selectionSort(a: &mut Vec<i32>)
    ensures 
        isSorted(a, 0, a.len() as nat),
        a.len() == old(a).len()
{
    let n = a.len();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            a.len() == n,
            isSorted(a, 0, i as nat),
            forall|x: int, y: int| 0 <= x < i && i <= y < n ==> a[x as int] <= a[y as int]
        decreases n - i
    {
        if i + 1 <= n {
            let ghost old_a = *a;
            let min_idx = findMin(a, i, n);
            
            if min_idx != i {
                // Store values before swap
                let old_a_i = a[i];
                let old_a_min = a[min_idx];
                
                // Swap elements
                a.set(i, old_a_min);
                a.set(min_idx, old_a_i);
                
                // Apply lemma to prove invariants are maintained
                proof {
                    lemma_swap_preserves_order(a, &old_a, i, min_idx, n);
                }
            } else {
                // No swap needed, but we still need to prove invariants
                proof {
                    assert(forall|k: int| i <= k < n ==> a[k as int] >= a[i as int]);
                    assert(isSorted(a, 0, (i + 1) as nat));
                    assert(forall|x: int, y: int| 0 <= x <= i && (i + 1) <= y < n ==> a[x as int] <= a[y as int]);
                }
            }
        }
        i = i + 1;
    }
}

// Helper lemma for transitivity of sortedness
proof fn lemma_adjacent_implies_sorted(a: &Vec<i32>)
    requires
        forall|k: int| 0 <= k < (a.len() - 1) ==> a[k as int] <= a[(k + 1) as int]
    ensures
        forall|x: int, y: int| 0 <= x < y < a.len() ==> a[x as int] <= a[y as int]
{
    // Proof by strong induction on the distance between indices
    assert forall|x: int, y: int| 0 <= x < y < a.len() implies a[x as int] <= a[y as int] by {
        if y == x + 1 {
            // Base case: adjacent elements
            assert(a[x as int] <= a[y as int]);
        } else {
            // Inductive case: use transitivity
            assert(a[x as int] <= a[(y-1) as int] <= a[y as int]);
        }
    }
}

// Helper function to check if array is sorted (executable version)
fn checkSorted(a: &Vec<i32>) -> (result: bool)
    ensures result == isSorted(a, 0, a.len() as nat)
{
    if a.len() <= 1 {
        return true;
    }
    
    let mut i = 0;
    while i + 1 < a.len()
        invariant
            0 <= i < a.len(),
            a.len() > 1,
            forall|k: int| 0 <= k < i + 1 && k + 1 < a.len() ==> a[k as int] <= a[(k + 1) as int]
        decreases a.len() - i
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i = i + 1;
    }
    
    // Prove that checking adjacent pairs is sufficient for full sortedness
    proof {
        assert(forall|k: int| 0 <= k < (a.len() - 1) ==> a[k as int] <= a[(k + 1) as int]);
        lemma_adjacent_implies_sorted(a);
        assert(forall|x: int, y: int| 0 <= x < y < a.len() ==> a[x as int] <= a[y as int]);
    }
    
    true
}

// Test function
fn testSelectionSort() -> (result1: usize, result2: bool, result3: bool)
{
    let mut test_array: Vec<i32> = Vec::new();
    test_array.push(5);
    test_array.push(2);
    test_array.push(8);
    test_array.push(1);
    test_array.push(9);
    
    let original_len = test_array.len();
    
    // Test findMin
    let min_index = findMin(&test_array, 0, test_array.len());
    
    // Test selectionSort
    selectionSort(&mut test_array);
    
    // Helper function to check if sorted (executable version)
    let is_sorted = checkSorted(&test_array);
    let length_preserved = test_array.len() == original_len;
    
    (min_index, is_sorted, length_preserved)
}

}