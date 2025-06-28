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
        if i + 1 < n {
            let min_idx = findMin(a, i, n);
            
            // Store values before swap for proof
            let old_a_i = a[i];
            let old_a_min = a[min_idx];
            
            // Swap elements
            a.set(i, old_a_min);
            a.set(min_idx, old_a_i);
            
            // Proof that the minimum element is now at position i
            assert(forall|k: int| i <= k < n ==> a[i as int] <= a[k as int]) by {
                // The element we moved to position i was the minimum in the range [i, n)
                assert(forall|k: int| i <= k < n ==> old_a_min <= a[k as int]);
                assert(a[i as int] == old_a_min);
            }
            
            // Proof that sorting invariant is maintained
            assert(isSorted(a, 0, (i + 1) as nat)) by {
                // Previous part [0, i) was already sorted and unchanged (except possibly min_idx)
                assert(isSorted(old(a), 0, i as nat));
                // New element at position i is <= all elements in [i+1, n)
                assert(forall|x: int| 0 <= x < i ==> a[x as int] <= a[i as int]);
                // Elements in [0, i) maintain their relative order
                assert(forall|x: int, y: int| 0 <= x < y < i && x != min_idx && y != min_idx ==> a[x as int] <= a[y as int]);
            }
        } else {
            // When i + 1 >= n, we have i == n - 1, so we're at the last element
            // The array is already sorted up to position i, and there's only one element left
            assert(i == n - 1);
            assert(isSorted(a, 0, (i + 1) as nat)) by {
                assert(isSorted(a, 0, i as nat));
                assert((i + 1) as nat == n as nat);
            }
        }
        i = i + 1;
    }
    
    // Final assertion that the entire array is sorted
    assert(i == n);
    assert(isSorted(a, 0, n as nat));
}

// Helper function to check if array is sorted (executable version)
fn checkSorted(a: &Vec<i32>) -> (result: bool)
    ensures result == isSorted(a, 0, a.len() as nat)
{
    if a.len() <= 1 {
        assert(isSorted(a, 0, a.len() as nat)) by {
            // For arrays of length 0 or 1, the sorted condition is trivially true
            assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> true);
        }
        return true;
    }
    
    let mut i = 0;
    while i + 1 < a.len()
        invariant
            0 <= i < a.len(),
            forall|x: int, y: int| 0 <= x < y < x + 1 && x + 1 <= i + 1 ==> a[x] <= a[y],
            isSorted(a, 0, (i + 1) as nat)
        decreases a.len() - i
    {
        if a[i] > a[i + 1] {
            // Prove that if we find a violation, the array is not sorted
            assert(!isSorted(a, 0, a.len() as nat)) by {
                assert(0 <= i < i + 1 < a.len());
                assert(a[i as int] > a[(i + 1) as int]);
                // This contradicts the definition of isSorted
            }
            return false;
        }
        
        // Prove the invariant is maintained
        assert(isSorted(a, 0, (i + 2) as nat)) by {
            assert(isSorted(a, 0, (i + 1) as nat));
            assert(a[i] <= a[i + 1]);
            // All pairs (x,y) with 0 <= x < y < i+2 satisfy a[x] <= a[y]
        }
        
        i = i + 1;
    }
    
    // At this point, i + 1 >= a.len(), so i >= a.len() - 1
    // We've checked all adjacent pairs, so the array is sorted
    assert(i + 1 >= a.len());
    assert(isSorted(a, 0, a.len() as nat)) by {
        assert(isSorted(a, 0, (i + 1) as nat));
        assert((i + 1) as nat >= a.len() as nat);
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