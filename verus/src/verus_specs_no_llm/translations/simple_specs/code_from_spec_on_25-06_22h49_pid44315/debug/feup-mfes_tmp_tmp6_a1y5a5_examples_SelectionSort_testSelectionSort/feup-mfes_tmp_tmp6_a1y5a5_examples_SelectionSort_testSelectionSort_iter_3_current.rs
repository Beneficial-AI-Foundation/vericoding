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
            
            // Swap elements
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
            
            // Proof that the sorted portion is still sorted
            assert(isSorted(a, 0, (i + 1) as nat)) by {
                assert(forall|k: int| i <= k < n ==> a[k as int] >= a[min_idx as int]);
                assert(a[i as int] == old(a)[min_idx as int]);
            };
            
            // Proof that elements before i+1 are <= elements after i
            assert(forall|x: int, y: int| 0 <= x < (i + 1) && (i + 1) <= y < n ==> a[x as int] <= a[y as int]) by {
                assert(forall|k: int| i <= k < n ==> old(a)[k as int] >= old(a)[min_idx as int]);
                assert(forall|x: int| 0 <= x < i ==> a[x as int] <= a[i as int]);
            };
        } else {
            // When i + 1 >= n, we're at the last element, so sorting is complete
            assert(isSorted(a, 0, (i + 1) as nat)) by {
                assert(i + 1 == n);
                assert(isSorted(a, 0, i as nat));
            };
        }
        i = i + 1;
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
            forall|j: int, k: int| 0 <= j < k <= i ==> a[j as int] <= a[k as int]
        decreases a.len() - i
    {
        if a[i] > a[i + 1] {
            return false;
        }
        i = i + 1;
    }
    
    // Prove that the local sortedness implies global sortedness
    assert(isSorted(a, 0, a.len() as nat)) by {
        assert(forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j as int] <= a[k as int]) by {
            // This follows from the transitivity of <= and the fact that consecutive elements are ordered
        };
    };
    
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