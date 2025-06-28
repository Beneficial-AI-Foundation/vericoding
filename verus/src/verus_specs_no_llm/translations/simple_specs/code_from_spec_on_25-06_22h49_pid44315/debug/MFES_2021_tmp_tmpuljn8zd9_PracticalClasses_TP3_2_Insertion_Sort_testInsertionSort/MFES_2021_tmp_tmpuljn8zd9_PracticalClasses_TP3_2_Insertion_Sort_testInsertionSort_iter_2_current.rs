use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSorted(a: Vec<int>, from: nat, to: nat) -> bool
    recommends 
        0 <= from <= to <= a.len()
{
    forall|i: int, j: int| from <= i < j < to ==> a[i as int] <= a[j as int]
}

// Helper spec function to check multiset equality
spec fn multiset_eq(a: Vec<int>, b: Vec<int>) -> bool {
    forall|x: int| a.count(x) == b.count(x)
}

// Helper function to insert an element at the correct position
fn insert(arr: &mut Vec<int>, key: int, pos: usize)
    requires 
        pos < old(arr).len(),
        isSorted(*old(arr), 0, pos as nat),
        old(arr)[pos as int] == key
    ensures
        arr.len() == old(arr).len(),
        isSorted(*arr, 0, (pos + 1) as nat),
        multiset_eq(*arr, *old(arr))
{
    let mut i = pos;
    
    while i > 0 && arr[i - 1] > key
        invariant
            i <= pos,
            arr.len() == old(arr).len(),
            key == old(arr)[pos as int],
            // Elements before i are unchanged from original
            forall|k: int| 0 <= k < i ==> arr[k] == old(arr)[k],
            // Elements after pos are unchanged
            forall|k: int| pos < k < arr.len() ==> arr[k] == old(arr)[k],
            // Elements from i+1 to pos are shifted versions of original elements from i to pos-1
            forall|k: int| i < k <= pos ==> arr[k] == old(arr)[k - 1],
            // Sortedness properties
            isSorted(*arr, 0, i as nat),
            forall|k: int| i < k < pos ==> arr[k] <= arr[k + 1],
            // Key positioning
            forall|k: int| 0 <= k < i ==> arr[k] <= key,
            i == 0 || arr[i - 1] <= key
    {
        arr.set(i, arr[i - 1]);
        i = i - 1;
    }
    
    arr.set(i, key);
    
    // Proof that multiset equality holds
    assert(multiset_eq(*arr, *old(arr)));
}

// Insertion sort implementation
fn insertionSort(arr: &mut Vec<int>)
    ensures
        arr.len() == old(arr).len(),
        isSorted(*arr, 0, arr.len() as nat),
        multiset_eq(*arr, *old(arr))
{
    if arr.len() <= 1 {
        return;
    }
    
    let mut i = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            arr.len() == old(arr).len(),
            isSorted(*arr, 0, i as nat),
            multiset_eq(*arr, *old(arr))
    {
        let key = arr[i];
        
        // Establish precondition for insert
        assert(arr[i as int] == key);
        
        insert(arr, key, i);
        i = i + 1;
    }
}

// Simple test case to check the postcondition
fn testInsertionSort() -> (result: bool)
    ensures result == true
{
    let mut test_array = vec![3, 1, 4, 1, 5, 9, 2, 6];
    let original_array = test_array;
    let original_len = test_array.len();
    
    insertionSort(&mut test_array);
    
    // Check that the array is sorted and has the same length
    let is_correct_length = test_array.len() == original_len;
    
    // We can call isSorted as a spec function in executable code for testing
    if is_correct_length {
        // The postcondition of insertionSort guarantees these properties
        assert(isSorted(test_array, 0, test_array.len() as nat));
        assert(multiset_eq(test_array, original_array));
        true
    } else {
        // This branch is unreachable due to insertionSort's postcondition
        false
    }
}

}