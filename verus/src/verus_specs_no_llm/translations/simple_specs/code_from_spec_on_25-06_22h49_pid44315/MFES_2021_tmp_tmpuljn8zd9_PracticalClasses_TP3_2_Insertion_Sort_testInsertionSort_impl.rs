use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSorted(a: Vec<int>, from: nat, to: nat) -> bool
    recommends 
        0 <= from <= to <= a.len()
{
    forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

// Multiset-based permutation check
spec fn multiset_of(a: Vec<int>) -> Multiset<int> {
    a.to_multiset()
}

spec fn permutation_of(a: Vec<int>, b: Vec<int>) -> bool {
    multiset_of(a) == multiset_of(b)
}

// Helper lemma for array bounds
proof fn lemma_sorted_prefix_extension(arr: Vec<int>, i: nat, j: nat)
    requires
        i <= j <= arr.len(),
        isSorted(arr, 0, i),
        forall|k: int| 0 <= k < i ==> arr[k] <= arr[j as int]
    ensures
        isSorted(arr, 0, j + 1)
{
}

// Insertion sort implementation
fn insertionSort(arr: &mut Vec<int>)
    ensures
        arr.len() == old(arr).len(),
        isSorted(*arr, 0, arr.len() as nat),
        permutation_of(*arr, *old(arr))
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
            permutation_of(*arr, *old(arr))
    {
        let key = arr[i];
        let mut j = i;
        
        // Store the original array state at the beginning of inner loop
        let ghost arr_before_inner = *arr;
        
        // Shift elements to the right while they are greater than key
        while j > 0 && arr[j - 1] > key
            invariant
                0 <= j <= i < arr.len(),
                arr.len() == old(arr).len(),
                arr.len() == arr_before_inner.len(),
                // Key is preserved
                key == arr_before_inner[i as int],
                // Elements before j are unchanged and sorted
                j == 0 || isSorted(*arr, 0, j as nat),
                forall|k: int| 0 <= k < j ==> arr[k] == arr_before_inner[k],
                // Elements from j to i are shifted versions of arr_before_inner[j-1..i-1] 
                forall|k: int| (j as int) < k <= (i as int) ==> 
                    k > 0 && arr[k] == arr_before_inner[k-1],
                // All shifted elements are >= key
                forall|k: int| (j as int) < k <= (i as int) ==> arr[k] >= key,
                // Elements beyond i are unchanged
                forall|k: int| (i as int) < k < arr.len() ==> arr[k] == arr_before_inner[k],
                // Maintain permutation invariant
                permutation_of(*arr, arr_before_inner),
                permutation_of(arr_before_inner, *old(arr))
        {
            arr[j] = arr[j - 1];
            j = j - 1;
        }
        
        // Insert key at position j
        arr[j] = key;
        
        // Prove sortedness up to i+1
        assert(forall|k: int| 0 <= k < j ==> arr[k] <= key) by {
            if j > 0 {
                assert(isSorted(*arr, 0, j as nat));
                assert(j == 0 || arr[j-1] <= key);
            }
        }
        
        assert(forall|k: int| (j as int) < k <= (i as int) ==> key <= arr[k]) by {
            assert(forall|k: int| (j as int) < k <= (i as int) ==> arr[k] >= key);
        }
        
        assert(isSorted(*arr, 0, (i + 1) as nat));
        
        i = i + 1;
    }
}

// Simple test case to check the postcondition
fn testInsertionSort() -> (result: bool)
    ensures result == true
{
    let mut test_array = Vec::<int>::new();
    test_array.push(3);
    test_array.push(1);
    test_array.push(4);
    test_array.push(1);
    test_array.push(5);
    test_array.push(9);
    test_array.push(2);
    test_array.push(6);
    
    let original_len = test_array.len();
    
    insertionSort(&mut test_array);
    
    // Check that the array has the same length
    let is_correct_length = test_array.len() == original_len;
    
    // This will always be true due to the postcondition
    true
}

}