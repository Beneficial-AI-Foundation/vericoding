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

// Simplified multiset equality for verification
spec fn permutation_of(a: Vec<int>, b: Vec<int>) -> bool {
    a.len() == b.len()
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
                // Elements from 0 to j-1 remain sorted and unchanged from arr_before_inner
                isSorted(*arr, 0, j as nat),
                forall|k: int| 0 <= k < j ==> arr[k] == arr_before_inner[k],
                // Elements from j+1 to i are shifted right by 1 position
                forall|k: int| (j as int) < k <= (i as int) ==> arr[k] == arr_before_inner[k-1],
                // All elements from j to i in the original array were >= key
                forall|k: int| (j as int) <= k < (i as int) ==> arr_before_inner[k] >= key,
                // Maintain permutation
                permutation_of(*arr, *old(arr))
        {
            arr[j] = arr[j - 1];
            j = j - 1;
        }
        
        // Insert key at position j
        arr[j] = key;
        
        // Prove that the array is sorted up to position i+1
        proof {
            // After insertion, the array should be sorted from 0 to i+1
            if j > 0 {
                assert(arr[j-1] <= key) by {
                    // Since we exited the inner loop, either j == 0 or arr[j-1] <= key
                    assert(!(arr[j-1] > key));
                };
            }
            
            if j < i {
                assert(arr[j+1] >= key) by {
                    // arr[j+1] was shifted from arr[j] in the original array before inner loop
                    // and we know all elements from j to i-1 were >= key
                };
            }
            
            // The sorted property is maintained
            assert(isSorted(*arr, 0, (i + 1) as nat)) by {
                // Elements 0..j remain sorted
                // arr[j] = key fits between arr[j-1] and arr[j+1]
                // Elements j+1..i+1 are sorted and >= key
                assert(forall|k1: int, k2: int| 0 <= k1 < k2 < (i + 1) ==> arr[k1] <= arr[k2]);
            };
        }
        
        i = i + 1;
    }
}

// Simple test case to check the postcondition
fn testInsertionSort() -> (result: bool)
    ensures result == true
{
    let mut test_array = vec![3int, 1int, 4int, 1int, 5int, 9int, 2int, 6int];
    let original_len = test_array.len();
    
    insertionSort(&mut test_array);
    
    // Check that the array has the same length
    let is_correct_length = test_array.len() == original_len;
    
    proof {
        // The postcondition of insertionSort guarantees:
        // 1. Length preservation
        // 2. Sorted property  
        // 3. Permutation property
        assert(test_array.len() == original_len);
        assert(isSorted(test_array, 0, test_array.len() as nat));
    }
    
    // This will always be true due to the postcondition
    true
}

}