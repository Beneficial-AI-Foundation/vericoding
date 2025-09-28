// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn count_occurrences(arr: Seq<i32>, x: i32) -> nat 
    decreases arr.len()
{
    if arr.len() == 0 {
        0nat
    } else {
        let first_count: nat = if arr[0] == x { 1nat } else { 0nat };
        first_count + count_occurrences(arr.skip(1), x)
    }
}

spec fn multiset_equal(arr1: Seq<i32>, arr2: Seq<i32>) -> bool {
    arr1.len() == arr2.len() &&
    forall|x: i32| count_occurrences(arr1, x) == count_occurrences(arr2, x)
}

fn partition(arr: Vec<i32>, kth: usize) -> (result: Vec<i32>)
    requires kth < arr.len(),
    ensures
        result.len() == arr.len(),
        /* All elements before kth are <= the kth element */
        forall|i: int| 0 <= i < kth as int ==> result@[i] <= result@[kth as int],
        /* All elements after kth are >= the kth element */
        forall|i: int| (kth as int) < i < (result@.len()) ==> result@[i] >= result@[kth as int],
        /* The k-th element is in its correct sorted position relative to the original array */
        exists|sorted: Seq<i32>| 
            is_sorted(sorted) &&
            multiset_equal(sorted, arr@) &&
            result@[kth as int] == sorted[kth as int],
        /* The result contains the same elements as the original (multiset equality) */
        multiset_equal(result@, arr@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced swap method calls with explicit swap to avoid complex arguments issue */
{
    let mut arr = arr;
    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1;
    let k: usize = kth;

    while low < high
        decreases (high - low) as int,
    {
        let pivot_index = high;
        let pivot = arr[pivot_index];
        let mut i = low;
        
        for j in low..high {
            if arr[j] <= pivot {
                // Explicit swap instead of arr.swap(i, j)
                let temp = arr[i];
                arr[i] = arr[j];
                arr[j] = temp;
                i += 1;
            }
        }
        
        // Explicit swap instead of arr.swap(i, high)
        let temp = arr[i];
        arr[i] = arr[high];
        arr[high] = temp;
        
        if i == k {
            break;
        } else if k < i {
            high = i - 1;
        } else {
            low = i + 1;
        }
    }

    arr
}
// </vc-code>


}
fn main() {}