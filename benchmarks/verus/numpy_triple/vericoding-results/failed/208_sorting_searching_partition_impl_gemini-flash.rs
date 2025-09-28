// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [fixed multiset_equal postcondition] */
fn swap(arr: &mut Vec<i32>, i: usize, j: usize)
    requires
        0 <= i,
        i < arr.len(),
        0 <= j,
        j < arr.len(),
    ensures
        arr@.len() == old(arr)@.len(),
        arr@[i as int] == old(arr)@[j as int],
        arr@[j as int] == old(arr)@[i as int],
        forall|k: int| 0 <= k < arr@.len() && k != i as int && k != j as int ==> arr@[k] == old(arr)@[k],
        multiset_equal(arr@, old(arr)@),
{
    let temp = arr[i];
    arr[i] = arr[j];
    arr[j] = temp;
}
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
/* code modified by LLM (iteration 5): [fixed tuple in forall condition] */
{
    let mut arr = arr;
    let len = arr.len();

    if len <= 1 {
        return arr;
    }

    let mut low: usize = 0;
    let mut high: usize = len - 1;

    while low <= high
        invariant
            0 <= low,
            high < len,
            low <= (high + 1) || high == (usize::MAX),
            multiset_equal(arr@, old(arr)@),
            forall|i: int| 0 <= i < low as int ==> arr@[i] <= arr@[kth as int],
            forall|i: int| high as int + 1 <= i < len as int ==> arr@[i] >= arr@[kth as int],
    {
        if low == high {
            break; 
        }

        let pivot_index = high;
        let pivot_value = arr[pivot_index];

        let mut i = low;
        let mut j = high - 1;

        while i <= j
            invariant
                low <= i,
                j < high,
                i <= j + 1,
                multiset_equal(arr@, OLD(arr)@),
                forall|k: int| low as int <= k < i as int ==> arr@[k] <= pivot_value,
                forall|k: int| k > j as int && k < high as int ==> arr@[k] >= pivot_value,
        {
            if arr[i] <= pivot_value {
                i += 1;
            } else if arr[j] >= pivot_value {
                j -= 1;
            } else {
                swap(&mut arr, i, j);
                i += 1;
                j -= 1;
            }
        }
        
        swap(&mut arr, i, high);

        let new_pivot_index = i;

        if new_pivot_index == kth {

            proof {
                assert(forall|idx: int| low as int <= idx && idx < new_pivot_index as int ==> arr@[idx] <= arr@[kth as int]);
                assert(forall|idx: int| new_pivot_index as int < idx && idx <= high as int ==> arr@[idx] >= arr@[kth as int]);
            }

            break;

        } else if new_pivot_index < kth {
            low = new_pivot_index + 1;
        } else {
            high = new_pivot_index - 1;
        }
    }
    arr
}
// </vc-code>


}
fn main() {}