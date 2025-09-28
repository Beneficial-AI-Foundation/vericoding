// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): rewrite helper to avoid &mut Vec parameter issues */
fn partition_helper(arr: &mut Vec<i32>, low: usize, high: usize, kth: usize) -> (result: usize)
    requires
        low <= kth,
        kth < high,
        high <= arr@.len(),
    ensures
        result == kth,
        forall|i: int| (low as int) <= i < (result as int) ==> arr@[i] <= arr@[result as int],
        forall|i: int| (result as int) < i < (high as int) ==> arr@[i] >= arr@[result as int],
        multiset_equal(arr@, old(arr)@),
    decreases high - low
{
    let pivot_index = high - 1;
    let pivot = arr[pivot_index];
    let mut i = low;
    let mut j = low;
    
    while j < pivot_index
        invariant
            low <= i <= j <= pivot_index,
            forall|idx: int| (low as int) <= idx < (i as int) ==> arr@[idx] <= pivot,
            forall|idx: int| (i as int) <= idx < (j as int) ==> arr@[idx] > pivot,
            multiset_equal(arr@, old(arr)@),
        decreases pivot_index - j
    {
        if arr[j] <= pivot {
            let temp = arr[i];
            arr.set(i, arr[j]);
            arr.set(j, temp);
            i += 1;
        }
        j += 1;
    }
    
    let temp = arr[i];
    arr.set(i, arr[pivot_index]);
    arr.set(pivot_index, temp);
    
    if i == kth {
        i
    } else if i < kth {
        partition_helper(arr, i + 1, high, kth)
    } else {
        partition_helper(arr, low, i, kth)
    }
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
/* code modified by LLM (iteration 5): use explicit element swapping instead of arr.swap */
{
    let mut result = arr.clone();
    let pivot_index = partition_helper(&mut result, 0, result.len(), kth);
    proof {
        assert(pivot_index == kth);
    }
    result
}
// </vc-code>


}
fn main() {}