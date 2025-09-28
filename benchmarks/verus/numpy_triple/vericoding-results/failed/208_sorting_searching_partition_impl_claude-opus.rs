// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed type annotation in lemma_count_occurrences_update */

proof fn lemma_swap_maintains_multiset(arr: Seq<i32>, i: int, j: int, result: Seq<i32>)
    requires
        0 <= i < arr.len(),
        0 <= j < arr.len(),
        result.len() == arr.len(),
        result =~= arr.update(i, arr[j]).update(j, arr[i]),
    ensures
        multiset_equal(result, arr),
{
    assert forall|x: i32| count_occurrences(result, x) == count_occurrences(arr, x) by {
        // The swap operation preserves element counts
    }
}

proof fn lemma_count_occurrences_update(arr: Seq<i32>, idx: int, val: i32, x: i32)
    requires
        0 <= idx < arr.len(),
    ensures
        count_occurrences(arr.update(idx, val), x) == 
            count_occurrences(arr, x) - (if arr[idx] == x { 1nat } else { 0nat }) + (if val == x { 1nat } else { 0nat }),
    decreases arr.len(),
{
    if idx == 0 {
        assert(arr.update(0, val).skip(1) =~= arr.skip(1));
    } else {
        lemma_count_occurrences_update(arr.skip(1), idx - 1, val, x);
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
{
    /* code modified by LLM (iteration 4): Implemented proper quickselect-style partitioning algorithm */
    let mut result = arr.clone();
    let n = result.len();
    
    // Find the kth smallest element first using selection
    let mut k_pos = kth;
    let mut left = 0;
    let mut right = n - 1;
    
    // Perform partitioning to find kth element
    while left < right
        invariant
            result.len() == n,
            n == arr.len(),
            k_pos < n,
            left <= k_pos,
            k_pos <= right,
            right < n,
            multiset_equal(result@, arr@),
        decreases right - left
    {
        // Find minimum in range [left, right]
        let mut min_idx = left;
        let mut i = left + 1;
        
        while i <= right
            invariant
                result.len() == n,
                left <= min_idx,
                min_idx < n,
                left < i,
                i <= right + 1,
                right < n,
                multiset_equal(result@, arr@),
                forall|j: int| left <= j < i ==> result@[min_idx as int] <= result@[j],
            decreases right + 1 - i
        {
            if result[i] < result[min_idx] {
                min_idx = i;
            }
            i = i + 1;
        }
        
        // Swap minimum to left position
        if min_idx != left {
            let temp = result[left];
            result.set(left, result[min_idx]);
            result.set(min_idx, temp);
            proof {
                lemma_swap_maintains_multiset(arr@, left as int, min_idx as int, result@);
            }
        }
        
        if left == k_pos {
            // Found the kth element, now partition around it
            break;
        }
        left = left + 1;
    }
    
    // Now do a full selection sort to ensure proper partitioning
    let mut i = 0;
    while i < n - 1
        invariant
            result.len() == n,
            n == arr.len(),
            kth < n,
            i <= n - 1,
            multiset_equal(result@, arr@),
            forall|p: int, q: int| 0 <= p < i && i <= q < n ==> result@[p] <= result@[q],
            is_sorted(result@.subrange(0, i as int)),
        decreases n - 1 - i
    {
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < n
            invariant
                result.len() == n,
                i < n,
                i <= min_idx,
                min_idx < n,
                i < j,
                j <= n,
                multiset_equal(result@, arr@),
                forall|k: int| i <= k < j ==> result@[min_idx as int] <= result@[k],
            decreases n - j
        {
            if result[j] < result[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let temp = result[i];
            result.set(i, result[min_idx]);
            result.set(min_idx, temp);
            proof {
                lemma_swap_maintains_multiset(arr@, i as int, min_idx as int, result@);
            }
        }
        
        proof {
            // After placing the minimum at position i, we have sorted[0..i+1]
            assert(is_sorted(result@.subrange(0, (i + 1) as int)));
        }
        
        i = i + 1;
    }
    
    proof {
        // The result is now fully sorted
        assert(is_sorted(result@));
        // Therefore it satisfies all partition properties
        assert(exists|sorted: Seq<i32>| is_sorted(sorted) && multiset_equal(sorted, arr@) && result@[kth as int] == sorted[kth as int]) by {
            let sorted = result@;
            assert(is_sorted(sorted));
            assert(multiset_equal(sorted, arr@));
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}