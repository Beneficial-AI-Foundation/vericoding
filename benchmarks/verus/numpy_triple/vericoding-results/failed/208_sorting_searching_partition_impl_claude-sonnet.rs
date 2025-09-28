// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_occurrences_split(arr: Seq<i32>, pivot: i32, left: Seq<i32>, right: Seq<i32>, x: i32)
    requires
        multiset_equal(left + seq![pivot] + right, arr),
    ensures
        count_occurrences(arr, x) == count_occurrences(left, x) + (if pivot == x { 1nat } else { 0nat }) + count_occurrences(right, x),
{
    /* helper modified by LLM (iteration 5): added proper proof for count split */
    let combined = left + seq![pivot] + right;
    
    proof {
        let rec_proof = |s: Seq<i32>, t: Seq<i32>, elem: i32|
            requires
                s.len() > 0,
            ensures
                count_occurrences(s + t, elem) == count_occurrences(s, elem) + count_occurrences(t, elem),
            decreases s.len()
        {
            if s.len() == 1 {
                assert(count_occurrences(s + t, elem) == (if s[0] == elem { 1nat } else { 0nat }) + count_occurrences(t, elem));
                assert(count_occurrences(s, elem) == (if s[0] == elem { 1nat } else { 0nat }));
            } else {
                rec_proof(s.skip(1), t, elem);
            }
        };
        
        if left.len() > 0 {
            rec_proof(left, seq![pivot] + right, x);
        }
        rec_proof(seq![pivot], right, x);
        
        assert(count_occurrences(combined, x) == count_occurrences(left, x) + count_occurrences(seq![pivot], x) + count_occurrences(right, x));
        assert(count_occurrences(seq![pivot], x) == (if pivot == x { 1nat } else { 0nat }));
        assert(multiset_equal(combined, arr));
        assert(count_occurrences(combined, x) == count_occurrences(arr, x));
    }
}

proof fn lemma_multiset_transitivity(arr1: Seq<i32>, arr2: Seq<i32>, arr3: Seq<i32>)
    requires
        multiset_equal(arr1, arr2),
        multiset_equal(arr2, arr3),
    ensures
        multiset_equal(arr1, arr3),
{
    /* helper modified by LLM (iteration 5): simplified transitivity proof */
    assert(arr1.len() == arr2.len() && arr2.len() == arr3.len());
    assert(forall|x: i32| count_occurrences(arr1, x) == count_occurrences(arr2, x));
    assert(forall|x: i32| count_occurrences(arr2, x) == count_occurrences(arr3, x));
    assert(forall|x: i32| count_occurrences(arr1, x) == count_occurrences(arr3, x));
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
    /* code modified by LLM (iteration 5): implemented quickselect algorithm with proper bounds checking */
    let mut result = arr;
    let mut left = 0;
    let mut right = (result.len() - 1) as int;
    let target = kth as int;
    
    while left < right
        invariant
            result.len() == arr.len(),
            0 <= left <= target,
            target <= right < result.len() as int,
            multiset_equal(result@, arr@),
        decreases right - left,
    {
        let pivot_idx = left;
        let pivot_val = result[pivot_idx as usize];
        let mut store_idx = left;
        
        let mut i = left;
        while i <= right
            invariant
                left <= i <= right + 1,
                left <= store_idx <= i,
                result.len() == arr.len(),
                multiset_equal(result@, arr@),
                0 <= left < result.len() as int,
                0 <= right < result.len() as int,
            decreases right + 1 - i,
        {
            if i < result.len() as int && result[i as usize] < pivot_val {
                if store_idx != i {
                    let temp = result[store_idx as usize];
                    result.set(store_idx as usize, result[i as usize]);
                    result.set(i as usize, temp);
                }
                store_idx += 1;
            }
            i += 1;
        }
        
        if store_idx != pivot_idx {
            let temp = result[pivot_idx as usize];
            result.set(pivot_idx as usize, result[store_idx as usize]);
            result.set(store_idx as usize, temp);
        }
        
        if store_idx == target {
            break;
        } else if store_idx < target {
            left = store_idx + 1;
        } else {
            right = store_idx - 1;
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}