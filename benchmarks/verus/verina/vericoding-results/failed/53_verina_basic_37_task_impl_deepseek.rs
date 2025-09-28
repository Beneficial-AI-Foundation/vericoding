// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sorted_array_contains_impl(arr: Seq<i32>, target: i32, low: int, high: int) -> (result: bool)
    requires
        low >= 0,
        high < arr.len(),
        low <= high,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        result == exists|i: int| low <= i <= high && arr[i] == target,
    decreases high - low,
{
    if low == high {
        arr[low] == target
    } else {
        let mid = low + (high - low) / 2;
        proof {
            assert(mid >= low);
            assert(mid <= high);
        }
        if arr[mid] == target {
            true
        } else if arr[mid] < target {
            lemma_sorted_array_contains_impl(arr, target, mid + 1, high)
        } else {
            lemma_sorted_array_contains_impl(arr, target, low, mid - 1)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        (result >= 0 ==> {
            &&& 0 <= result < arr.len()
            &&& arr[result as int] == target
            &&& forall|i: int| 0 <= i < result ==> arr[i] != target
        }) &&
        (result == -1 ==> {
            &&& forall|i: int| 0 <= i < arr.len() ==> arr[i] != target
        }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed array bounds checking and invariant satisfaction */
    let len = arr.len();
    if len == 0 {
        return -1;
    }
    let mut low: usize = 0;
    let mut high: usize = len - 1;
    while low <= high
        invariant
            0 <= low <= high < len,
            forall|i: int| 0 <= i < len ==> arr[i] != target ==> !(low as int <= i <= high as int),
            exists|i: int| 0 <= i < len && arr[i] == target <==> exists|i: int| low as int <= i <= high as int && arr[i] == target,
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        if arr[mid] == target {
            proof {
                let arr_seq = arr@;
                assert(forall|i: int, j: int| 0 <= i < j < arr_seq.len() ==> arr_seq[i] <= arr_seq[j]);
                assert(forall|i: int| 0 <= i < mid as int ==> arr_seq[i] <= arr_seq[mid as int]);
                assert(forall|i: int| 0 <= i < mid as int ==> arr_seq[i] != target);
            }
            return mid as i32;
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    -1
}
// </vc-code>

}
fn main() {}