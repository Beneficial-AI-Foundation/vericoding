// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_less_than_transitive(a: int, b: int, c: int)
    requires
        a <= b,
        b <= c,
    ensures
        a <= c,
{
}

proof fn lemma_array_sorted_property(arr: Seq<i32>, i: int, j: int)
    requires
        0 <= i < j < arr.len(),
        forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] <= arr[l],
    ensures
        arr[i] <= arr[j],
{
}

spec fn contains(arr: Seq<i32>, target: i32, start: int, end: int) -> bool {
    exists|i: int| start <= i < end && arr[i] == target
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
/* code modified by LLM (iteration 2): fix nat/int usage and add proof for first occurrence */
{
    let mut low: nat = 0;
    let mut high: nat = arr.len() as nat - 1;
    let mut result: i32 = -1;
    let arr_seq = arr@;

    while low <= high
        invariant
            0 <= low <= high + 1,
            high < arr.len(),
            result == -1 ==> !contains(arr_seq, target, 0, arr.len()),
            result >= 0 ==> {
                &&& 0 <= result < arr.len() as int
                &&& arr[result as usize] == target
                &&& forall|i: int| 0 <= i < result ==> arr[i as usize] != target
            },
        decreases high - low,
    {
        let mid: nat = (low + high) / 2;
        let mid_val = arr[mid as usize];

        if mid_val == target {
            proof {
                assert(contains(arr_seq, target, low, high + 1));
                let mut i: nat = 0;
                while i < mid
                    invariant
                        0 <= i <= mid,
                        forall|j: int| 0 <= j < i ==> arr[j as usize] != target,
                    decreases mid - i,
                {
                    if arr[i as usize] == target {
                        assert(false);
                    }
                    i += 1;
                }
            }
            result = mid as i32;
            break;
        } else if mid_val < target {
            proof {
                if mid + 1 <= high {
                    lemma_array_sorted_property(arr_seq, mid, high);
                }
            }
            low = mid + 1;
        } else {
            proof {
                if low <= mid - 1 {
                    lemma_array_sorted_property(arr_seq, low, mid - 1);
                }
            }
            high = mid - 1;
        }
    }

    result
}
// </vc-code>

}
fn main() {}