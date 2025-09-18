// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn last_position(arr: &Vec<i32>, elem: i32) -> (result: i32)
    requires forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        (result >= 0 ==> 
            0 <= result < arr.len() &&
            arr[result as int] == elem &&
            forall|k: int| result < k < arr.len() ==> arr[k] != elem) &&
        (result == -1 ==> forall|k: int| 0 <= k < arr.len() ==> arr[k] != elem),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected mismatched types from usize to int for array indexing */
    let mut low: usize = 0;
    let mut high: usize = if arr.len() == 0 { 0 } else { arr.len() - 1 };
    let mut ans: isize = -1;

    while low <= high && high < arr.len()
        invariant
            0 <= low,
            high < arr.len(),
            (ans == -1 || (0 <= ans && (ans as usize) < arr.len() && arr[ans as usize] == elem)),
            // Corrected type for arr[i] from usize to int
            forall|i: int| 0 <= i < low as int ==> arr[i] != elem || (ans != -1 && i <= ans),
            // Corrected type for arr[i] from usize to int
            forall|i: int| (high as int) < i < arr.len() as int ==> arr[i] != elem || (ans != -1 && i <= ans),
            // Corrected type for arr[k] from usize to int
            forall|k: int|
                0 <= k && (k as usize) < arr.len() && arr[k] == elem && (ans == -1 || k > ans)
                ==>
                (low as int) <= k && k <= (high as int),
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if arr[mid] == elem {
            ans = mid as isize;
            low = mid + 1;
            assert(low <= arr.len() as usize);
        } else if arr[mid] < elem {
            low = mid + 1;
            assert(low <= arr.len() as usize);
        } else {
            assert(mid > 0 ==> mid - 1 < arr.len());
            if mid == 0 { high = 0; } else { high = mid - 1; }
        }
    }
    ans as i32
}
// </vc-code>

}
fn main() {}