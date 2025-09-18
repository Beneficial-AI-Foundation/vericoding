// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): derive arr[i] <= arr[j] from global nondecreasing property */
proof fn nondec_implies_le(arr: &Vec<i32>, i: int, j: int)
    requires
        0 <= i && i < j && j < arr.len() as int,
        forall|a: int, b: int| 0 <= a && a < b && b < arr.len() as int ==> arr[a as usize] <= arr[b as usize],
    ensures
        arr[i as usize] <= arr[j as usize],
{
    // instantiate the given monotonicity property for the specific indices i and j
    assert(arr[i as usize] <= arr[j as usize]);
}

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
    /* code modified by LLM (iteration 5): linear scan tracking last occurrence using usize indices and i32 result */
    let n: usize = arr.len();
    let mut i: usize = 0;
    let mut last: i32 = -1;
    while i < n
        invariant
            -1 <= last as int && last as int < n as int,
            last >= 0 ==> arr[last as usize] == elem,
            forall|k: int| 0 <= k && k < i as int ==> (arr[k as usize] == elem ==> last as int >= k),
        decreases n - i
    {
        if arr[i] == elem {
            last = i as i32;
        }
        i = i + 1;
    }
    last
}
// </vc-code>

}
fn main() {}