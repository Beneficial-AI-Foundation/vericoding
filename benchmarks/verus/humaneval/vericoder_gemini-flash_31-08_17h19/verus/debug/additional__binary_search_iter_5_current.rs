use vstd::prelude::*;

verus! {

// <vc-helpers>
fn binary_search_recursive_helper(arr: &[i32], target: i32, low: int, high: int) -> (result: Option<usize>)
    requires
        low >= 0,
        high >= -1, // high can be -1 initially (low - 1)
        high < arr.len() as int,
        low <= high + 1, // high can be -1 initially or cross low
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    ensures
        match result {
            Some(index) => {
                low <= index && index <= high && arr[index as int] == target
            },
            None =>
                forall|i: int| low <= i && i <= high ==> arr[i] != target,
        },
{
    if low > high {
        return None;
    }

    let mid = low + (high - low) / 2;
    assert(mid >= low && mid <= high); // mid is within the search range
    assert(mid as int >= 0 && mid as int <= arr.len() as int);
    // Verus does not recognize `arr.len()` as an int, so it needs to be cast to `int`
    // to allow comparison operations. This fixes `arr.len()` to `arr.len() as int`
    assert(mid as int >= 0 && mid as int <= (arr.len() as int - 1)) by {
        if arr.len() > 0 {
            assert(mid as int < arr.len() as int);
        } else {
            // If arr.len() is 0, this assertion (mid < -1) is vacuously true.
            // But we already handle arr.len() == 0 case in main function.
        }
    }; // mid is a valid array index when arr.len() > 0


    if arr[mid as int] == target {
        Some(mid as usize)
    } else if arr[mid as int] < target {
        binary_search_recursive_helper(arr, target, mid + 1, high)
    } else {
        binary_search_recursive_helper(arr, target, low, mid - 1)
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        match result {
            Some(index) => arr[index as int] == target && arr.len() > 0 && index < arr.len(),
            None => forall|i: int| 0 <= i && i < arr.len() ==> arr[i] != target,
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    if arr.len() == 0 {
        return None;
    }

    let low: int = 0;
    let high: int = arr.len() as int - 1;

    binary_search_recursive_helper(arr, target, low, high)
    // impl-end
}
// </vc-code>

fn main() {}
}