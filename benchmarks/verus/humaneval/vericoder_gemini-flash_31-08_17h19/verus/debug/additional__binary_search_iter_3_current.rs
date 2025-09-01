use vstd::prelude::*;

verus! {

// <vc-helpers>
fn binary_search_recursive_helper(arr: &[i32], target: i32, low: int, high: int) -> (result: Option<usize>)
    requires
        low >= 0,
        high >= -1, // high can be -1 initially (low - 1)
        high < arr.len(),
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
    // The previous error was here due to a syntax error.
    // The previous syntax error was due to `arr.len()` in `assert(mid as int >= 0 && mid as int < arr.len());`
    //  `arr.len()` is a `usize`, but it was being treated as an `int` within the `assert` statement.
    // The fix involves casting `arr.len()` to `int` for consistency.
    assert(mid >= low && mid <= high); // mid is within the search range
    assert(mid as int >= 0 && mid as int < arr.len() as int); // mid is a valid array index

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

    let mut low: int = 0;
    let mut high: int = arr.len() as int - 1;

    while low <= high
        invariant
            low >= 0,
            high < arr.len() as int, // high can be arr.len() - 1, which implies high < arr.len()
            low <= high + 1, // `high` can become `low - 1`
            forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
            forall|i: int| 0 <= i && i < low ==> arr[i] != target, // target cannot be in [0, low-1]
            forall|i: int| high < i && i < arr.len() ==> arr[i] != target, // target cannot be in [high+1, arr.len()-1]
    {
        let mid: int = low + (high - low) / 2;
        proof {
            assert(mid >= low && mid <= high);
            assert(mid as int >= 0 && mid as int < arr.len() as int);
        }

        if arr[mid as int] == target {
            return Some(mid as usize);
        } else if arr[mid as int] < target {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    None
    // impl-end
}
// </vc-code>

fn main() {}
}