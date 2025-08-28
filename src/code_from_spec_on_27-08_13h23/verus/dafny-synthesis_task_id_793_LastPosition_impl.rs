use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_binary_search_midpoint(low: int, high: int)
    requires
        low <= high,
    ensures
        low <= (low + high) / 2 <= high,
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn last_position(arr: &Vec<i32>, elem: i32) -> (pos: i32)
    requires 
        arr.len() > 0,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        pos == -1 || (0 <= pos < arr.len() && arr[pos as int] == elem && 
            (pos >= arr.len() - 1 || arr[(pos + 1) as int] > elem)),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn last_position(arr: &Vec<i32>, elem: i32) -> (pos: i32)
    requires 
        arr.len() > 0,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        pos == -1 || (0 <= pos < arr.len() && arr[pos as int] == elem && 
            (pos >= arr.len() - 1 || arr[(pos + 1) as int] > elem)),
{
    let mut low: i32 = 0;
    let mut high: i32 = (arr.len() as i32) - 1;
    let mut result: i32 = -1;

    while low <= high
        invariant
            0 <= low <= arr.len() as i32,
            0 <= high < arr.len() as i32 || high == arr.len() as i32 - 1,
            low <= high + 1,
            result == -1 || (0 <= result < arr.len() as i32 && arr[result as int] == elem),
            forall|i: int| 0 <= i < low ==> arr[i] < elem,
            forall|i: int| high < i < arr.len() as i32 ==> arr[i] > elem,
        decreases
            high - low,
    {
        let mid = (low + high) / 2;
        proof {
            lemma_binary_search_midpoint(low as int, high as int);
        }
        if arr[mid as int] == elem {
            result = mid;
            low = mid + 1;
        } else if arr[mid as int] < elem {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }

    result
}
// </vc-code>

fn main() {}

}