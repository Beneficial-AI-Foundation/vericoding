// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_helper(a: &Vec<i32>, key: i32, low: int, high: int) -> (result: int)
    requires
        0 <= low <= high <= a.len(),
        forall|i: int| low <= i < high ==> a[i] != key,
    ensures
        result == -1 || (result >= 0 && result < a.len()),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
{
    if low == high {
        -1
    } else {
        let mid = (low + high) / 2;
        if a[mid as usize] == key {
            mid
        } else {
            if a[mid as usize] < key {
                find_helper(a, key, mid + 1, high)
            } else {
                find_helper(a, key, low, mid)
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    ensures
        (result == -1 || (result >= 0 && result < a.len())),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
// </vc-spec>
// <vc-code>
{
    find_helper(a, key, 0, a.len() as int)
}
// </vc-code>

}
fn main() {}