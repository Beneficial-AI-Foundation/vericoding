use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] <= a[k]
}

// <vc-helpers>
proof fn extend_sorted_interval(a: &[int], low: int, mid: int, value: int)
    requires
        sorted(a),
        0 <= low <= mid < a.len(),
        a[mid] < value,
    ensures
        forall|k: int| low <= k <= mid ==> a[k] <= a[mid],
{
    assert(forall|k: int| low <= k <= mid implies a[k] <= a[mid] by {
        if k < mid {
            assert(a[k] <= a[mid]);
        } else {
            assert(k == mid);
            assert(a[k] == a[mid]);
        }
    });
}

proof fn extend_sorted_interval_gt(a: &[int], mid: int, high: int, value: int)
    requires
        sorted(a),
        0 <= mid < high <= a.len(),
        a[mid] > value,
    ensures
        forall|k: int| mid <= k < high implies a[k] >= a[mid],
{
    assert(forall|k: int| mid <= k < high implies a[k] >= a[mid] by {
        if mid < k {
            assert(a[mid] <= a[k]);
        } else {
            assert
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], value: int) -> (index: i32)
    requires 
        sorted(a),
    ensures 
        0 <= index ==> index < a.len() && a[index as int] == value,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != value,
// </vc-spec>
// <vc-code>
proof fn extend_sorted_interval(a: &[int], low: int, mid: int, value: int)
    requires
        sorted(a),
        0 <= low <= mid < a.len(),
        a[mid] < value,
    ensures
        forall|k: int| low <= k <= mid ==> a[k] <= a[mid],
{
    assert(forall|k: int| low <= k <= mid implies a[k] <= a[mid] by {
        if k < mid {
            assert(a[k] <= a[mid]);
        } else {
            assert(k == mid);
            assert(a[k] == a[mid]);
        }
    });
}

proof fn extend_sorted_interval_gt(a: &[int], mid: int, high: int, value: int)
    requires
        sorted(a),
        0 <= mid < high <= a.len(),
        a[mid] > value,
    ensures
        forall|k: int| mid <= k < high implies a[k] >= a[mid],
{
    assert(forall|k: int| mid <= k < high implies a[k] >= a[mid] by {
        if mid < k {
            assert(a[mid] <= a[k]);
        } else {
            assert
// </vc-code>

fn main() {
}

}