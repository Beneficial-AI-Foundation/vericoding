use vstd::prelude::*;

verus! {

// <vc-helpers>
fn distinct_elements_proof(a: &[i32], l: usize, r: usize, val: i32)
    requires
        0 <= l <= r <= a.len(),
        forall|i: int, j: int| 0 <= i < j < a.len() as int ==> a[i] <= a[j],
        l < r ==> a[l as int] == val,
        l < r ==> a[(r-1) as int] >= val
    ensures
        l < r ==> exists|k: int| l <= k < r && a[k as int] == val
{
    // This helper proof is essentially proving a property that if both ends of a sorted array
    // fulfill certain conditions, then an element equal to 'val' must exist within the range.
    // However, for binary search, typically we are looking for the insertion point.
    // The `ensures` clause of the main function is more about partitioning the array
    // based on `key`, rather than finding an exact match.
    // Thus, this helper might not be strictly necessary for the given specification
    // which focuses on the partition property.
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[i32], key: i32) -> (n: usize)
    requires 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
    ensures 
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> a[i] < key,
        n == a.len() ==> forall|i: int| 0 <= i < a.len() ==> a[i] < key,
        forall|i: int| n <= i < a.len() ==> a[i] >= key
// </vc-spec>
// <vc-code>
{
    let mut low: usize = 0;
    let mut high: usize = a.len();

    while low < high
        invariant
            0 <= low as int <= high as int <= a.len() as int,
            forall|i: int| 0 <= i < low as int ==> a[i] < key,
            forall|i: int| high as int <= i < a.len() as int ==> a[i] >= key,
            forall|i: int, j: int| 0 <= i < j < a.len() as int ==> a[i] <= a[j],
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        // This if condition is good to check for `mid` reaching `a.len()` which can happen when
        // `low` is `a.len() - 1` and `high` is `a.len()`
        // In that specific case, `mid` would be `a.len() - 1`, and `mid + 1` could be `a.len()`
        // However, the out of bounds array access happens when `a[mid]` is used, not `mid+1`.
        // The only scenario where `a[mid]` can cause issues is when `low == high`, then `mid` also becomes `low` (which would be out of bounds if `low == a.len()`).
        // But the loop condition `low < high` guarantees `mid < high`.
        // If `high` is `a.len()`, `mid` is at most `a.len() - 1`.
        if a[mid] < key {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}
// </vc-code>

fn main() {}

}