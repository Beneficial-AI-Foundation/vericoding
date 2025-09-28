// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `old(a)` access within `swap` function ensures block for `&mut` parameters. */
fn swap(a: &mut Vec<i32>, i: usize, j: usize)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        a[i as int] == old(a).old_vec()[j as int],
        a[j as int] == old(a).old_vec()[i as int],
        forall|k: int| 0 <= k < a.len() && k != i as int && k != j as int ==> a[k as int] == old(a).old_vec()[k as int],
{
    let temp = a[i];
    a.set(i, a[j]);
    a.set(j, temp);
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        a@.to_multiset() == result@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Add missing clone for `old(a)` access inside the invariant to fix the compilation error. */
{
    let mut arr = a.clone();
    let n = arr.len();

    if n == 0 {
        return arr;
    }

    assert(n >= 0);

    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            arr.len() == n,
            forall|k: int, l: int| (n as int) - (i as int) <= k < l < (n as int) ==> arr[k as int] <= arr[l as int],
            a@.to_multiset() == arr@.to_multiset(),
    {
        let mut j = 0;
        while j < n - 1 - i
            invariant
                0 <= i < n,
                0 <= j <= n - 1 - i,
                arr.len() == n,
                forall|k: int, l: int| (n as int) - (i as int) <= k < l < (n as int) ==> arr[k as int] <= arr[l as int],
                a@.to_multiset() == arr@.to_multiset(),
                forall|k: int| (n as int) - 1 - (i as int) <= k < (n as int) ==> arr[k as int] >= arr[j as int],
                // This ensures that the elements at the end of the array are sorted
                // and greater than or equal to the current element being considered.
        {
            if arr[j] > arr[j+1] {
                swap(&mut arr, j, j+1);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    arr
}
// </vc-code>

}
fn main() {}