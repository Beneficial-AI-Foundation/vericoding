use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::slice;

fn find_min_index(a: &Vec<i32>, start: usize) -> (min_index: usize)
    requires
        0 <= start < a.len(),
    ensures
        start <= min_index < a.len(),
        forall|i: int| start as int <= i < a.len() as int ==> a@[min_index as int] <= a@[i],
{
    let mut min_index = start;
    let mut i = start + 1;
    while i < a.len()
        invariant
            start <= min_index < a.len(),
            start <= i <= a.len(),
            forall|k: int| start as int <= k < i as int ==> a@[min_index as int] <= a@[k],
    {
        if a[min_index] > a[i] {
            min_index = i;
        }
        i = i + 1;
    }
    min_index
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i = 0 as usize;
    while i < n
        invariant
            n == old(a).len(),
            forall|k: int, l: int| 0 <= k < l < (i as int) ==> a@[k] <= a@[l],
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| (i as int) <= k < (n as int) ==> exists|m: int| (i as int) <= m < (n as int) && a@[m] == old(a)@[k],
            forall|k: int| 0 <= k < (i as int) ==> exists|m: int| 0 <= m < (i as int) && a@[k] == old(a)@[m],
    {
        let min_index = find_min_index(a, i);
        a.swap(i, min_index);
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}