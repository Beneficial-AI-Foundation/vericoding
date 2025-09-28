// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_min_index(a: &Vec<i32>, start: usize) -> (min_index: usize)
    requires
        start < a.len(),
    ensures
        start <= min_index < a.len(),
        forall|j: int| (start as int) <= j < (a.len() as int) ==> a[min_index as int] <= a[j as int],
{
    let mut min_index = start;
    let mut i = start + 1;
    while i < a.len()
        invariant
            start < i <= a.len(),
            start <= min_index < i,
            forall|j: int| (start as int) <= j < (i as int) ==> a[min_index as int] <= a[j as int],
        decreases a.len() - i
    {
        if a[i] < a[min_index] {
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
    /* code modified by LLM (iteration 3): Changed `Vec::swap` to `a.swap` to fix a compilation error. */
    let ghost initial_a = a@;
    let len = a.len();
    if len > 0 {
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                a.len() == len,
                forall|x: int, y: int| 0 <= x < y < (i as int) ==> a[x] <= a[y],
                forall|x: int, y: int| 0 <= x < (i as int) && (i as int) <= y < (len as int) ==> a[x] <= a[y],
                a@.to_multiset() == initial_a.to_multiset(),
            decreases len - i
        {
            let min_idx = find_min_index(a, i);
            a.swap(i, min_idx);
            i = i + 1;
        }
    }
}
// </vc-code>

}
fn main() {}