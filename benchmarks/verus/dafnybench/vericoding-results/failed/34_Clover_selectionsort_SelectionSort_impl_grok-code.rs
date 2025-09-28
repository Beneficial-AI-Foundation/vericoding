use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let len: usize = a@.len().try_into().unwrap();
    for i: usize in 0..len
        invariant
            a@.len() as int == len as int,
            a@.to_multiset() == old(a)@.to_multiset(),
            0 <= i as int <= len as int,
            forall|j: int, k: int| 0 <= j < k < i as int ==> a@[j] <= a@[k],
            forall|p: int, q: int| 0 <= p < i as int <= q < len as int ==> a@[p] <= a@[q],
    {
        let mut min_idx: usize = i;
        for j: usize in (i + 1)..len
            invariant
                i < len,
                i <= min_idx < len,
                forall|k: int| i as int <= k < j as int + 1 ==> a@[min_idx as int] <= a@[k],
        {
            if a@[j as int] < a@[min_idx as int] {
                min_idx = j;
            }
        }
        proof {
            assert(forall|k: int| i as int <= k < len as int ==> a@[min_idx as int] <= a@[k]);
        }
        a.swap(i, min_idx);
        proof {
            assert forall |j: int, k: int| 0 <= j < k < i as int + 1 ==> a@[j] <= a@[k] by {
                if j < k && k < i as int {
                    assert(a@[j] <= a@[k]);
                } else if j < i as int && k == i as int {
                    assert(a@[j] <= a@[k]);
                } else if j == i as int && k == i as int {
                    // j < k false
                }
            }
            assert forall |p: int, q: int| 0 <= p < i as int + 1 <= q < len as int ==> a@[p] <= a@[q] by {
                if p < i as int {
                    assert(a@[p] <= a@[q]);
                } else if p == i as int {
                    assert(i as int < i as int + 1 <= q < len as int);
                    assert(a@[p] <= a@[q]);
                }
            }
        }
    }
}
// </vc-code>

fn main() {}

}