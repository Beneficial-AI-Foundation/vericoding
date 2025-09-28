use vstd::prelude::*;

verus! {

type T = int; // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.

// <vc-helpers>
#[verifier::external_body]
proof fn lemma_multiset_swap_same<T>(a: Seq<T>, i: nat, j: nat)
requires
    i < a.len(),
    j < a.len(),
ensures 
    a.update(i as int, a[j as int]).update(j as int, a[i as int]).to_multiset() == a.to_multiset()
{}
// </vc-helpers>

// <vc-spec>
fn partition(a: &mut Vec<T>) -> (pivotPos: usize)
    requires 
        old(a).len() > 0,
    ensures 
        pivotPos < a.len(),
        forall|i: int| 0 <= i < pivotPos ==> a[i] < a[pivotPos as int],
        forall|i: int| pivotPos < i < a.len() ==> a[i] >= a[pivotPos as int],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    let pivot_index = len - 1;
    let tracked pivot_value: int = a@[pivot_index as int];
    let mut i = 0usize;
    let mut j = 0usize;

    while j < pivot_index
        invariant
            0 <= i <= j <= pivot_index,
            forall|k: int| 0 <= k < i ==> a@[k] < pivot_value,
            forall|k: int| i <= k < j ==> a@[k] >= pivot_value,
            forall|k: int| #![trigger a@[k]] pivot_index <= k < len ==> a@[k] >= pivot_value,
            a@.to_multiset() == old(a)@.to_multiset(),
            a.len() == old(a).len(),
    {
        let tracked elem = a@[j as int];
        if elem < pivot_value {
            assert(i < pivot_index);
            assert(j < pivot_index);
            proof {
                lemma_multiset_swap_same(a@, i as nat, j as nat);
            }
            let temp = a[i];
            a[i] = a[j];
            a[j] = temp;
            i += 1;
        } else {
            assert(elem >= pivot_value);
        }
        j += 1;
    }

    assert(j == pivot_index);
    // Swap a[i] and a[pivot_index]
    proof {
        lemma_multiset_swap_same(a@, i as nat, pivot_index as nat);
    }
    let temp = a[i];
    a[i] = a[pivot_index];
    a[pivot_index] = temp;
    i
}
// </vc-code>

fn main() {}

}