use vstd::prelude::*;

verus! {

type T = int; // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.

// <vc-helpers>
// Providing no additional helpers; keep this section present for possible future lemmas.
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
    let n: usize = a.len();
    let pivot_idx_usize: usize = n - 1;
    let orig = a@;
    let pivot: T = orig[pivot_idx_usize as int];
    let pivot_idx: int = pivot_idx_usize as int;

    let mut i: int = 0;
    let mut j: int = 0;

    while j < pivot_idx
        invariant 0 <= i && i <= j && j <= pivot_idx;
        invariant forall |k: int| 0 <= k && k < i ==>
            #[trigger] (a@[k] < pivot);
        invariant forall |k: int| i <= k && k < j ==>
            #[trigger] (a@[k] >= pivot);
        invariant a@.to_multiset() == orig.to_multiset();
        decreases pivot_idx - j;
    {
        if a@[j] < pivot {
            a.swap(i as usize, j as usize);
            i = i + 1;
        }
        j = j + 1;
    }

    proof {
        // From loop exit condition and invariant, j == pivot_idx
        assert(j >= pivot_idx);
        assert(j <= pivot_idx);
        assert(j == pivot_idx);
    }

    a.swap(i as usize, pivot_idx_usize);

    proof {
        // pivot is now at position i
        assert(a@[i as int] == pivot);

        // All elements before i are < pivot (these positions were not changed by final swap)
        assert(forall |k: int| 0 <= k && k < i ==>
            a@[k] < pivot);
        assert(forall |k: int| 0 <= k && k < i ==>
            a@[k] < a@[i as int]);

        // All elements in [i, pivot_idx) were >= pivot before swap and remain so after swap
        assert(forall |k: int| i <= k && k < pivot_idx ==>
            a@[k] >= pivot);

        // If i < pivot_idx then the old a[i] (now at pivot_idx) was >= pivot by invariant when j == pivot_idx
        assert((i < pivot_idx) ==> (a@[pivot_idx as int] >= pivot));

        // Combine to conclude all elements after i are >= a[i] (which is pivot)
        assert(forall |k: int| i < k && k < n as int ==>
            a@[k] >= a@[i as int]);

        // Multiset preserved
        assert(a@.to_multiset() == orig.to_multiset());
    }

    i as usize
}
// </vc-code>

fn main() {}

}