use vstd::prelude::*;

verus! {

type T = int; // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.

// <vc-helpers>
spec fn less_than_pivot(s: Seq<T>, pivot: T, low: int, high: int) -> bool
    recommends low <= high
{
    forall|i: int| low <= i < high ==> s[i] < pivot
}

spec fn geq_than_pivot(s: Seq<T>, pivot: T, low: int, high: int) -> bool
    recommends low <= high
{
    forall|i: int| low <= i < high ==> s[i] >= pivot
}

proof fn swap_preserves_multiset<T>(v: &mut Vec<T>, i: usize, j: usize)
    requires
        0 <= i < old(v).len(),
        0 <= j < old(v).len(),
    ensures
        v@.to_multiset() == old(v)@.to_multiset(),
{
    v.lemma_swap_preserves_multiset(i as int, j as int);
}

proof fn update_preserves_multiset<T>(v: &mut Vec<T>, i: usize, value: T)
    requires
        0 <= i < old(v).len(),
    ensures
        v@.to_multiset() == old(v)@.to_multiset().insert(value).remove(old(v)@[i as int]),
{
    v.lemma_update_preserves_multiset(i as int, value);
}
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
    let n = a.len();
    let pivot = a[0 as int];
    let mut i: usize = 1;
    let mut j: usize = n - 1;
    
    proof {
        assert(a@.to_multiset() == old(a)@.to_multiset());
    }
    
    while i <= j
        invariant
            0 < i <= n,
            0 <= j < n,
            j + 1 >= i,
            less_than_pivot(a@, pivot, 1, i as int),
            geq_than_pivot(a@, pivot, j as int + 1, n as int),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        if a[i as int] < pivot {
            i += 1;
        } else {
            a.swap(i, j);
            proof {
                swap_preserves_multiset(a, i, j);
            }
            j -= 1;
        }
    }
    
    a.swap(0, j);
    proof {
        swap_preserves_multiset(a, 0, j);
        assert(a@.to_multiset() == old(a)@.to_multiset());
        
        assert forall|k: int| 0 <= k < j as int implies a@[k] < a@[j as int] by {
            if k == 0 {
                assert(a@[0] == old(a)@[j as int]);
                assert(a@[j as int] == pivot);
                assert(old(a)@[j as int] >= pivot);
                assert(a@[0] >= pivot);
                assert(a@[j as int] == pivot);
                assert(a@[0] >= a@[j as int]);
            } else {
                assert(less_than_pivot(a@, pivot, 1, i as int));
                assert(a@[k] < pivot);
                assert(a@[j as int] == pivot);
                assert(a@[k] < a@[j as int]);
            }
        };
        
        assert forall|k: int| j as int < k < n as int implies a@[k] >= a@[j as int] by {
            assert(geq_than_pivot(a@, pivot, j as int + 1, n as int));
            assert(a@[k] >= pivot);
            assert(a@[j as int] == pivot);
            assert(a@[k] >= a@[j as int]);
        };
    }
    
    j
}
// </vc-code>

fn main() {}

}