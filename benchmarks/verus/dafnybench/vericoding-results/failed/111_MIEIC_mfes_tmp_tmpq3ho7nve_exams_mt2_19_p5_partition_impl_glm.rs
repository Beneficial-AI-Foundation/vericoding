use vstd::prelude::*;

verus! {

type T = int; // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.

// <vc-helpers>
spec fn is_partitioned<T: vstd::prelude::SpecOrd>(a: Seq<T>, pivotPos: nat) -> bool {
    forall|i: int| 0 <= i < pivotPos ==> a[i] < a[pivotPos as int] &&
    forall|i: int| pivotPos < i < a.len() ==> a[i] >= a[pivotPos as int]
}

proof fn partition_lemma<T: vstd::prelude::SpecOrd>()
    ensures
        forall|array: Seq<T>, pivotPos: nat|
            #![trigger is_partitioned(array, pivotPos)]
            pivotPos < array.len() ==> is_partitioned(array, pivotPos) ==> array.len() > 0
{
}

spec fn multiset_preserved<T>(a: Seq<T>, old_a: Seq<T>) -> bool {
    a.to_multiset() == old_a.to_multiset()
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
    let pivot = a[0];
    let mut i = 1;
    let mut j = 1;
    
    proof {
        partition_lemma::<T>();
    }

    while j < n
        invariant 
            1 <= i <= j <= n,
            forall|k: int| 1 <= k < i ==> a[k] < pivot,
            forall|k: int| i <= k < j ==> a[k] >= pivot,
            a@.to_multiset() == old(a)@.to_multiset(),
            a[0] == pivot,
    {
        if a[j] < pivot {
            a.swap(i, j);
            i = i + 1;
        }
        j = j + 1;
    }
    
    a.swap(0, i - 1);
    let pivotPos = i - 1;
    
    proof {
        assert forall|k: int| 0 <= k < pivotPos implies a[k] < a[pivotPos as int] by {
            if k == 0 {
                assert(a[k] == old(a)@[i - 1]);
                assert(old(a)@[i - 1] == pivot);
                assert(a[pivotPos as int] == pivot);
            } else {
                assert(1 <= k < i);
                assert(a[k] < pivot);
                assert(a[pivotPos as int] == pivot);
            }
        };
        
        assert forall|k: int| pivotPos < k < n implies a[k] >= a[pivotPos as int] by {
            assert(pivotPos == i - 1);
            assert(i <= k < j);
            assert(j == n);
            assert(a[k] >= pivot);
            assert(a[pivotPos as int] == pivot);
        };
    }
    
    pivotPos
}
// </vc-code>

fn main() {}

}