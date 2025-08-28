use vstd::prelude::*;

verus! {

type T = int; // example

 // Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.

// <vc-helpers>
spec fn swap_preserves_multiset<T>(v1: Seq<T>, v2: Seq<T>, i: int, j: int) -> bool {
    v1.len() == v2.len() &&
    0 <= i < v1.len() &&
    0 <= j < v1.len() &&
    v2[i] == v1[j] &&
    v2[j] == v1[i] &&
    (forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v2[k] == v1[k])
}

proof fn swap_multiset_lemma<T>(v1: Seq<T>, v2: Seq<T>, i: int, j: int)
    requires swap_preserves_multiset(v1, v2, i, j)
    ensures v1.to_multiset() == v2.to_multiset()
{
    assert(v1.to_multiset().insert(v1[i]).remove(v1[i]) == v1.to_multiset());
    assert(v1.to_multiset().insert(v1[j]).remove(v1[j]) == v1.to_multiset());
    
    if i == j {
        assert(v1 == v2);
    } else {
        let ms1 = v1.to_multiset();
        let ms2 = v2.to_multiset();
        
        assert(ms1.contains(v1[i]) && ms1.contains(v1[j]));
        assert(ms2.contains(v2[i]) && ms2.contains(v2[j]));
        assert(v2[i] == v1[j] && v2[j] == v1[i]);
        
        let temp_ms = ms1.remove(v1[i]).remove(v1[j]).insert(v1[j]).insert(v1[i]);
        assert(temp_ms == ms1);
        assert(temp_ms == ms2);
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut left: usize = 0;
    let mut right: usize = a.len() - 1;
    let pivot_val = a[0];
    
    while left < right
        invariant
            left <= right,
            right < a.len(),
            forall|i: int| 0 <= i < left ==> a[i] < pivot_val,
            forall|i: int| right < i < a.len() ==> a[i] >= pivot_val,
            a@.to_multiset() == old(a)@.to_multiset(),
        decreases right - left,
    {
        while left < right && a[left] < pivot_val
            invariant
                left <= right,
                right < a.len(),
                forall|i: int| 0 <= i < left ==> a[i] < pivot_val,
                forall|i: int| right < i < a.len() ==> a[i] >= pivot_val,
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            left += 1;
        }
        
        while left < right && a[right] >= pivot_val
            invariant
                left <= right,
                right < a.len(),
                forall|i: int| 0 <= i < left ==> a[i] < pivot_val,
                forall|i: int| right < i < a.len() ==> a[i] >= pivot_val,
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            right -= 1;
        }
        
        if left < right {
            proof {
                swap_multiset_lemma(a@, a@.update(left as int, a@[right as int]).update(right as int, a@[left as int]), left as int, right as int);
            }
            let temp = a[left];
            let right_val = a[right];
            a.set(left, right_val);
            a.set(right, temp);
        }
    }
    
    if a[left] >= pivot_val && left > 0 {
        left -= 1;
    }
    
    if left != 0 {
        proof {
            swap_multiset_lemma(a@, a@.update(0, a@[left as int]).update(left as int, a@[0]), 0, left as int);
        }
        let temp = a[0];
        let left_val = a[left];
        a.set(0, left_val);
        a.set(left, temp);
    }
    
    left
}
// </vc-code>

fn main() {}

}