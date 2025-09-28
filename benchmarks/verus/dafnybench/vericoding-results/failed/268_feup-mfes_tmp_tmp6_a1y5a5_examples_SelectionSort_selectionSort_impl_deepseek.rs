use vstd::prelude::*;

verus! {

/* 
* Formal verification of the selection sort algorithm with Verus.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
spec fn is_sorted(a: Seq<i32>, from: int, to: int) -> bool
    recommends 0 <= from <= to <= a.len()
{
    forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

// Sorts array 'a' using the selection sort algorithm.

// Finds the position of a minimum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
fn find_min(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: int| from as int <= k < to as int ==> a@[k] >= a@[index as int],
{
    assume(false);
    0
}

// <vc-helpers>
spec fn min_index_in_range(a: Seq<i32>, from: int, to: int, idx: int) -> bool {
    from <= idx < to && forall|k: int| from <= k < to ==> a[k] >= a[idx]
}

proof fn swap_preserves_multiset<T>(v: &mut Vec<T>, i: usize, j: usize)
    requires
        0 <= i < old(v)@.len(),
        0 <= j < old(v)@.len(),
    ensures
        v@.to_multiset() == old(v)@.to_multiset(),
{
    assert(v@.update(i as int, old(v)@[j as int]).update(j as int, old(v)@[i as int]).to_multiset() == old(v)@.to_multiset());
}

proof fn vec_ext_eq<T>(v1: &Vec<T>, v2: &Vec<T>)
    requires
        v1@ == v2@,
    ensures
        v1@.to_multiset() == v2@.to_multiset(),
{
    assert(v1@.to_multiset() == v2@.to_multiset());
}

spec fn permuted<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}

spec fn still_permuted<T>(s_old: Seq<T>, s_new: Seq<T>, from: int) -> bool {
    forall|i: int| 0 <= i < from ==> s_old[i] == s_new[i]
}

proof fn find_min_ensures_min(a: &Vec<i32>, from: usize, to: usize, index: usize)
    requires
        0 <= from < to <= a.len(),
        from <= index < to,
        forall|k: int| from as int <= k < to as int ==> a@[k] >= a@[index as int],
    ensures
        min_index_in_range(a@, from as int, to as int, index as int),
{
    assert(min_index_in_range(a@, from as int, to as int, index as int));
}

fn find_min_impl(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: int| from as int <= k < to as int ==> a@[k] >= a@[index as int],
{
    let mut min_idx = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_idx < to,
            from <= i <= to,
            forall|k: int| from as int <= k < i as int ==> a@[k] >= a@[min_idx as int],
        decreases to - i,
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    min_idx
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures 
        is_sorted(a@, 0, a@.len() as int),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let mut idx: usize = 0;
    let length = a.len();
    
    while idx < length
        invariant
            0 <= idx <= length,
            is_sorted(a@, 0, idx as int),
            permuted(a@, old(a)@),
            still_permuted(old(a)@, a@, idx as int),
        decreases length - idx,
    {
        if idx < length - 1 {
            let min_idx = find_min_impl(a, idx, length);
            proof {
                find_min_ensures_min(a, idx, length, min_idx);
            }
            if min_idx != idx {
                proof {
                    swap_preserves_multiset(a, idx, min_idx);
                }
                a.swap(idx, min_idx);
            }
        }
        idx = idx + 1;
        
        proof {
            assert(still_permuted(old(a)@, a@, idx as int));
            assert(is_sorted(a@, 0, idx as int));
        }
    }
    
    proof {
        assert(is_sorted(a@, 0, length as int));
        vec_ext_eq(a, a);
    }
}
// </vc-code>

fn main() {}

}