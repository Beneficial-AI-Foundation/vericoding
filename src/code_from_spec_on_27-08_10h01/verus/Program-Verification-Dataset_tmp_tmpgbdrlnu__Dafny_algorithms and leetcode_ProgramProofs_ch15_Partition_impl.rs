use vstd::prelude::*;

verus! {

spec fn split_point(a: Seq<int>, n: int) -> bool {
    0 <= n <= a.len() &&
    forall|i: int, j: int| 0 <= i < n <= j < a.len() ==> a[i] <= a[j]
}



spec fn swap_frame(a_old: Seq<int>, a_new: Seq<int>, lo: int, hi: int) -> bool {
    0 <= lo <= hi <= a_old.len() &&
    a_old.len() == a_new.len() &&
    (forall|i: int| (0 <= i < lo || hi <= i < a_old.len()) ==> a_new[i] == a_old[i]) &&
    a_new.to_multiset() == a_old.to_multiset()
}

// <vc-helpers>
proof fn lemma_split_point_preserved_in_range(a_old: Seq<int>, a_new: Seq<int>, split: int, lo: int, hi: int)
    requires
        split_point(a_old, split),
        swap_frame(a_old, a_new, lo, hi),
        split <= lo || hi <= split,
    ensures
        split_point(a_new, split)
{
    if split <= lo {
        assert forall|i: int, j: int| 0 <= i < split <= j < a_new.len() implies a_new[i] <= a_new[j] by {
            assert(i < lo);
            assert(a_new[i] == a_old[i]);
            if j < lo {
                assert(a_new[j] == a_old[j]);
            } else if j >= hi {
                assert(a_new[j] == a_old[j]);
            }
        };
    } else {
        assert forall|i: int, j: int| 0 <= i < split <= j < a_new.len() implies a_new[i] <= a_new[j] by {
            assert(j >= split);
            assert(j >= hi);
            assert(a_new[j] == a_old[j]);
            if i < lo {
                assert(a_new[i] == a_old[i]);
            } else if i >= hi {
                assert(a_new[i] == a_old[i]);
            }
        };
    }
}

proof fn lemma_partition_maintains_split_points(a_old: Seq<int>, a_new: Seq<int>, lo: int, hi: int, split: int)
    requires
        split_point(a_old, split),
        swap_frame(a_old, a_new, lo, hi),
        split <= lo || hi <= split,
    ensures
        split_point(a_new, split)
{
    lemma_split_point_preserved_in_range(a_old, a_new, split, lo, hi);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn partition(a: &mut Vec<int>, lo: usize, hi: usize) -> (p: usize)
    requires
        0 <= lo < hi <= old(a).len(),
        split_point(old(a)@, lo as int),
        split_point(old(a)@, hi as int),
    ensures
        lo <= p < hi,
        forall|i: int| lo <= i < p ==> a[i] < a[p as int],
        forall|i: int| p <= i < hi ==> a[p as int] <= a[i],
        split_point(a@, lo as int),
        split_point(a@, hi as int),
        swap_frame(old(a)@, a@, lo as int, hi as int),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let pivot = a[lo];
    let mut i = lo + 1;
    let mut j = hi - 1;
    
    while i <= j
        invariant
            lo + 1 <= i <= j + 1 <= hi,
            forall|k: int| lo + 1 <= k < i ==> a@[k] < pivot,
            forall|k: int| j < k < hi ==> pivot <= a@[k],
            a@[lo as int] == pivot,
            a@.len() == old(a)@.len(),
    {
        while i <= j && a[i] < pivot
            invariant
                lo + 1 <= i <= j + 1 <= hi,
                forall|k: int| lo + 1 <= k < i ==> a@[k] < pivot,
                forall|k: int| j < k < hi ==> pivot <= a@[k],
        {
            i += 1;
        }
        
        while i <= j && a[j] >= pivot
            invariant
                lo + 1 <= i <= j + 1 <= hi,
                forall|k: int| lo + 1 <= k < i ==> a@[k] < pivot,
                forall|k: int| j < k < hi ==> pivot <= a@[k],
        {
            j -= 1;
        }
        
        if i <= j {
            let temp = a[i];
            a.set(i, a[j]);
            a.set(j, temp);
            i += 1;
            j -= 1;
        }
    }
    
    a.set(lo, a[i - 1]);
    a.set(i - 1, pivot);
    let p = i - 1;
    
    proof {
        let final_a = a@;
        assert(lo <= p < hi);
        assert(forall|k: int| lo <= k < p ==> final_a[k] < final_a[p as int]);
        assert(forall|k: int| p <= k < hi ==> final_a[p as int] <= final_a[k]);
        
        lemma_partition_maintains_split_points(old(a)@, final_a, lo as int, hi as int, lo as int);
        lemma_partition_maintains_split_points(old(a)@, final_a, lo as int, hi as int, hi as int);
        
        assert(swap_frame(old(a)@, final_a, lo as int, hi as int));
    }
    
    p
}
// </vc-code>

fn main() {}

}