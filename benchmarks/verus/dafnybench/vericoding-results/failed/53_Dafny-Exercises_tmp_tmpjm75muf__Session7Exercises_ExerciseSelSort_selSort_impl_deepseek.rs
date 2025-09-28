use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
{
    &&& 0 <= i <= j <= a.len()
    &&& forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn min_index_seg(a: Seq<int>, i: int, j: int) -> int
    recommends i < j
    decreases j - i
{
    if j - i == 1 {
        i
    } else {
        let mid = i + (j - i)/2;
        let left_min = min_index_seg(a, i, mid);
        let right_min = min_index_seg(a, mid, j);
        if a[left_min] <= a[right_min] { left_min } else { right_min }
    }
}

proof fn min_index_seg_decreases(a: Seq<int>, i: int, j: int)
    requires i < j
    ensures min_index_seg(a, i, j) >= i && min_index_seg(a, i, j) < j
    decreases j - i
{
    if j - i == 1 {
    } else {
        let mid = i + (j - i)/2;
        min_index_seg_decreases(a, i, mid);
        min_index_seg_decreases(a, mid, j);
    }
}

proof fn min_index_seg_correct(a: Seq<int>, i: int, j: int, k: int)
    requires i <= k < j
    ensures a[min_index_seg(a, i, j)] <= a[k]
    decreases j - i
{
    if j - i == 1 {
        assert(min_index_seg(a, i, j) == i);
    } else {
        let mid = i + (j - i)/2;
        if k < mid {
            min_index_seg_correct(a, i, mid, k);
        } else {
            min_index_seg_correct(a, mid, j, k);
        }
    }
}

spec fn swap(a: Seq<int>, i: int, j: int) -> Seq<int>
    requires 0 <= i < a.len() && 0 <= j < a.len()
{
    a.update(i, a[j]).update(j, a[i])
}

proof fn swap_preserves_multiset(a: Seq<int>, i: int, j: int)
    requires 0 <= i < a.len() && 0 <= j < a.len()
    ensures swap(a, i, j).to_multiset() == a.to_multiset()
{
}

proof fn swap_preserves_unrelated_segments(a: Seq<int>, i: int, j: int, start: int, end: int)
    requires 0 <= start <= end <= a.len(), 0 <= i < a.len(), 0 <= j < a.len(), 
        end <= i || j < start || (i < start && end <= j) || (j < start && end <= i)
    ensures swap(a, i, j)@.subrange(start, end) == a@.subrange(start, end)
{
}
// </vc-helpers>

// <vc-spec>
fn sel_sort(a: &mut Vec<int>, c: usize, f: usize)
    requires 
        c <= f <= old(a).len(),
    ensures 
        sorted_seg(a@, c as int, f as int),
        a.len() == old(a).len(),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
// </vc-spec>
// <vc-code>
{
    let mut idx = c;
    while idx < f
        invariant 
            c <= idx <= f <= a.len(),
            sorted_seg(a@, c as int, idx as int),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
            a@.to_multiset() == old(a)@.to_multiset(),
        decreases f - idx
    {
        let a_seq = a@;
        ghost {
            min_index_seg_decreases(a_seq, idx as int, f as int);
            let min_idx_val = min_index_seg(a_seq, idx as int, f as int);
            assert(min_idx_val >= idx as int && min_idx_val < f as int);
        }
        
        let min_idx = ghost!(min_index_seg(a@, idx as int, f as int) as usize);
        assert(min_idx@ >= idx && min_idx@ < f);
        
        if idx != min_idx@ {
            let temp = a[idx];
            a.set(idx, a[min_idx@]);
            a.set(min_idx@, temp);
            proof {
                swap_preserves_multiset(a@, idx as int, min_idx@ as int);
                swap_preserves_unrelated_segments(a@, idx as int, min_idx@ as int, 0, c as int);
                swap_preserves_unrelated_segments(a@, idx as int, min_idx@ as int, f as int, a.len() as int);
            }
        }
        
        proof {
            let a_seq = a@;
            assert forall|l: int, k: int| idx as int <= l <= k < (idx + 1) as int implies a_seq[l] <= a_seq[k] by {
                if l == k {
                } else {
                    assert(false);
                }
            };
            
            assert forall|l: int, k: int| c as int <= l <= k < (idx + 1) as int implies a_seq[l] <= a_seq[k] by {
                if k < idx as int {
                    assert(sorted_seg(a_seq, c as int, idx as int));
                } else if l >= idx as int {
                    assert(l == idx as int && k == idx as int);
                } else {
                    assert(sorted_seg(a_seq, c as int, idx as int));
                    let min_val = a_seq[min_index_seg(a_seq, idx as int, f as int)];
                    min_index_seg_correct(a_seq, idx as int, f as int, k as int);
                    assert(a_seq[l] <= a_seq[k]);
                }
            };
        }
        
        idx = idx + 1;
    }
}
// </vc-code>

fn main() {}

}