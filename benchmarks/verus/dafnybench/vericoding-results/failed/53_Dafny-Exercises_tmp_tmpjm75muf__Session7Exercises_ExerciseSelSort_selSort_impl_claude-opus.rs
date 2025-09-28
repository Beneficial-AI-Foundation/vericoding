use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
{
    &&& 0 <= i <= j <= a.len()
    &&& forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
proof fn swap_maintains_multiset(a: Seq<int>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        a.update(i, a[j]).update(j, a[i]).to_multiset() == a.to_multiset(),
{
    let swapped = a.update(i, a[j]).update(j, a[i]);
    assert forall|v: int| #[trigger] swapped.to_multiset().count(v) == a.to_multiset().count(v) by {
        let count_orig = a.filter(|x: int| x == v).len();
        let count_swap = swapped.filter(|x: int| x == v).len();
        assert(count_orig == count_swap);
    }
}

proof fn subrange_multiset_swap(a: Seq<int>, i: int, j: int, start: int, end: int)
    requires
        0 <= start <= end <= a.len(),
        start <= i < end,
        start <= j < end,
    ensures
        a.update(i, a[j]).update(j, a[i]).subrange(start, end).to_multiset() == a.subrange(start, end).to_multiset(),
{
    let sub = a.subrange(start, end);
    let swapped = a.update(i, a[j]).update(j, a[i]);
    let sub_swapped = swapped.subrange(start, end);
    swap_maintains_multiset(sub, i - start, j - start);
}

proof fn sorted_seg_swap_min(a: Seq<int>, c: int, i: int, min_idx: int)
    requires
        0 <= c <= i < a.len(),
        i <= min_idx < a.len(),
        sorted_seg(a, c, i),
        forall|k: int| i <= k < a.len() ==> a[min_idx] <= a[k],
    ensures
        sorted_seg(a.update(i, a[min_idx]).update(min_idx, a[i]), c, i + 1),
{
    let swapped = a.update(i, a[min_idx]).update(min_idx, a[i]);
    assert forall|l: int, k: int| c <= l <= k < i + 1 implies #[trigger] swapped[l] <= #[trigger] swapped[k] by {
        if k == i {
            assert(swapped[i] == a[min_idx]);
            if l == i {
                assert(swapped[l] <= swapped[k]);
            } else {
                assert(l < i);
                assert(swapped[l] == a[l]);
                if i > c {
                    assert(a[l] <= a[i - 1]) by { assert(sorted_seg(a, c, i)); }
                    assert(a[min_idx] <= a[i]);
                    assert(swapped[l] <= swapped[k]);
                } else {
                    assert(swapped[l] <= swapped[k]);
                }
            }
        } else {
            assert(k < i);
            assert(swapped[l] == a[l]);
            assert(swapped[k] == a[k]);
            assert(sorted_seg(a, c, i));
            assert(swapped[l] <= swapped[k]);
        }
    }
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
    let mut i = c;
    while i < f
        invariant
            c <= i <= f,
            f <= a.len(),
            a.len() == old(a).len(),
            sorted_seg(a@, c as int, i as int),
            forall|k: int, l: int| c <= k < i && i <= l < f ==> #[trigger] a@[k] <= #[trigger] a@[l],
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
    {
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < f
            invariant
                c <= i < f,
                f <= a.len(),
                i <= min_idx < f,
                i < j <= f,
                min_idx < a.len(),
                a.len() == old(a).len(),
                sorted_seg(a@, c as int, i as int),
                forall|k: int, l: int| c <= k < i && i <= l < f ==> #[trigger] a@[k] <= #[trigger] a@[l],
                forall|k: int| i <= k < j ==> a@[min_idx as int] <= a@[k],
                a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        assert(forall|k: int| i <= k < f ==> a@[min_idx as int] <= a@[k]);
        
        if min_idx != i {
            let ghost a_before_swap = a@;
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
            
            proof {
                assert(a@ == a_before_swap.update(i as int, a_before_swap[min_idx as int]).update(min_idx as int, a_before_swap[i as int]));
                
                // Prove multiset preservation
                subrange_multiset_swap(a_before_swap, i as int, min_idx as int, c as int, f as int);
                
                // Prove subranges outside [c, f) are unchanged
                assert(a@.subrange(0, c as int) == a_before_swap.subrange(0, c as int));
                assert(a@.subrange(f as int, a.len() as int) == a_before_swap.subrange(f as int, a.len() as int));
                
                // Prove sorted segment extended
                sorted_seg_swap_min(a_before_swap, c as int, i as int, min_idx as int);
                
                // Prove the separation property
                assert forall|k: int, l: int| c <= k < i + 1 && i + 1 <= l < f implies #[trigger] a@[k] <= #[trigger] a@[l] by {
                    if k == i {
                        assert(a@[k] == a_before_swap[min_idx as int]);
                        assert(a_before_swap[min_idx as int] <= a_before_swap[l]);
                        if l == min_idx as int {
                            assert(a@[l] == a_before_swap[i as int]);
                            assert(a_before_swap[min_idx as int] <= a_before_swap[i as int]);
                        } else {
                            assert(a@[l] == a_before_swap[l]);
                        }
                        assert(a@[k] <= a@[l]);
                    } else {
                        assert(k < i);
                        assert(a@[k] == a_before_swap[k]);
                        if l == min_idx as int {
                            assert(a@[l] == a_before_swap[i as int]);
                            assert(a_before_swap[k] <= a_before_swap[i as int]);
                        } else {
                            assert(a@[l] == a_before_swap[l]);
                            assert(a_before_swap[k] <= a_before_swap[l]);
                        }
                        assert(a@[k] <= a@[l]);
                    }
                }
            }
        }
        
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}