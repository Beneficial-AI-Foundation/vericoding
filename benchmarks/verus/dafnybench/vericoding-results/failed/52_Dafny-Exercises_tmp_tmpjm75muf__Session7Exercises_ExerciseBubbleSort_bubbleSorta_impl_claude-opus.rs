use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<i32>, i: int, j: int) -> bool //j excluded
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
proof fn swap_preserves_multiset(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
    ensures
        a.update(i, a[j]).update(j, a[i]).to_multiset() == a.to_multiset()
{
    assert(a.update(i, a[j]).update(j, a[i]) =~= a.update(i, a[j]).update(j, a[i]));
}

proof fn swap_preserves_subrange_multiset(a: Seq<i32>, i: int, j: int, start: int, end: int)
    requires
        0 <= start <= end <= a.len(),
        start <= i < end,
        start <= j < end,
    ensures
        a.update(i, a[j]).update(j, a[i]).subrange(start, end).to_multiset() 
            == a.subrange(start, end).to_multiset()
{
    let swapped = a.update(i, a[j]).update(j, a[i]);
    assert forall|k: int| start <= k < end implies #[trigger] swapped[k] == 
        if k == i { a[j] } 
        else if k == j { a[i] } 
        else { a[k] } by {
        if k == i {
            assert(swapped[k] == a[j]);
        } else if k == j {
            assert(swapped[k] == a[i]);
        } else {
            assert(swapped[k] == a[k]);
        }
    }
}

proof fn swap_preserves_outside_range(a: Seq<i32>, i: int, j: int, start: int, end: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
        0 <= start <= end <= a.len(),
        start <= i < end,
        start <= j < end,
    ensures
        a.update(i, a[j]).update(j, a[i]).subrange(0, start) == a.subrange(0, start),
        a.update(i, a[j]).update(j, a[i]).subrange(end, a.len() as int) == a.subrange(end, a.len() as int)
{
    let swapped = a.update(i, a[j]).update(j, a[i]);
    assert forall|k: int| 0 <= k < start implies #[trigger] swapped[k] == a[k] by {}
    assert forall|k: int| end <= k < a.len() implies #[trigger] swapped[k] == a[k] by {}
}
// </vc-helpers>

// <vc-spec>
fn bubbleSorta(a: &mut Vec<i32>, c: usize, f: usize) //f excluded
    requires 
        c <= f,
        f <= old(a).len(), //when c==f empty sequence
    ensures 
        sorted_seg(a@, c as int, f as int),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
// </vc-spec>
// <vc-code>
{
    if c >= f {
        return;
    }
    
    let mut i = f - 1;
    while i > c
        invariant
            c <= i < f,
            f <= a.len(),
            sorted_seg(a@, (i + 1) as int, f as int),
            forall|k: int, l: int| (i as int) <= k < (i + 1) as int && (i + 1) as int <= l < f as int 
                ==> #[trigger] a@[k] <= #[trigger] a@[l],
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
        decreases i - c
    {
        let mut j = c;
        while j < i
            invariant
                c <= j <= i < f,
                f <= a.len(),
                sorted_seg(a@, (i + 1) as int, f as int),
                forall|k: int| c as int <= k <= j as int ==> #[trigger] a@[k] <= a@[j as int],
                forall|k: int, l: int| j as int <= k < (i + 1) as int && (i + 1) as int <= l < f as int 
                    ==> #[trigger] a@[k] <= #[trigger] a@[l],
                a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
                a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
                a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
        {
            if a[j] > a[j + 1] {
                proof {
                    swap_preserves_subrange_multiset(a@, j as int, (j + 1) as int, c as int, f as int);
                    swap_preserves_outside_range(a@, j as int, (j + 1) as int, c as int, f as int);
                }
                let temp = a[j];
                let temp2 = a[j + 1];
                a.set(j, temp2);
                a.set(j + 1, temp);
            }
            j = j + 1;
        }
        
        assert(sorted_seg(a@, i as int, f as int)) by {
            assert forall|l: int, k: int| i as int <= l <= k < f as int implies #[trigger] a@[l] <= #[trigger] a@[k] by {
                if l == i as int && k == i as int {
                } else if l == i as int && k > i as int {
                    assert(a@[l] <= a@[k]);
                } else {
                    assert(sorted_seg(a@, (i + 1) as int, f as int));
                }
            }
        }
        
        i = i - 1;
    }
    
    assert(sorted_seg(a@, c as int, f as int)) by {
        assert forall|l: int, k: int| c as int <= l <= k < f as int implies #[trigger] a@[l] <= #[trigger] a@[k] by {
            if l == c as int && k == c as int {
            } else if l == c as int && k > c as int {
                assert((c + 1) as int <= k < f as int);
                assert(sorted_seg(a@, (c + 1) as int, f as int));
                assert(a@[l] <= a@[k]);
            } else {
                assert(sorted_seg(a@, (c + 1) as int, f as int));
                assert(a@[l] <= a@[k]);
            }
        }
    }
}
// </vc-code>

fn main() {}

}