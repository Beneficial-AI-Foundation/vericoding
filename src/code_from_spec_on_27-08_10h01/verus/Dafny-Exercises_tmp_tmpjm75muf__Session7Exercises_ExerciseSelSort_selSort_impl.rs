use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
{
    &&& 0 <= i <= j <= a.len()
    &&& forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn min_index_in_range(a: Seq<int>, start: int, end: int) -> int;

proof fn min_index_correct(a: Seq<int>, start: int, end: int)
    requires 0 <= start < end <= a.len()
    ensures 
        start <= min_index_in_range(a, start, end) < end,
        forall|k: int| start <= k < end ==> a[min_index_in_range(a, start, end)] <= a[k]
{
}

proof fn swap_preserves_multiset(a: Seq<int>, b: Seq<int>, i: int, j: int, start: int, end: int)
    requires 
        0 <= i < a.len(),
        0 <= j < a.len(),
        a.len() == b.len(),
        b == a.update(i, a[j]).update(j, a[i]),
        start <= i < end <= a.len(),
        start <= j < end
    ensures a.subrange(start, end).to_multiset() == b.subrange(start, end).to_multiset()
{
}

proof fn swap_preserves_sorted_before(a: Seq<int>, b: Seq<int>, i: int, j: int, start: int, end: int)
    requires 
        0 <= i < a.len(),
        0 <= j < a.len(),
        a.len() == b.len(),
        b == a.update(i, a[j]).update(j, a[i]),
        sorted_seg(a, start, i + 1),
        start <= i < j < end <= a.len(),
        forall|k: int| i < k < end ==> a[j] <= a[k]
    ensures sorted_seg(b, start, i + 1)
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut i = c;
    while i < f
        invariant
            c <= i <= f,
            a.len() == old(a).len(),
            sorted_seg(a@, c as int, i as int),
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
            forall|k: int, l: int| c <= k < i && i <= l < f ==> a@[k] <= a@[l]
        decreases f - i
    {
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < f
            invariant
                i <= min_idx < j <= f,
                forall|k: int| i <= k < j ==> a@[min_idx as int] <= a@[k]
            decreases f - j
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            proof {
                swap_preserves_multiset(a@, a@.update(i as int, a@[min_idx as int]).update(min_idx as int, a@[i as int]), i as int, min_idx as int, c as int, f as int);
                swap_preserves_sorted_before(a@, a@.update(i as int, a@[min_idx as int]).update(min_idx as int, a@[i as int]), i as int, min_idx as int, c as int, f as int);
            }
            
            let temp = a[i];
            let min_val = a[min_idx];
            a.set(i, min_val);
            a.set(min_idx, temp);
        }
        
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}