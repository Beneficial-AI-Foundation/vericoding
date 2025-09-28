use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
{
    &&& 0 <= i <= j <= a.len()
    &&& forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
{
    &&& 0 <= i <= j <= a.len()
    &&& forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
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
        decreases (f as int - i as int)
        invariant {
            c <= i <= f,
            sorted_seg(a@, c as int, i as int),
            a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
            a.len() == old(a).len()
        }
    {
        proof {
            assert(sorted_seg(a@, c as int, i as int));
            assert(a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset());
        }
        let mut min_idx = i;
        let mut j = i + 1;
        while j < f
            decreases (f as int - j as int)
            invariant {
                i <= j <= f,
                min_idx >= i,
                min_idx < j,
                forall|k: int| i <= k < j ==> a@[min_idx as int] <= a@[k as int]
            }
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        let tmp = a[i];
        a[i] = a[min_idx];
        a[min_idx] = tmp;
        i += 1;
    }
}
// </vc-code>

fn main() {}

}