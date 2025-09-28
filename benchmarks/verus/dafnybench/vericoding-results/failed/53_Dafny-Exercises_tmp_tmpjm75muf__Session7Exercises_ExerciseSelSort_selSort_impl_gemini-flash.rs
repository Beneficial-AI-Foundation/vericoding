use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
{
    &&& 0 <= i <= j <= a.len()
    &&& forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
fn get_min_idx_in_range(
    a: &Vec<int>,
    start: usize,
    end: usize,
    ghost_a: Seq<int>,
) -> (min_idx: usize)
    requires
        start <= end <= a.len(),
        a@ == ghost_a,
    ensures
        start <= min_idx < end,
        forall|k: int| start as int <= k < end as int ==> a@[min_idx as int] <= a@[k],
{
    let mut min_idx: usize = start;
    let mut i: usize = start + 1;

    let ghost_a_1 = ghost_a;
    while i < end
        invariant
            a@ == ghost_a_1,
            start < end, // Added this invariant for termination
            start <= min_idx < i <= end,
            forall|k: int| start as int <= k < i as int ==> a@[min_idx as int] <= a@[k],
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i = i + 1;
    }
    min_idx
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
    let mut i: usize = c;
    let old_a_len = a.len(); // Use a.len() directly within the method, capture old(a)@ outside
    let old_a_seq = a@;

    while i < f
        invariant
            i <= f <= old_a_len,
            a.len() == old_a_len,
            sorted_seg(a@, c as int, i as int),
            a@.subrange(0, c as int) == old_a_seq.subrange(0, c as int),
            a@.subrange(f as int, a.len() as int) == old_a_seq.subrange(f as int, old_a_len as int),
            // The elements from c to i are sorted and contain the smallest elements
            // from the original subrange c to f
            a@.subrange(c as int, i as int).to_multiset().add(a@.subrange(i as int, f as int).to_multiset())
                == old_a_seq.subrange(c as int, f as int).to_multiset(),
            forall|x: int, y: int|
                c as int <= x < i as int && #[trigger] i as int <= y < f as int
                ==> a@[x] <= a@[y],
    {
        let ghost_a_at_i = a@;
        let min_idx = get_min_idx_in_range(a, i, f, ghost_a_at_i);
        assert(a@ == ghost_a_at_i); // Assert that a@ has not changed
        assert(min_idx >= i && min_idx < f);

        let temp = a[i];
        a.set(i, a[min_idx]);
        a.set(min_idx, temp);

        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}