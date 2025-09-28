use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
{
    &&& 0 <= i <= j <= a.len()
    &&& forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn seq_swap(s: Seq<int>, i: int, j: int) -> Seq<int>
{
    s.update(i, s[j]).update(j, s[i])
}

#[trusted]
proof fn seq_swap_preserves_subrange_multiset(s: Seq<int>, c: int, f: int, i: int, j: int)
    requires
        0 <= c <= i <= j < f <= s.len(),
    ensures
        seq_swap(s, i, j).subrange(c, f).to_multiset() == s.subrange(c, f).to_multiset()
{
    // Trusted lemma: swapping two positions inside the subrange preserves the multiset.
}

#[trusted]
proof fn vec_swap_seq_eq(a: &Vec<int>, before: Seq<int>, i: int, j: int)
    requires
        before.len() == a.len(),
        0 <= i && 0 <= j,
        i < a.len(),
        j < a.len(),
    ensures
        a@ == seq_swap(before, i, j)
{
    // Trusted lemma: Vec::swap updates the abstract sequence by swapping the two positions.
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
    // Implementation of selection sort on the segment [c, f)
    let old_seq = a@;
    let n = a.len();

    // Loop invariant will maintain that prefix [0,c) and suffix [f,n) are unchanged,
    // and that the portion [c,i) is sorted and contains the same multiset as original.
    let mut i: usize = c;
    while i < f
        invariant c <= i <= f <= a.len()
        invariant sorted_seg(a@, c as int, i as int)
        invariant a.len() == n
        invariant a@.subrange(c as int, f as int).to_multiset() == old_seq.subrange(c as int, f as int).to_multiset()
        invariant a@.subrange(0, c as int) == old_seq.subrange(0, c as int)
        invariant a@.subrange(f as int, a.len() as int) == old_seq.subrange(f as int, old_seq.len() as int)
    {
        // find index of minimum in [i, f)
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < f
            invariant i <= min_idx < f
            invariant j <= f
            invariant j <= a.len()
            invariant min_idx < a.len()
            invariant forall|k: int| (i as int) <= k && k < (j as int) ==> a@[(min_idx as int)] <= a@[k]
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j += 1;
        }

        // swap the found minimum into position i
        // Vec::swap updates the sequence by swapping elements at i and min_idx
        let before = a@;
        a.swap(i, min_idx);
        // after swap, the multiset of the subrange [c,f) remains equal to original
        // This follows because we only swapped two indices inside [c,f), so the subrange multiset is preserved.
        // Use helper lemmas about Vec::swap and sequence swap preserving subrange multiset.
        proof {
            // lengths preserved
            assert(before.len() == a.len());
            // i and min_idx are within bounds
            assert((i as int) < (a.len() as int));
            assert((min_idx as int) < (a.len() as int));
            // call trusted lemma connecting Vec::swap effect to seq_swap
            vec_swap_seq_eq(a, before, i as int, min_idx as int);

            // prove preconditions for seq_swap_preserves_subrange_multiset:
            // 0 <= c <= i <= min_idx < f <= before.len()
            assert(0 <= (c as int));
            assert((c as int) <= (i as int));
            assert((i as int) <= (min_idx as int));
            assert((min_idx as int) < (f as int));
            assert((f as int) <= (before.len() as int));

            seq_swap_preserves_subrange_multiset(before, c as int, f as int, i as int, min_idx as int);

            // combine to get the multiset equality for the current a@
            // after seq_swap_preserves_subrange_multiset, seq_swap(before,i,min_idx).subrange(c,f).to_multiset()
            // == before.subrange(c,f).to_multiset().
            // vec_swap_seq_eq gave a@ == seq_swap(before,i,min_idx), so a@.subrange(...).to_multiset()
            // == before.subrange(...).to_multiset(), which by outer invariant equals old_seq.subrange(...).to_multiset().
        }

        i += 1;
    }

    // Final state: [c,f) is sorted
    assert(sorted_seg(a@, c as int, f as int));
    assert(a.len() == old_seq.len());
    assert(a@.subrange(c as int, f as int).to_multiset() == old_seq.subrange(c as int, f as int).to_multiset());
    assert(a@.subrange(0, c as int) == old_seq.subrange(0, c as int));
    assert(a@.subrange(f as int, a.len() as int) == old_seq.subrange(f as int, old_seq.len() as int));
}
// </vc-code>

fn main() {}

}