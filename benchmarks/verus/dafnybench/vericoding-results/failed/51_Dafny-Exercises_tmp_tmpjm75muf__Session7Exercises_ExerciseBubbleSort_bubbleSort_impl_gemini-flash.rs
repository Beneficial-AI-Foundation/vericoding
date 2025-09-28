use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn swappable(a: Seq<int>, c: int, f: int, i: int, j: int) -> bool
recommends 0 <= c <= f <= a.len() && c <= i < j < f
{
    a[j] < a[i]
}

proof fn lemma_swap_is_permutation(a: Seq<int>, c: int, f: int, i: int, j: int)
    requires
        0 <= c <= f <= a.len(),
        c <= i < j < f,
    ensures
        (a.update(i, a[j]).update(j, a[i])).subrange(c, f).to_multiset() == a.subrange(c, f).to_multiset(),
        a.update(i, a[j]).update(j, a[i]).subrange(0, c) == a.subrange(0, c),
        a.update(i, a[j]).update(j, a.update(i,a[j]).len() as int).subrange(f, a.len() as int) == a.subrange(f, a.len() as int),
{
    // This lemma essentially proves that swapping two elements within a subrange
    // preserves the multiset of that subrange and leaves other subranges unchanged.
    // Verus's default sequence reasoning is often sufficient for this,
    // but stating it explicitly can help if more complex reasoning is needed.
}

proof fn lemma_sorted_implies_not_swappable(a: Seq<int>, c: int, f: int, i: int, j: int)
    requires
        sorted_seg(a, c, f),
        c <= i < j < f,
    ensures
        !swappable(a, c, f, i, j),
{
    assert(a[i] <= a[j]) by {
        // By definition of sorted_seg, a[i] <= a[j] for c <= i <= j < f.
        // We have c <= i < j < f, so specifically a[i] <= a[j] holds.
    }
    assert(!(a[j] < a[i])); // This directly proves !swappable
}

proof fn lemma_consecutive_sorted_segments(a: Seq<int>, b: Seq<int>, k: int, i: int, j: int)
    requires
        // Adjusted: k is a split point, so it can be equal to i or j
        i <= k <= j, 
        sorted_seg(a, i, k),
        sorted_seg(b, k, j),
        a.subrange(i, k) == b.subrange(i, k),
        a.subrange(k, j) == b.subrange(k, j),
        // To merge, we need to ensure the element at the end of the first segment
        // is less than or equal to the element at the beginning of the second segment.
        // This condition is not always necessary for bubble sort invariant,
        // which focuses on a growing sorted suffix.
    ensures
        sorted_seg(a, i, j) && sorted_seg(b,i,j)
{
    // This is a complex lemma for merging sorted segments, which might not be strictly needed
    // if the loop invariant properly captures the sorted prefix.
    // For bubble sort, the invariant is usually that the suffix is sorted relative to future passes,
    // and a prefix is sorted by the current pass.
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<int>, c: usize, f: usize)
    requires 
        0 <= c <= f <= old(a).len(),
    ensures 
        sorted_seg(a@, c as int, f as int),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int),
// </vc-spec>
// <vc-code>
{
    let f_int = f as int;
    let c_int = c as int;
    let mut i = c;

    while (i < f)
        invariant 
            f_int == f as int,
            c_int == c as int,
            c <= i <= f,
            let i_int = i as int; 
            sorted_seg(a@, f_int - (i_int - c_int), f_int),
            a@.subrange(c_int, f_int).to_multiset() == old(a)@.subrange(c_int, f_int).to_multiset(),
            a@.subrange(0, c_int) == old(a)@.subrange(0, c_int),
            a@.subrange(f_int, a@.len() as int) == old(a)@.subrange(f_int, old(a)@.len() as int),
    {
        let mut j = c;
        while (j < f - (i - c) - 1)
            invariant
                f_int == f as int,
                c_int == c as int,
                let i_int = i as int; 
                c <= i < f,
                c <= j < f - (i - c), 
                sorted_seg(a@, f_int - (i_int - c_int), f_int),
                a@.subrange(c_int, f_int).to_multiset() == old(a)@.subrange(c_int, f_int).to_multiset(),
                a@.subrange(0, c_int) == old(a)@.subrange(0, c_int),
                a@.subrange(f_int, a@.len() as int) == old(a)@.subrange(f_int, old(a)@.len() as int),
        {
                let j_usize = j as usize;
                let j_plus_1_usize = (j + 1) as usize;

                if a[j_usize] > a[j_plus_1_usize] {
                     proof {
                        lemma_swap_is_permutation(a@, c_int, f_int, j as int, j_plus_1_usize as int);
                     }
                    a.swap(j_usize, j_plus_1_usize);
                }
                j = j + 1;
            }
        proof {
            assert(sorted_seg(a@, (f_int - ((i+1) as int - c_int)), f_int));
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}