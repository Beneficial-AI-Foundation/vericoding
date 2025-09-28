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

proof fn lemma_subrange_fresh<T>(s: Seq<T>, start: int, end: int, fresh_start: int, fresh_end: int)
    requires
        0 <= start <= end <= s.len(),
        0 <= fresh_start <= fresh_end <= s.len(),
    ensures
        s.subrange(fresh_start, fresh_end) 
            == s.subrange(fresh_start, start) 
                + s.subrange(start, end) 
                + s.subrange(end, fresh_end),
{
}

proof fn lemma_permutation_multiset_eq<T>(s1: Seq<T>, s2: Seq<T>, start: int, end: int)
    requires
        0 <= start <= end <= s1.len(),
        0 <= start <= end <= s2.len(),
        s1.subrange(start, end) =~= s2.subrange(start, end),
    ensures
        s1.subrange(start, end).to_multiset() == s2.subrange(start, end).to_multiset(),
{
    assert(s1.subrange(start, end).to_multiset() =~= s2.subrange(start, end).to_multiset());
}

proof fn lemma_seq_permutation_preserves_other_subrange<T>(a1: Seq<T>, a2: Seq<T>, start: int, end: int, other_start: int, other_end: int)
    requires
        0 <= start <= end <= a1.len(),
        0 <= start <= end <= a2.len(),
        0 <= other_start <= other_end <= a1.len(),
        0 <= other_start <= other_end <= a2.len(),
        other_end <= start || other_start >= end,
        a1.subrange(start, end) =~= a2.subrange(start, end),
    ensures
        a1.subrange(other_start, other_end) == a2.subrange(other_start, other_end),
{
    if other_end <= start {
        lemma_subrange_fresh(a1, start, end, other_start, other_end);
        lemma_subrange_fresh(a2, start, end, other_start, other_end);
        assert(a1.subrange(other_start, other_end) =~= a2.subrange(other_start, other_end));
    } else if other_start >= end {
        lemma_subrange_fresh(a1, start, end, other_start, other_end);
        lemma_subrange_fresh(a2, start, end, other_start, other_end);
        assert(a1.subrange(other_start, other_end) =~= a2.subrange(other_start, other_end));
    }
}

proof fn lemma_sorted_seg_permutation(a1: Seq<int>, a2: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end <= a1.len(),
        0 <= start <= end <= a2.len(),
        sorted_seg(a1, start, end),
        a1.subrange(start, end) =~= a2.subrange(start, end),
    ensures
        sorted_seg(a2, start, end),
{
    assert forall|l, k: int| start <= l <= k < end implies a2[l] <= a2[k] by {
        assert(a1[l] <= a1[k]);
    }
}

fn find_min_index(a: &Vec<int>, start: usize, end: usize) -> (min_index: usize)
    requires
        start < end <= a.len(),
    ensures
        (start as int) <= (min_index as int) < (end as int),
        forall|j: int| (start as int) <= j < (end as int) ==> a@[min_index as int] <= a@[j],
{
    let mut min_index = start;
    let mut i = start + 1;
    while i < end
        invariant 
            (start as int) <= (min_index as int) < (i as int),
            forall|j: int| (start as int) <= j < (i as int) ==> a@[min_index as int] <= a@[j],
    {
        if a[i] < a[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    min_index
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
    let mut n = c;
    while n < f
        invariant
            c <= n <= f,
            sorted_seg(a@, c as int, n as int),
            a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
            a@.subrange(n as int, f as int).to_multiset() == old(a)@.subrange(n as int, f as int).to_multiset(),
            a@.subrange(f as int, a.len() as int) == old(a)@.subrange(f as int, old(a).len() as int),
    {
        let min_index = find_min_index(a, n, f);
        if min_index != n {
            a.swap(n, min_index);
            proof {
                let a_pre = old(a)@;
                let a_post = a@;
                assert(a_pre.subrange(n as int, min_index as int) =~= a_post.subrange(n as int, min_index as int));
                assert(a_pre.subrange(min_index as int, min_index as int + 1) =~= a_post.subrange(min_index as int, min_index as int + 1));
                assert(a_pre.subrange(n as int, f as int) =~= a_post.subrange(n as int, f as int));
                lemma_permutation_multiset_eq(a_pre, a_post, n as int, f as int);
                lemma_sorted_seg_permutation(a_pre, a_post, n as int, f as int);
            }
        }
        n = n + 1;
    }
}
// </vc-code>

fn main() {}

}