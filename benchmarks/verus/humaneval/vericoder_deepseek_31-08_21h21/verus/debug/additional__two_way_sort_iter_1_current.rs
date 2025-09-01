use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn partition_lemma(s: Seq<bool>, l: int, r: int, count: int, p: bool)
    requires
        0 <= l <= r <= s.len(),
        count == s.subrange(l, r).count(|x| x),
    ensures
        s.count(|x| x) == count + s.subrange(0, l).count(|x| x) + s.subrange(r, s.len()).count(|x| x),
        s.to_multiset() == s.subrange(l, r).to_multiset() + s.subrange(0, l).to_multiset() + s.subrange(r, s.len()).to_multiset(),
{
}

proof fn slice_multiset_lemma<T>(s: Seq<T>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        s.to_multiset() == s.subrange(0, start).to_multiset() + s.subrange(start, end).to_multiset() + s.subrange(end, s.len()).to_multiset(),
{
}

proof fn reordering_lemma(s1: Seq<bool>, s2: Seq<bool>)
    requires
        s1.to_multiset() == s2.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < s2.len() ==> !s2[i] || s2[j],
    ensures
        s1.count(|x| x) == s2.count(|x| x),
        s1.count(|x| !x) == s2.count(|x| !x),
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    // pre-conditions-start
    requires
        old(a).len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    let mut i: usize = 0;
    let mut j: usize = len;
    let old_seq = a@;
    
    while i < j
        invariant
            0 <= i <= j <= len,
            a@.subrange(0, i).count(|x| !x) == old_seq.subrange(0, i).count(|x| !x),
            a@.subrange(j, len).count(|x| x) == old_seq.subrange(j, len).count(|x| x),
            a@.to_multiset() == old_seq.to_multiset(),
            forall|k: int| 0 <= k < i ==> !a@[k],
            forall|k: int| j <= k < len ==> a@[k],
            forall|k: int, l: int| 0 <= k < i <= l < len ==> !a@[k] || a@[l],
            forall|k: int, l: int| 0 <= k < j <= l < len ==> !a@[k] || a@[l],
    {
        if a[i] {
            j = j - 1;
            a.swap(i, j);
            proof {
                partition_lemma(a@, i, j + 1, a@.subrange(i, j + 1).count(|x| x), a@[i]);
                slice_multiset_lemma(a@, 0, i);
                slice_multiset_lemma(a@, j + 1, len);
            }
        } else {
            i = i + 1;
            proof {
                partition_lemma(a@, i, j, a@.subrange(i, j).count(|x| x), a@[i - 1]);
                slice_multiset_lemma(a@, 0, i);
                slice_multiset_lemma(a@, j, len);
            }
        }
    }
    
    proof {
        reordering_lemma(old_seq, a@);
        assert(a@.to_multiset() == old_seq.to_multiset());
        assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> !a@[i] || a@[j]);
    }
}
// </vc-code>

fn main() {}
}