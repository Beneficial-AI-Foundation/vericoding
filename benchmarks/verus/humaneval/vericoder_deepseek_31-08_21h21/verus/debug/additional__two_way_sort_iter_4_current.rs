use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn partition_lemma(s: Seq<bool>, l: int, r: int, count: int, p: bool)
    requires
        0 <= l <= r <= s.len(),
        count == s.subrange(l, r).filter(|x: bool| x).len() as int,
    ensures
        s.filter(|x: bool| x).len() as int == count + s.subrange(0, l).filter(|x: bool| x).len() as int + s.subrange(r, s.len() as int).filter(|x: bool| x).len() as int,
        s.to_multiset() == s.subrange(l, r).to_multiset().add(s.subrange(0, l).to_multiset()).add(s.subrange(r, s.len() as int).to_multiset()),
{
}

proof fn slice_multiset_lemma<T>(s: Seq<T>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        s.to_multiset() == s.subrange(0, start).to_multiset().add(s.subrange(start, end).to_multiset()).add(s.subrange(end, s.len() as int).to_multiset()),
{
}

proof fn reordering_lemma(s1: Seq<bool>, s2: Seq<bool>)
    requires
        s1.to_multiset() == s2.to_multiset(),
        forall|i: int, j: int| 极 0 <= i < j < s2.len() ==> !s2[i] || s2[j],
    ensures
        s1.filter(|x: bool| x).极 len() as int == s2.filter(|x: bool| x).len() as int,
        s1.filter(|x: bool| !x).len() as int == s2.filter(|x: bool| !x).len() as int,
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
            0 <= i as int <= j as int <= len as int,
            a@.subrange(0, i as int).filter(|x: bool| !x).len() as int == old_seq.subrange(0, i as int).filter(|x: bool| !x).len() as int,
            a@.subrange(j as int, len as int).filter(|x: bool| x).len() as int == old_seq.subrange(j as int, len as int).filter(|x: bool| x).len() as int,
            a@.to_multiset() == old_seq.to_multiset(),
            forall|k: int| 0 <= k < i as int ==> !a@[k],
            forall|k: int| j as int <= k < len as int ==> a@[k],
            forall|极 k: int, l: int| 0 <= k < i as int <= l < len as int ==> !a@[k] || a@[l],
            forall|k: int, l: int| 0 <= k < j as int <= l < len as int ==> !a@[k] || a@[l],
    {
        if a[i] {
            j = j - 1;
            a.swap(i, j);
            proof {
                partition_lemma(a@, i as int, (j + 1) as int, a@.subrange(i as int, (j + 1) as int).filter(|x: bool| x).len() as int, a@[i as int]);
                slice_multiset_lemma(a@, 0, i as int);
                slice_multiset_lemma(a@, (j + 1) as int, len as int);
            }
        } else {
            i = i + 1;
            proof {
                partition_lemma(a@, i as int, j as int, a@.subrange(i as int, j as int).filter(|x: bool| x).len() as int, a@[(i - 1) as int]);
                slice_multiset_lemma(a@, 0, i as int);
                slice_multiset_lemma(a@, j as int, len as int);
            }
        }
    }
    
    proof {
        reordering_lemma(old_seq, a@);
        assert(a@.to_multiset() == old_seq.to_multiset());
        assert(forall|i: int, j: int| 0 <= i < j < a.len() as int ==> !a@[i] || a@[j]);
    }
}
// </vc-code>

fn main() {}
}