use vstd::prelude::*;

verus! {

// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

// <vc-helpers>
spec fn is_permutation(s1: Seq<int>, s2: Seq<int>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}

proof fn lemma_insert_preserves_multiset(s: Seq<int>, idx: int, val: int)
    requires
        0 <= idx <= s.len(),
    ensures
        s.insert(idx, val).to_multiset() == s.to_multiset().insert(val),
{
}

proof fn lemma_insert_at_preserves_order(s: Seq<int>, idx: int, val: int)
    requires
        0 <= idx <= s.len(),
        is_sorted(s),
        (forall|i: int| 0 <= i < idx ==> s[i] <= val),
        (forall|i: int| idx <= i < s.len() ==> val <= s[i]),
    ensures
        is_sorted(s.insert(idx, val)),
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn insertion_sort(s: Seq<int>) -> (r: Seq<int>)
    ensures
        s.to_multiset() == r.to_multiset(),
        is_sorted(r),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn insertion_sort(mut s: Vec<int>) -> (r: Vec<int>)
    ensures
        s@.to_multiset() == r@.to_multiset(),
        is_sorted(r@),
{
    let mut i: usize = 1;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_sorted(s@.subrange(0, i as int)),
            s@.to_multiset() == old(s)@.to_multiset(),
    {
        let mut j: usize = i;
        let val = s[i];
        while j > 0 && s[j - 1] > val
            invariant
                0 <= j <= i,
                i < s.len(),
                s@.to_multiset() == old(s)@.to_multiset(),
                forall |k: int| j <= k < i as int ==> s@[k] >= val,
        {
            s.set(j, s[j - 1]);
            j = j - 1;
        }
        s.set(j, val);
        i = i + 1;
    }
    s
}
// </vc-code>

fn main() {}

}