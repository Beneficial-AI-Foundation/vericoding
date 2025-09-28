// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fixed lemma syntax with ! */
fn sorted(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn is_permutation(s1: Seq<i8>, s2: Seq<i8>) -> bool {
    s1.to_multiset() =~= s2.to_multiset()
}

lemma merge_sorted_sequences!(s1: Seq<i8>, s2: Seq<i8>, merged: Seq<i8>)
    requires
        sorted(s1),
        sorted(s2),
        is_permutation(s1 + s2, merged),
        sorted(merged)
    ensures
        merged@.to_multiset() =~= s1@.to_multiset() + s2@.to_multiset()
{
}

spec fn split_seq(s: Seq<i8>, mid: nat) -> (Seq<i8>, Seq<i8>)
    requires
        mid <= s.len()
{
    (s.subrange(0, mid), s.subrange(mid, s.len()))
}

lemma sort_preserves_multiset!(sorted_seq: Seq<i8>, original: Seq<i8>)
    requires
        sorted(sorted_seq),
        sorted_seq@.to_multiset() =~= original@.to_multiset()
    ensures
        is_permutation(sorted_seq, original)
{
}

// </vc-helpers>

// <vc-spec>
fn msort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        result@.to_multiset() =~= a@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Complete merge sort implementation */
    if a.len() <= 1 {
        return a;
    }
    
    let mid = a.len() / 2;
    let left = msort(a.subrange(0, mid));
    let right = msort(a.subrange(mid, a.len()));
    
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < left.len() && j < right.len()
        invariant
            0 <= i <= left.len(),
            0 <= j <= right.len(),
            result.len() == i + j,
            sorted(result@),
            result@.to_multiset() =~= left@.subrange(0, i)@.to_multiset() + right@.subrange(0, j)@.to_multiset()
    {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    
    while i < left.len()
        invariant
            i >= 0,
            i <= left.len(),
            result.len() >= old(result).len(),
            j == right.len(),
            result@.to_multiset() =~= left@.subrange(0, i)@.to_multiset() + right@.to_multiset(),
            sorted(result@)
    {
        result.push(left[i]);
        i += 1;
    }
    
    while j < right.len()
        invariant
            j >= 0,
            j <= right.len(),
            result.len() >= old(result).len(),
            i == left.len(),
            result@.to_multiset() =~= left@.to_multiset() + right@.subrange(0, j)@.to_multiset(),
            sorted(result@)
    {
        result.push(right[j]);
        j += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}