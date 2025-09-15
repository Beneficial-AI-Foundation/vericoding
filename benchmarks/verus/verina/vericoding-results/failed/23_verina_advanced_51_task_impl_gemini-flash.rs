// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn multiset_equiv(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed extraneous proofs from multiset_equiv lemma */
spec fn merge_sorted_spec(a: Seq<i32>, b: Seq<i32>) -> (result: Seq<i32>) {
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else if a[0] <= b[0] {
        Seq::singleton(a[0]).add(merge_sorted_spec(a.skip(1), b))
    } else {
        Seq::singleton(b[0]).add(merge_sorted_spec(a, b.skip(1)))
    }
}

proof fn lemma_merge_sorted_spec_is_sorted(a: Seq<i32>, b: Seq<i32>)
    requires
        is_sorted(a),
        is_sorted(b),
    ensures
        is_sorted(merge_sorted_spec(a, b)),
    decreases a.len(), b.len()
{
    if a.len() == 0 {
        /* handled by base case */
    } else if b.len() == 0 {
        /* handled by base case */
    } else if a[0] <= b[0] {
        lemma_merge_sorted_spec_is_sorted(a.skip(1), b);
    } else {
        lemma_merge_sorted_spec_is_sorted(a, b.skip(1));
    }
}

proof fn lemma_merge_sorted_spec_multiset_equiv(a: Seq<i32>, b: Seq<i32>)
    ensures multiset_equiv(merge_sorted_spec(a, b), a + b),
    decreases a.len(), b.len()
{
    if a.len() == 0 {
        /* handled by base case */
    } else if b.len() == 0 {
        /* handled by base case */
    } else if a[0] <= b[0] {
        lemma_merge_sorted_spec_multiset_equiv(a.skip(1), b);
    } else {
        lemma_merge_sorted_spec_multiset_equiv(a, b.skip(1));
    }
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        is_sorted(a@),
        is_sorted(b@),
    ensures 
        is_sorted(result@),
        multiset_equiv(result@, a@ + b@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed invariant_degenerate_condition */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < a.len() || j < b.len()
        invariant
            result.len() == i + j,
            is_sorted(result@),
            multiset_equiv(result@, (a@.subsequence(0, i) + b@.subsequence(0, j))),
            is_sorted(a@.subsequence(i, a.len())),
            is_sorted(b@.subsequence(j, b.len())),
    {
        if i < a.len() && (j == b.len() || a[i] <= b[j]) {
            result.push(a[i]);
            i = i + 1;
        } else if j < b.len() && (i == a.len() || b[j] < a[i]) {
            result.push(b[j]);
            j = j + 1;
        }
    }
    
    proof {
        lemma_merge_sorted_spec_is_sorted(a@, b@);
        lemma_merge_sorted_spec_multiset_equiv(a@, b@);
    }
    
    result
}
// </vc-code>

}
fn main() {}