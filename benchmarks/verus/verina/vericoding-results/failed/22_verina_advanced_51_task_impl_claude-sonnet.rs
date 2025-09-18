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
/* helper modified by LLM (iteration 5): fixed lemma proofs with correct multiset operations */
proof fn lemma_sorted_concat_helper(a: Seq<i32>, b: Seq<i32>, i: int, j: int)
    requires
        is_sorted(a),
        is_sorted(b),
        0 <= i < a.len(),
        0 <= j < b.len(),
        a[i] <= b[j],
    ensures
        forall|k: int| 0 <= k < i ==> a[k] <= b[j],
    decreases i,
{
    if i > 0 {
        assert(a[i-1] <= a[i]);
        lemma_sorted_concat_helper(a, b, i-1, j);
    }
}

proof fn lemma_multiset_merge(a: Seq<i32>, b: Seq<i32>, result: Seq<i32>, ai: int, bi: int)
    requires
        0 <= ai <= a.len(),
        0 <= bi <= b.len(),
        result == a.subrange(0, ai) + b.subrange(0, bi),
    ensures
        result.to_multiset() == a.subrange(0, ai).to_multiset().add(b.subrange(0, bi).to_multiset()),
{
    assert(result.to_multiset() == (a.subrange(0, ai) + b.subrange(0, bi)).to_multiset());
    vstd::seq::lemma_multiset_commutative(a.subrange(0, ai), b.subrange(0, bi));
}

proof fn lemma_subrange_multiset(s: Seq<i32>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.subrange(0, i+1).to_multiset() == s.subrange(0, i).to_multiset().insert(s[i]),
{
    let s1 = s.subrange(0, i);
    let s2 = s.subrange(i, i+1);
    assert(s.subrange(0, i+1) == s1 + s2);
    assert(s2 == seq![s[i]]);
    vstd::seq::lemma_multiset_commutative(s1, s2);
}

proof fn lemma_multiset_distributive(a: Seq<i32>, b: Seq<i32>)
    ensures
        a.to_multiset().add(b.to_multiset()) == (a + b).to_multiset(),
{
    vstd::seq::lemma_multiset_commutative(a, b);
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
{
    /* code modified by LLM (iteration 5): fixed invariants and added necessary lemma calls */
    let mut result = Vec::new();
    let mut ai = 0;
    let mut bi = 0;
    
    while ai < a.len() || bi < b.len()
        invariant
            0 <= ai <= a.len(),
            0 <= bi <= b.len(),
            is_sorted(result@),
            result@ == a@.subrange(0, ai as int) + b@.subrange(0, bi as int),
            forall|k: int| 0 <= k < result@.len() ==> (
                (ai < a.len() ==> result@[k] <= a@[ai as int]) &&
                (bi < b.len() ==> result@[k] <= b@[bi as int])
            ),
        decreases (a.len() - ai) + (b.len() - bi),
    {
        if ai >= a.len() {
            result.push(b[bi]);
            bi += 1;
            proof {
                lemma_subrange_multiset(b@, (bi-1) as int);
            }
        } else if bi >= b.len() {
            result.push(a[ai]);
            ai += 1;
            proof {
                lemma_subrange_multiset(a@, (ai-1) as int);
            }
        } else if a[ai] <= b[bi] {
            result.push(a[ai]);
            ai += 1;
            proof {
                lemma_subrange_multiset(a@, (ai-1) as int);
            }
        } else {
            result.push(b[bi]);
            bi += 1;
            proof {
                lemma_subrange_multiset(b@, (bi-1) as int);
            }
        }
    }
    
    proof {
        assert(ai == a.len() && bi == b.len());
        assert(a@.subrange(0, ai as int) == a@);
        assert(b@.subrange(0, bi as int) == b@);
        assert(result@ == a@ + b@);
        lemma_multiset_distributive(a@, b@);
    }
    
    result
}
// </vc-code>

}
fn main() {}