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
    /* code modified by LLM (iteration 5): Fixed trigger syntax for quantifiers */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < a.len() || j < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= j <= b.len(),
            is_sorted(result@),
            is_sorted(a@),
            is_sorted(b@),
            forall|k: int| 0 <= k < result.len() ==> (
                (exists|ai: int| 0 <= ai < i && result@[k] == a@[ai]) ||
                (exists|bi: int| 0 <= bi < j && result@[k] == b@[bi])
            ),
            result@.to_multiset() =~= a@.take(i as int).to_multiset().add(b@.take(j as int).to_multiset()),
            forall|k: int| 0 <= k < result.len() - 1 ==> result@[k] <= result@[k + 1],
            result.len() == i + j,
            forall|ai: int, bi: int| i <= ai < a.len() && j <= bi < b.len() ==> (
                forall|k: int| 0 <= k < result.len() ==> (result@[k] <= a@[ai] && result@[k] <= b@[bi])
            ),
        decreases a.len() + b.len() - i - j
    {
        if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
            result.push(a[i]);
            i = i + 1;
        } else {
            result.push(b[j]);
            j = j + 1;
        }
    }
    
    proof {
        assert(i == a.len());
        assert(j == b.len());
        assert(a@.take(a.len() as int) =~= a@);
        assert(b@.take(b.len() as int) =~= b@);
        assert(result@.to_multiset() =~= a@.to_multiset().add(b@.to_multiset()));
        assert((a@ + b@).to_multiset() =~= a@.to_multiset().add(b@.to_multiset()));
        assert(multiset_equiv(result@, a@ + b@));
    }
    
    result
}
// </vc-code>

}
fn main() {}