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
proof fn lemma_sorted_merge(a: Seq<i32>, b: Seq<i32>, i: int, j: int, k: int)
    requires
        is_sorted(a),
        is_sorted(b),
        0 <= i <= a.len(),
        0 <= j <= b.len(),
        k == i + j,
    ensures
        forall|l: int, m: int| 0 <= l < m < k ==> (if l < i { a[l] } else { b[l - i] }) <= (if m < i { a[m] } else { b[m - i] })
    decreases i + j
{
    /* helper modified by LLM (iteration 5): Fixed parameter types to use int consistently */
    if i > 0 && j > 0 {
        lemma_sorted_merge(a, b, i - 1, j, k - 1);
    } else if i > 0 {
        lemma_sorted_merge(a, b, i - 1, j, k - 1);
    } else if j > 0 {
        lemma_sorted_merge(a, b, i, j - 1, k - 1);
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
{
    /* code modified by LLM (iteration 5): Convert usize to int for lemma parameters */
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < a.len() || j < b.len()
        invariant
            is_sorted(result@),
            multiset_equiv(result@, a@.subrange(0, i as int) + b@.subrange(0, j as int)),
            i <= a.len(),
            j <= b.len(),
            result.len() == i + j
        decreases (a.len() - i) + (b.len() - j)
    {
        if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
        proof {
            lemma_sorted_merge(a@, b@, i as int, j as int, result.len() as int);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}