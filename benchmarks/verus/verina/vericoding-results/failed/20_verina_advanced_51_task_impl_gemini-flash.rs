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
/* helper modified by LLM (iteration 5): The `subsequence` method is not available on `vstd::seq::Seq`. Instead, the `subsequence` method is a ghost function on `Seq` */
spec fn sub_seq(s: Seq<i32>, start: int, end: int) -> Seq<i32>
    requires
        0 <= start <= end <= s.len()
{
    s.subsequence(start, end)
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
/* code modified by LLM (iteration 5): Fixed type mismatch for params of `sub_seq`, `to_multiset().add()` instead of `+` operand */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    let mut j = 0;

    while i < a.len() || j < b.len()
        invariant
            result@.len() == (i as int) + (j as int),
            result@.to_multiset() == sub_seq(a@, 0, i as int).to_multiset().add(sub_seq(b@, 0, j as int).to_multiset()),
            is_sorted(result@),
            is_sorted(sub_seq(a@, i as int, a.len() as int)),
            is_sorted(sub_seq(b@, j as int, b.len() as int)),
            i <= a.len(),
            j <= b.len(),
        decreases (a.len() - i) + (b.len() - j)
    {
        if i < a.len() && (j == b.len() || a[i] <= b[j]) {
            result.push(a[i]);
            i += 1;
        } else if j < b.len() && (i == a.len() || b[j] < a[i]) {
            result.push(b[j]);
            j += 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}