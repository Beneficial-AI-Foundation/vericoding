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
/* helper modified by LLM (iteration 5): seq prefix helper to avoid slicing parsing issues */
spec fn prefix(s: Seq<i32>, n: int) -> Seq<i32> {
    s[..n]
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
    /* code modified by LLM (iteration 5): merge implementation using usize indices and ghost invariants */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a.len() || j < b.len()
        invariant
            0 <= i as int, i as int <= a.len() as int,
            0 <= j as int, j as int <= b.len() as int,
            is_sorted(res@),
            multiset_equiv(res@, prefix(a@, i as int) + prefix(b@, j as int)),
        decreases (a.len() + b.len() - i - j)
    {
        if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
            res.push(a[i]);
            i += 1;
        } else {
            res.push(b[j]);
            j += 1;
        }
    }
    res
}
// </vc-code>

}
fn main() {}