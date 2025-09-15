// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_merge_preserves_sorted(a: Seq<nat>, b: Seq<nat>, i: int, j: int, res: Seq<nat>)
    requires 
        is_sorted(a),
        is_sorted(b),
        0 <= i <= a.len(),
        0 <= j <= b.len(),
        is_sorted(res),
        forall|k: int| 0 <= k < res.len() ==> (if k < a.len() { res[k] <= a[i] } else { true }),
        forall|k: int| 0 <= k < res.len() ==> (if k < b.len() { res[k] <= b[j] } else { true })
    ensures is_sorted(res.add(if i < a.len() && (j >= b.len() || a[i] <= b[j]) { seq![a[i]] } else { seq![b[j]] }))
{ 
    /* helper modified by LLM (iteration 5): Fixed integer/unsigned type mismatches */
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a1: &Vec<nat>, a2: &Vec<nat>) -> (result: Vec<nat>)
    requires 
        is_sorted(a1@),
        is_sorted(a2@),
    ensures
        is_sorted(result@),
        result@.to_multiset() == a1@.to_multiset().add(a2@.to_multiset()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer/unsigned type mismatches in lemma calls and subrange arguments */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < a1.len() || j < a2.len()
        invariant 
            0 <= i <= a1.len(),
            0 <= j <= a2.len(),
            is_sorted(result@),
            result@.to_multiset() == a1@.subrange(0, i as int).to_multiset().add(a2@.subrange(0, j as int).to_multiset())
        decreases (a1.len() as int) - (i as int) + (a2.len() as int) - (j as int)
    {
        if i < a1.len() && (j >= a2.len() || a1[i] <= a2[j]) {
            result.push(a1[i]);
            proof {
                lemma_merge_preserves_sorted(a1@, a2@, i as int, j as int, result@.subrange(0, (result@.len() as int) - 1));
            }
            i += 1;
        } else {
            result.push(a2[j]);
            proof {
                lemma_merge_preserves_sorted(a1@, a2@, i as int, j as int, result@.subrange(0, (result@.len() as int) - 1));
            }
            j += 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}