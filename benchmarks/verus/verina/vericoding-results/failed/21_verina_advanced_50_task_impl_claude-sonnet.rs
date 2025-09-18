// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed lemma keyword and made proper function signatures */
proof fn lemma_merge_preserves_sorted(a1: Seq<nat>, a2: Seq<nat>, result: Seq<nat>, i1: int, i2: int, k: int)
    requires
        is_sorted(a1),
        is_sorted(a2),
        0 <= i1 <= a1.len(),
        0 <= i2 <= a2.len(),
        k == i1 + i2,
        k <= result.len(),
        forall|idx: int| 0 <= idx < k ==> (idx < result.len()),
    ensures
        forall|idx: int| 0 <= idx < k ==> (idx == 0 || result[idx - 1] <= result[idx]),
{
}

proof fn lemma_multiset_preservation(a1: Seq<nat>, a2: Seq<nat>, result: Seq<nat>, i1: int, i2: int)
    requires
        0 <= i1 <= a1.len(),
        0 <= i2 <= a2.len(),
        result == a1.subrange(0, i1) + a2.subrange(0, i2),
    ensures
        result.to_multiset() == a1.subrange(0, i1).to_multiset().add(a2.subrange(0, i2).to_multiset()),
{
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
    /* code modified by LLM (iteration 5): added decreases clause for while loop */
    let mut result = Vec::new();
    let mut i1: usize = 0;
    let mut i2: usize = 0;
    
    while i1 < a1.len() || i2 < a2.len()
        invariant
            i1 <= a1.len(),
            i2 <= a2.len(),
            is_sorted(result@),
            result@.to_multiset() == a1@.subrange(0, i1 as int).to_multiset().add(a2@.subrange(0, i2 as int).to_multiset()),
        decreases (a1.len() - i1) + (a2.len() - i2)
    {
        if i1 >= a1.len() {
            result.push(a2[i2]);
            i2 += 1;
        } else if i2 >= a2.len() {
            result.push(a1[i1]);
            i1 += 1;
        } else if a1[i1] <= a2[i2] {
            result.push(a1[i1]);
            i1 += 1;
        } else {
            result.push(a2[i2]);
            i2 += 1;
        }
    }
    
    proof {
        assert(i1 == a1.len());
        assert(i2 == a2.len());
        assert(a1@.subrange(0, i1 as int) == a1@);
        assert(a2@.subrange(0, i2 as int) == a2@);
        assert(result@.to_multiset() == a1@.to_multiset().add(a2@.to_multiset()));
    }
    
    result
}
// </vc-code>

}
fn main() {}