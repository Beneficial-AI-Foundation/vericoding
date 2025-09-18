// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Changed loop indices i and j from nat to usize to allow direct Vec indexing a1[i] instead of sequence access a1@[], fixing compilation errors with spec types in exec code; adjusted invariants to cast usize to int for spec conditions */
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a1.len() && j < a2.len()
        invariant
            0 <= i as int <= a1@.len(),
            0 <= j as int <= a2@.len(),
            is_sorted(result@),
            result@.len() == (i as int + j as int),
            result@.to_multiset() == a1@.take(i as int).to_multiset().add(a2@.take(j as int).to_multiset())
    {
        if a1[i] <= a2[j] {
            result.push(a1[i]);
            i = i + 1;
        } else {
            result.push(a2[j]);
            j = j + 1;
        }
    }
    while i < a1.len()
        invariant
            j as int == a2@.len(),
            0 <= i as int <= a1@.len(),
            is_sorted(result@),
            result@.len() == (a2@.len() as int + i as int),
            result@.to_multiset() == a2@.to_multiset().add(a1@.take(i as int).to_multiset())
    {
        result.push(a1[i]);
        i = i + 1;
    }
    while j < a2.len()
        invariant
            i as int == a1@.len(),
            0 <= j as int <= a2@.len(),
            is_sorted(result@),
            result@.len() == (a1@.len() + j as int),
            result@.to_multiset() == a1@.to_multiset().add(a2@.take(j as int).to_multiset())
    {
        result.push(a2[j]);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}