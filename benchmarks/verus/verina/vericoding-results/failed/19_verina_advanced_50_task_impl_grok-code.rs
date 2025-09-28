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
/* code modified by LLM (iteration 5): fixed compilation errors by using direct casts to int instead of ghost declarations */
{
    let mut result = Vec::new();
    let mut i = 0usize;
    let mut j = 0usize;
    while i < a1.len() && j < a2.len()
        invariant
            is_sorted(result@),
            result@.len() == i as int + j as int,
            result@.to_multiset() == a1@[0..i as int].to_multiset().add(a2@[0..j as int].to_multiset())
        decreases (a1@.len() as int - i as int) + (a2@.len() as int - j as int)
    {
        if a1@[i as int] <= a2@[j as int] {
            result.push(a1[i]);
            i = i + 1;
        } else {
            result.push(a2[j]);
            j = j + 1;
        }
    }
    while i < a1.len()
        invariant
            is_sorted(result@),
            result@.len() == i as int + a2.len() as int,
            result@.to_multiset() == a1@[0..i as int].to_multiset().add(a2@.to_multiset())
        decreases a1@.len() as int - i as int
    {
        result.push(a1[i]);
        i = i + 1;
    }
    while j < a2.len()
        invariant
            is_sorted(result@),
            result@.len() == a1.len() as int + j as int,
            result@.to_multiset() == a1@.to_multiset().add(a2@[0..j as int].to_multiset())
        decreases a2@.len() as int - j as int
    {
        result.push(a2[j]);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}