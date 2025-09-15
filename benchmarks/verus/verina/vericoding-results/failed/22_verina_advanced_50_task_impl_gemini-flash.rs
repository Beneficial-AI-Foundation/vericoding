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
/* code modified by LLM (iteration 5): Removed unnecessary explicit casts to `int` for comparisons with `len()`, as `nat` can be directly compared with `usize` (which `len()` returns). */
{
    let mut result: Vec<nat> = Vec::new();
    let mut i: nat = 0nat;
    let mut j: nat = 0nat;

    while i < a1.len() || j < a2.len()
        invariant 
            0 <= i <= a1.len(),
            0 <= j <= a2.len(),
            is_sorted(result@),
            result@.len() == (i as int) + (j as int),
        decreases (a1.len() - i) + (a2.len() - j) 
    {
        if i < a1.len() && (j == a2.len() || a1.view().index(i) <= a2.view().index(j)) {
            result.push(a1.view().index(i));
            i = i + 1nat;
        } else if j < a2.len() && (i == a1.len() || a2.view().index(j) < a1.view().index(i)) {
            result.push(a2.view().index(j));
            j = j + 1nat;
        }
    }
    result
}
// </vc-code>

}
fn main() {}