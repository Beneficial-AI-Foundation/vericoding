// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [No changes needed for 5th iteration. Sub_seq implementation is correct.] */
spec fn sub_seq(s: Seq<nat>, start: int, end_exclusive: int) -> Seq<nat> {
    s.subrange(start, end_exclusive)
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
/* code modified by LLM (iteration 5): [Fixed compilation errors by explicitly casting `a1.len()` and `a2.len()` to `int` so that there's no mismatch with other `int` variables. Also fixed indexing for `a1@` and `a2@` by making it explicit `a1@.index(i)` and `a2@.index(j)`.] */
{
    let mut result: Vec<nat> = Vec::new();
    let mut i: int = 0;
    let mut j: int = 0;

    while i < a1.len() as int || j < a2.len() as int
        invariant
            0 <= i <= a1.len() as int,
            0 <= j <= a2.len() as int,
            result.len() == i + j,
            is_sorted(result@),
            result@.to_multiset() == sub_seq(a1@, 0, i).to_multiset().add(
                sub_seq(a2@, 0, j).to_multiset()),
        decreases (a1.len() as int - i) + (a2.len() as int - j)
    {
        if i < a1.len() as int && (j >= a2.len() as int || a1@.index(i) <= a2@.index(j)) {
            result.push(a1@.index(i));
            i = i + 1;
        } else if j < a2.len() as int && (i >= a1.len() as int || a2@.index(j) < a1@.index(i)) {
            result.push(a2@.index(j));
            j = j + 1;
        } else {
            // This else branch should ideally be unreachable given the conditions cover all cases
            // until both i and j reach their respective lengths. Verus proves this by exclusion.
            // If both i and j are at their limits, the loop condition (i < a1.len() || j < a2.len()) would be false.
            // So, this branch logically implies an unreachable state within the loop.
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}