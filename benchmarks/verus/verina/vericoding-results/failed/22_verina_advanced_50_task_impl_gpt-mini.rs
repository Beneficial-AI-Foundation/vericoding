// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide min for nat */
spec fn min_nat(a: nat, b: nat) -> nat { if a <= b { a } else { b } }
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
    /* code modified by LLM (iteration 5): standard merge loop with explicit invariants */
    let mut i: nat = 0;
    let mut j: nat = 0;
    let mut result: Vec<nat> = Vec::new();

    while (i < a1.len()) || (j < a2.len())
        invariant i <= a1.len();
        invariant j <= a2.len();
        invariant result@.to_multiset() == a1@[0..i].to_multiset().add(a2@[0..j].to_multiset());
        invariant is_sorted(result@);
        decreases a1.len() + a2.len() - (i + j);
    {
        if i < a1.len() && j < a2.len() {
            if a1@[i] <= a2@[j] {
                result.push(a1[i]);
                i = i + 1;
            } else {
                result.push(a2[j]);
                j = j + 1;
            }
        } else if i < a1.len() {
            result.push(a1[i]);
            i = i + 1;
        } else {
            result.push(a2[j]);
            j = j + 1;
        }
    }

    result
}
// </vc-code>

}
fn main() {}