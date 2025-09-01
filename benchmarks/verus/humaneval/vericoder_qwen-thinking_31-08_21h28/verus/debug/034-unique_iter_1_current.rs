use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
use vstd::seq::sorted;
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
        forall|i: int| #![auto] 0 <= i < result.len() ==> s@.contains(result[i]),
        forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> result@.contains(s[i]),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let sorted = sorted(s);
    let mut result = Vec::new();
    if sorted.len() > 0 {
        result.push(sorted[0]);
    }
    for i in 1..sorted.len() {
        if sorted[i] != sorted[i-1] {
            assert!(result[result.len()-1] < sorted[i]);
            result.push(sorted[i]);
        }
    }
    result
}
// </vc-code>

fn main() {}
}