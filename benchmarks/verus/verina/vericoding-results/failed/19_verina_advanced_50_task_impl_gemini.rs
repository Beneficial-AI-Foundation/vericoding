// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): an unused helper, kept from previous turn */
spec fn always_true() -> bool {
    true
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
    /* code modified by LLM (iteration 5): added invariants to connect local length variables to actual vector lengths */
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    let a1_len = a1.len();
    let a2_len = a2.len();

    while i < a1_len && j < a2_len
        invariant
            a1_len == a1.len(),
            a2_len == a2.len(),
            0 <= i <= a1_len,
            0 <= j <= a2_len,
            is_sorted(result@),
            result@.to_multiset() == a1@.subrange(0, i as int).to_multiset().add(a2@.subrange(0, j as int).to_multiset()),
            (i < a1_len && result@.len() > 0) ==> result@.last() <= a1[i as int],
            (j < a2_len && result@.len() > 0) ==> result@.last() <= a2[j as int],
        decreases (a1_len - i) + (a2_len - j)
    {
        if a1[i] <= a2[j] {
            result.push(a1[i]);
            i = i + 1;
        } else {
            result.push(a2[j]);
            j = j + 1;
        }
    }

    while i < a1_len
        invariant
            a1_len == a1.len(),
            a2_len == a2.len(),
            0 <= i <= a1_len,
            j == a2_len,
            is_sorted(result@),
            result@.to_multiset() == a1@.subrange(0, i as int).to_multiset().add(a2@.to_multiset()),
            (i < a1_len && result@.len() > 0) ==> result@.last() <= a1[i as int],
        decreases a1_len - i
    {
        result.push(a1[i]);
        i = i + 1;
    }

    while j < a2_len
        invariant
            a1_len == a1.len(),
            a2_len == a2.len(),
            i == a1_len,
            0 <= j <= a2_len,
            is_sorted(result@),
            result@.to_multiset() == a1@.to_multiset().add(a2@.subrange(0, j as int).to_multiset()),
            (j < a2_len && result@.len() > 0) ==> result@.last() <= a2[j as int],
        decreases a2_len - j
    {
        result.push(a2[j]);
        j = j + 1;
    }

    result
}
// </vc-code>

}
fn main() {}