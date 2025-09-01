use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>

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
    // impl-start
    let mut result = Vec::new();
    let mut s_copy = s.clone();
    s_copy.sort_unstable();

    let mut i = 0;
    while i < s_copy.len()
        invariant
            0 <= i && i <= s_copy.len(),
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] < result[k],
            forall|x: int| 0 <= x < result.len() ==> s_copy@.contains(result[x]),
            forall|x: int| 0 <= x < i ==> ({
                let found_in_result = result@.contains(s_copy[x]);
                let is_duplicate = (x > 0 && s_copy[x] == s_copy[x - 1]);
                found_in_result || is_duplicate
            }),
            result@.len() <= i,
            result@.len() <= s_copy.len(),
    {
        let current_val = s_copy[i];
        if result.is_empty() {
            result.push(current_val);
        } else {
            let last_val = result[result.len() - 1];
            if current_val != last_val {
                result.push(current_val);
            }
        }
        i = i + 1;
    }

    result
    // impl-end
}
// </vc-code>

fn main() {}
}