use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
#[verus::trusted]
fn sort_seq(s: Vec<i32>) -> Vec<i32> {
    let mut result = s;
    result.sort();
    result
}
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
    let sorted_vec = sort_seq(s.clone());
    let mut result = Vec::new();
    if sorted_vec.len() > 0 {
        result.push(sorted_vec[0]);
    }
    for i in 1..sorted_vec.len() {
        if sorted_vec[i] != sorted_vec[i-1] {
            assert!(result[result.len()-1] < sorted_vec[i]);
            result.push(sorted_vec[i]);
        }
    }
    result
}
// </vc-code>

fn main() {}
}