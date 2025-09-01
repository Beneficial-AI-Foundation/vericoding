use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;
use vstd::seq_lib::lemma_seq_contains_after_push;

verus! {

// <vc-helpers>
fn find_min_index_and_value(v: &Vec<i32>) -> (index: int, value: i32)
    requires
        v.len() > 0
    ensures
        0 <= index < v.len(),
        value == v@[index],
        forall|i: int| 0 <= i < v.len() ==> v@[index] <= v@[i
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
fn find_min_index_and_value(v: &Vec<i32>) -> (index: int, value: i32)
    requires
        v.len() > 0
    ensures
        0 <= index < v.len(),
        value == v@[index],
        forall|i: int| 0 <= i < v.len() ==> v@[index] <= v@[i
// </vc-code>

fn main() {}
}