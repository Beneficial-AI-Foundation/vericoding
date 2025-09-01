use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
// Helper to prove equivalence between set equality and sequence condition
#[verifier::spec]
proof fn set_equality_eq_condition(s0: &Vec<u8>, s1: &Vec<u8>)
    ensures
        (Set::from_iter(s0.into_iter()) == Set::from_iter(s1.into_iter())) <==> 
        (forall|i: int| 0 <= i < s0.len() implies s1@.contains(s0[i])) &&
        (forall|i: int| 0 <= i < s1.len() implies s0@.contains(s1[i]))
{
    // Prove set equality implies both conditions
    let set0 = Set::from_iter(s0.into_iter());
    let set1 = Set::from_iter(s1.into_iter());
    if set0 == set1 {
        // Condition 1: for all elements in s0, they appear in set1
        for i in 0..s0.len() {
            assert(s0[i] in set0);
            assert(s0[i] in set1);
        }
        // Condition 2: for all elements in s1, they appear in set0
        for i in 0..s1.len() {
            assert(s1[i] in set1);
            assert(s1[i] in set0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn same_chars(s0: &Vec<u8>, s1: &Vec<u8>) -> (same: bool)
    // post-conditions-start
    ensures
        same <==> (forall|i: int| #![auto] 0 <= i < s0.len() ==> s1@.contains(s0[i])) && (forall|
            i: int,
        |
            #![auto]
            0 <= i < s1.len() ==> s0@.contains(s1[i])),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let set0 = Set::from_iter(s0.into_iter());
    let set1 = Set::from_iter(s1.into_iter());
    set0 == set1
}
// </vc-code>

fn main() {}
}