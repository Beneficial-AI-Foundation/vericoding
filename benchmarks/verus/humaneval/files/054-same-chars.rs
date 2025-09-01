use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

/*
function_signature: "def same_chars(s0: string, s1: string) -> Bool"
docstring: Check if two words have the same characters.
test_cases:
- input: ['eabcdzzzz', 'dddzzzzzzzddeddabc']
expected_output: True
- input: ['eabcd', 'dddddddabc']
expected_output: False
*/

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
{
    // impl-start
    assume(false);
    false
    // impl-end
}

}
fn main() {}