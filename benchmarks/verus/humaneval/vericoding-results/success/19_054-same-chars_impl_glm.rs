// <vc-preamble>
use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added exec helper to check if element is in vector */
fn contains_in_vec(vec: &Vec<u8>, elem: u8) -> (result: bool)
    ensures
        result <==> vec@.contains(elem),
{
    let mut found = false;
    let mut i = 0;
    while i < vec.len()
        invariant
            0 <= i <= vec.len(),
            found <==> (exists|j: int| 0 <= j < i && vec[j] == elem),
        decreases vec.len() - i
    {
        if vec[i] == elem {
            found = true;
        }
        i += 1;
    }
    found
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn same_chars(s0: &Vec<u8>, s1: &Vec<u8>) -> (same: bool)

    ensures
        same <==> (forall|i: int| #![auto] 0 <= i < s0.len() ==> s1@.contains(s0[i])) && (forall|
            i: int,
        |
            #![auto]
            0 <= i < s1.len() ==> s0@.contains(s1[i])),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): replaced set-based approach with vector scanning using helper */
{
    let mut all_s0_in_s1 = true;
    let mut i = 0;
    while i < s0.len()
        invariant
            0 <= i <= s0.len(),
            all_s0_in_s1 <==> (forall|j: int| 0 <= j < i ==> s1@.contains(s0[j])),
        decreases s0.len() - i
    {
        if !contains_in_vec(s1, s0[i]) {
            all_s0_in_s1 = false;
        }
        i += 1;
    }

    let mut all_s1_in_s0 = true;
    let mut i = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            all_s1_in_s0 <==> (forall|j: int| 0 <= j < i ==> s0@.contains(s1[j])),
        decreases s1.len() - i
    {
        if !contains_in_vec(s0, s1[i]) {
            all_s1_in_s0 = false;
        }
        i += 1;
    }

    all_s0_in_s1 && all_s1_in_s0
}
// </vc-code>

}
fn main() {}