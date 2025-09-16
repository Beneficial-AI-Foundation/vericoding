// <vc-preamble>
use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed helper function to properly handle character containment checks with proof support */
fn char_in_vec(c: u8, v: &Vec<u8>) -> (b: bool)
    ensures
        b <==> v@.contains(c),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j] != c,
        decreases
            v.len() - i,
    {
        if v[i] == c {
            return true;
        }
        i = i + 1;
    }
    false
}

proof fn forall_char_in_vec_implies_contains(c: u8, v: &Vec<u8>)
    ensures
        (forall|i: int| 0 <= i < v.len() ==> v@[i] != c) ==> !v@.contains(c),
{
}

proof fn contains_implies_exists_char_in_vec(c: u8, v: &Vec<u8>)
    ensures
        v@.contains(c) ==> (exists|i: int| 0 <= i < v.len() && v@[i] == c),
{
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
{
    /* code modified by LLM (iteration 4): fixed verification by ensuring full character set equivalence */
    let mut i: usize = 0;
    while i < s0.len()
        invariant
            0 <= i <= s0.len(),
            forall|j: int| 0 <= j < i ==> s1@.contains(s0@[j]),
        decreases
            s0.len() - i,
    {
        if !char_in_vec(s0[i], s1) {
            return false;
        }
        i = i + 1;
    }
    
    let mut j: usize = 0;
    while j < s1.len()
        invariant
            0 <= j <= s1.len(),
            forall|k: int| 0 <= k < j ==> s0@.contains(s1@[k]),
        decreases
            s1.len() - j,
    {
        if !char_in_vec(s1[j], s0) {
            return false;
        }
        j = j + 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}