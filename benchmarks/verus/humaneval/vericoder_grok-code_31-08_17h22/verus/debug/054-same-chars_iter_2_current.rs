use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>

pub open spec fn same_chars_spec(s0: Seq<u8>, s1: Seq<u8>) -> bool {
    (forall |i: int| #![trigger] 0 <= i < s0.len() ==> s1.contains(s0[i])) &&
    (forall |i: int| #![trigger] 0 <= i < s1.len() ==> s0.contains(s1[i]))
}

// </vc-helpers>

// <vc-spec>
// </vc-spec>

// <vc-code>
// </vc-code>

// POSTAMBLE remains unchanged

fn main() {}
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
    let mut same: bool = true;
    for i in 0..s0.len() {
        let c = s0[i];
        if !s1.contains(&c) {
            same = false;
            break; // optional: early exit
        }
    }
    if same {
        for i in 0..s1.len() {
            let c = s1[i];
            if !s0.contains(&c) {
                same = false;
                break;
            }
        }
    }
    same
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}