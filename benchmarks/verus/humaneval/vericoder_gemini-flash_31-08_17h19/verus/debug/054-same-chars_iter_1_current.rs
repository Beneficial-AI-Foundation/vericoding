use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
#[verifier::spec]
fn set_from_vec(s: &Vec<u8>) -> (res: Set<u8>) {
    Set::new(|c: u8| s@.contains(c))
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
    let s0_set = set_from_vec(s0);
    let s1_set = set_from_vec(s1);

    let same_chars_local = s0_set.ext_eq(s1_set);

    if same_chars_local {
        assert forall|i: int| 0 <= i < s0.len() implies s1@.contains(s0[i]) by {
            s0_set.contains(s0[i]);
            assert(s0_set.ext_eq(s1_set));
            s1_set.contains(s0[i]);
        }
        assert forall|i: int| 0 <= i < s1.len() implies s0@.contains(s1[i]) by {
            s1_set.contains(s1[i]);
            assert(s0_set.ext_eq(s1_set));
            s0_set.contains(s1[i]);
        }
        same_chars_local
    } else {
        assert(!(s0_set.ext_eq(s1_set))); // This is true by assumption.
        assert(!same_chars_local);

        let mut diff_char_opt: Option<u8> = None;

        if exists|c: u8| s0_set.contains(c) && !s1_set.contains(c) {
            let diff_c_s0 = choose|c: u8| s0_set.contains(c) && !s1_set.contains(c);
            diff_char_opt = Some(diff_c_s0);
            assert forall|i: int| #![auto] 0 <= i < s0.len() && (s0@.contains(s0[i])) implies (s0_set.contains(s0[i])) by {};
            assert forall|i: int| #![auto] 0 <= i < s0.len() && s0[i] == diff_c_s0 implies (s0_set.contains(diff_c_s0)) by {};
            assert forall|i: int| #![auto] 0 <= i < s0.len() && (s0[i] == diff_c_s0) implies !s1@.contains(s0[i]) by {
                assert(!s1_set.contains(diff_c_s0));
                assert forall|x: u8| s1@.contains(x) implies s1_set.contains(x) by {};
                assert(s0[i] == diff_c_s0);
                if (s1@.contains(s0[i])) {
                    assert(s1_set.contains(s0[i]));
                    assert(s1_set.contains(diff_c_s0));
                } else {
                   assert(!s1_set.contains(diff_c_s0));
                }
            }
            return false;
        }

        if exists|c: u8| s1_set.contains(c) && !s0_set.contains(c) {
            let diff_c_s1 = choose|c: u8| s1_set.contains(c) && !s0_set.contains(c);
            diff_char_opt = Some(diff_c_s1);
            assert forall|i: int| #![auto] 0 <= i < s1.len() && (s1@.contains(s1[i])) implies (s1_set.contains(s1[i])) by {};
            assert forall|i: int| #![auto] 0 <= i < s1.len() && s1[i] == diff_c_s1 implies (s1_set.contains(diff_c_s1)) by {};
            assert forall|i: int| #![auto] 0 <= i < s1.len() && (s1[i] == diff_c_s1) implies !s0@.contains(s1[i]) by {
                assert(!s0_set.contains(diff_c_s1));
                assert forall|x: u8| s0@.contains(x) implies s0_set.contains(x) by {};
                assert(s1[i] == diff_c_s1);
                if (s0@.contains(s1[i])) {
                    assert(s0_set.contains(s1[i]));
                    assert(s0_set.contains(diff_c_s1));
                } else {
                   assert(!s0_set.contains(diff_c_s1));
                }
            }
            return false;
        }

        if diff_char_opt.is_none() {
            // If no differentiating character was found, then the sets must be equal.
            // This case should ideally not be reached if same_chars_local is false.
            // We can prove this by contradiction.
            assert(false); // Should not reach here based on the if conditions.
        }
        false
    }
}
// </vc-code>

fn main() {}
}