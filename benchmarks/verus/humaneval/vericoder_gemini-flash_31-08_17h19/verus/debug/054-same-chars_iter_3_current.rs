use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
use vstd::prelude::*;
#[verifier::spec]
fn set_from_vec(s: &Vec<u8>) -> (res: Set<u8>) {
    Set::new(|c: u8| {
        s@.contains(c)
    })
}

#[verifier::proof]
fn lemma_vec_to_set_eq(s0: &Vec<u8>, s1: &Vec<u8>)
    ensures
        set_from_vec(s0).ext_equal(set_from_vec(s1)) <==>
        (forall|c: u8| set_from_vec(s0).contains(c) <==> set_from_vec(s1).contains(c))
{
    // This lemma is just to make the ext_equal verification-friendly.
    // The definition of ext_equal already states this, but Verus might not always pick it up.
    assert(set_from_vec(s0).ext_equal(set_from_vec(s1)) <==>
           (forall|c| set_from_vec(s0).contains(c) <==> set_from_vec(s1).contains(c)));
}

#[verifier::proof]
fn lemma_char_in_vec_implies_in_set(s: &Vec<u8>, c: u8)
    requires s@.contains(c)
    ensures set_from_vec(s).contains(c)
{
    assert(set_from_vec(s).contains(c)) by {
        assert exists|i: int| 0 <= i < s.len() && s@[i] == c;
    }
}

#[verifier::proof]
fn lemma_char_in_set_implies_in_vec(s: &Vec<u8>, c: u8)
    requires set_from_vec(s).contains(c)
    ensures s@.contains(c)
{
    assert(s@.contains(c)) by {
        assert(Set::new(|x: u8| s@.contains(x)).contains(c));
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
    let s0_set = set_from_vec(s0);
    let s1_set = set_from_vec(s1);

    let same_chars_local = s0_set.ext_equal(s1_set);

    if same_chars_local {
        assert forall|i: int| 0 <= i < s0.len() implies s1@.contains(s0[i]) by {
            lemma_char_in_vec_implies_in_set(s0, s0[i]);
            assert(s0_set.contains(s0[i]));
            lemma_vec_to_set_eq(s0, s1);
            assert(s0_set.ext_equal(s1_set)); // This is true by assumption 'same_chars_local'.
            assert(s1_set.contains(s0[i])); // Follows from ext_equal and s0_set contains.
            lemma_char_in_set_implies_in_vec(s1, s0[i]);
        }
        assert forall|i: int| 0 <= i < s1.len() implies s0@.contains(s1[i]) by {
            lemma_char_in_vec_implies_in_set(s1, s1[i]);
            assert(s1_set.contains(s1[i]));
            lemma_vec_to_set_eq(s0, s1);
            assert(s0_set.ext_equal(s1_set)); // This is true by assumption 'same_chars_local'.
            assert(s0_set.contains(s1[i])); // Follows from ext_equal and s1_set contains.
            lemma_char_in_set_implies_in_vec(s0, s1[i]);
        }
        same_chars_local
    } else {
        assert(!(s0_set.ext_equal(s1_set))); // This is true by assumption.
        assert(!same_chars_local);

        let mut diff_char_found = false;

        if exists|c: u8| s0_set.contains(c) && !s1_set.contains(c) {
            let diff_c_s0 = choose|c: u8| s0_set.contains(c) && !s1_set.contains(c);
            diff_char_found = true;

            assert forall|i: int| #![auto] 0 <= i < s0.len() && (s0@.contains(s0[i])) implies (s0_set.contains(s0[i])) by {
                lemma_char_in_vec_implies_in_set(s0, s0[i]);
            };

            assert forall|idx: int| 0 <= idx < s0.len() && s0[idx] == diff_c_s0 implies !s1@.contains(s0[idx]) by {
                lemma_char_in_set_implies_in_vec(s0, diff_c_s0); // To prove diff_c_s0 is in s0@
                assert(s0@.contains(diff_c_s0));
                assert(s0_set.contains(diff_c_s0));
                assert(!s1_set.contains(diff_c_s0));
                if (s1@.contains(s0[idx])) {
                    lemma_char_in_vec_implies_in_set(s1, s0[idx]);
                    assert(s1_set.contains(s0[idx]));
                    assert(s0[idx] == diff_c_s0);
                    assert(s1_set.contains(diff_c_s0));
                } else {
                    assert(!s1@.contains(s0[idx]));
                }
            };
            return false;
        }

        if exists|c: u8| s1_set.contains(c) && !s0_set.contains(c) {
            let diff_c_s1 = choose|c: u8| s1_set.contains(c) && !s0_set.contains(c);
            diff_char_found = true;

            assert forall|i: int| #![auto] 0 <= i < s1.len() && (s1@.contains(s1[i])) implies (s1_set.contains(s1[i])) by {
                 lemma_char_in_vec_implies_in_set(s1, s1[i]);
            };

            assert forall|idx: int| 0 <= idx < s1.len() && s1[idx] == diff_c_s1 implies !s0@.contains(s1[idx]) by {
                lemma_char_in_set_implies_in_vec(s1, diff_c_s1); // To prove diff_c_s1 is in s1@
                assert(s1@.contains(diff_c_s1));
                assert(s1_set.contains(diff_c_s1));
                assert(!s0_set.contains(diff_c_s1));
                if (s0@.contains(s1[idx])) {
                    lemma_char_in_vec_implies_in_set(s0, s1[idx]);
                    assert(s0_set.contains(s1[idx]));
                    assert(s1[idx] == diff_c_s1);
                    assert(s0_set.contains(diff_c_s1));
                } else {
                    assert(!s0@.contains(s1[idx]));
                }
            };
            return false;
        }
        
        // This case should not be reached if same_chars_local is false.
        // If diff_char_found is still false, it means no character was found that exists in one set but not the other.
        // This implies that for all characters 'c', (s0_set.contains(c) <==> s1_set.contains(c)).
        // By the definition of Set.ext_equal, this means s0_set.ext_equal(s1_set) is true.
        // But we are in the 'else' branch where same_chars_local is false, which means s0_set.ext_equal(s1_set) is false.
        // This is a contradiction.
        assert(false);
        false
    }
}
// </vc-code>

fn main() {}
}