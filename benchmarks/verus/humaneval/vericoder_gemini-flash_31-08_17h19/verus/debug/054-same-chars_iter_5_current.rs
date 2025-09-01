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
        set_from_vec(s0).ext_equivalent(set_from_vec(s1)) <==>
        (forall|c: u8| set_from_vec(s0).contains(c) <==> set_from_vec(s1).contains(c))
{
    // This lemma is just to make the ext_equivalent verification-friendly.
    // The definition of ext_equivalent already states this, but Verus might not always pick it up.
    assert(set_from_vec(s0).ext_equivalent(set_from_vec(s1)) <==>
           (forall|c| set_from_vec(s0).contains(c) <==> set_from_vec(s1).contains(c)));
}

#[verifier::proof]
fn lemma_char_in_vec_implies_in_set(s: &Vec<u8>, c: u8)
    requires s@.contains(c)
    ensures set_from_vec(s).contains(c)
{
    // No specific proof needed here; the definition of set_from_vec directly implies this.
    // The `Set::new` constructor ensures that if `s@.contains(c)` then `set_from_vec(s).contains(c)`
    // because the set is defined as containing all elements `c` for which `s@.contains(c)` is true.
}

#[verifier::proof]
fn lemma_char_in_set_implies_in_vec(s: &Vec<u8>, c: u8)
    requires set_from_vec(s).contains(c)
    ensures s@.contains(c)
{
    // Similar to the above lemma, this is also directly implied by the definition of set_from_vec.
    // If `set_from_vec(s).contains(c)`, then by definition of the set, `s@.contains(c)` must be true.
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

    let same_chars_local = s0_set.ext_equivalent(s1_set);

    if same_chars_local {
        assert forall|i: int| 0 <= i < s0.len() implies s1@.contains(s0[i]) by {
            lemma_char_in_vec_implies_in_set(s0, s0[i]); // This establishes s0_set.contains(s0[i])
            assert(s0_set.contains(s0[i]));
            lemma_vec_to_set_eq(s0, s1); // This is needed to reason about ext_equivalent
            assert(s0_set.ext_equivalent(s1_set)); // This is true by assumption 'same_chars_local'.
            assert(s1_set.contains(s0[i])); // Follows from ext_equivalent and s0_set contains.
            lemma_char_in_set_implies_in_vec(s1, s0[i]); // This establishes s1@.contains(s0[i])
        }
        assert forall|i: int| 0 <= i < s1.len() implies s0@.contains(s1[i]) by {
            lemma_char_in_vec_implies_in_set(s1, s1[i]); // This establishes s1_set.contains(s1[i])
            assert(s1_set.contains(s1[i]));
            lemma_vec_to_set_eq(s0, s1); // This is needed to reason about ext_equivalent
            assert(s0_set.ext_equivalent(s1_set)); // This is true by assumption 'same_chars_local'.
            assert(s0_set.contains(s1[i])); // Follows from ext_equivalent and s1_set contains.
            lemma_char_in_set_implies_in_vec(s0, s1[i]); // This establishes s0@.contains(s1[i])
        }
        same_chars_local
    } else {
        assert(!(s0_set.ext_equivalent(s1_set))); // This is true by assumption.

        let mut diff_char_found = false;

        proof {
            if exists|c: u8| s0_set.contains(c) && !s1_set.contains(c) {
                let diff_c_s0 = choose|c: u8| s0_set.contains(c) && !s1_set.contains(c);
                diff_char_found = true;

                assert forall|i: int| 0 <= i < s0.len() implies (s0[i] != diff_c_s0 || !s1@.contains(s0[i])) by {
                    if s0[i] == diff_c_s0 {
                        assert(s0_set.contains(diff_c_s0));
                        assert(!s1_set.contains(diff_c_s0));
                        if s1@.contains(s0[i]) {
                            lemma_char_in_vec_implies_in_set(s1, s0[i]);
                            assert(s1_set.contains(s0[i]));
                            assert(s1_set.contains(diff_c_s0)); // Contradicts !s1_set.contains(diff_c_s0)
                        }
                    }
                };

                assert(!((forall|i: int| 0 <= i < s0.len() ==> s1@.contains(s0[i]))));
            } else if exists|c: u8| s1_set.contains(c) && !s0_set.contains(c) {
                let diff_c_s1 = choose|c: u8| s1_set.contains(c) && !s0_set.contains(c);
                diff_char_found = true;

                assert forall|i: int| 0 <= i < s1.len() implies (s1[i] != diff_c_s1 || !s0@.contains(s1[i])) by {
                    if s1[i] == diff_c_s1 {
                        assert(s1_set.contains(diff_c_s1));
                        assert(!s0_set.contains(diff_c_s1));
                        if s0@.contains(s1[i]) {
                            lemma_char_in_vec_implies_in_set(s0, s1[i]);
                            assert(s0_set.contains(s1[i]));
                            assert(s0_set.contains(diff_c_s1)); // Contradicts !s0_set.contains(diff_c_s1)
                        }
                    }
                };
                assert(!((forall|i: int| 0 <= i < s1.len() ==> s0@.contains(s1[i]))));
            } else {
                // If diff_char_found is still false, it means no character was found that exists in one set but not the other.
                // This implies that for all characters 'c', (s0_set.contains(c) <==> s1_set.contains(c)).
                // By the definition of Set.ext_equivalent, this means s0_set.ext_equivalent(s1_set) is true.
                // But we are in the 'else' branch where same_chars_local is false, which means s0_set.ext_equivalent(s1_set) is false.
                // This is a contradiction.
                lemma_vec_to_set_eq(s0, s1);
                assert(s0_set.ext_equivalent(s1_set));
                assert(false); // Contradiction: same_chars_local == false and s0_set.ext_equivalent(s1_set) == true
            }
        }
        false
    }
}
// </vc-code>

fn main() {}
}