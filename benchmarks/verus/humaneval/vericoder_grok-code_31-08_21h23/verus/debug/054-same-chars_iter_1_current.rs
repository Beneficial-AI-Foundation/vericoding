use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
use vstd::hash_set::*;

proof fn invoke_hash_axiom() {
    axiom_u8_obeys_hash_table_key_model();
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
    proof { invoke_hash_axiom(); }
    let mut hs0 = HashSetWithView::<u8>::new();
    let mut hs1 = HashSetWithView::<u8>::new();
    let mut i = 0;
    while i < s0.len()
        invariant
            0 <= i <= s0.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] hs0@.contains(s0@[j]),
            forall|e: u8| #[trigger] hs0@.contains(e) ==> exists|j: int| 0 <= j < i && s0@[j] == e,
    {
        hs0.insert(s0[i]);
        proof {
            assert(hs0@.contains(s0@[i]));
        }
        i += 1;
    }
    i = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] hs1@.contains(s1@[j]),
            forall|e: u8| #[trigger] hs1@.contains(e) ==> exists|j: int| 0 <= j < i && s1@[j] == e,
    {
        hs1.insert(s1[i]);
        proof {
            assert(hs1@.contains(s1@[i]));
        }
        i += 1;
    }
    let same = hs0@ == hs1@;
    proof {
        // The equality of sets implies the postcondition quantifiers
        assert(same ==> forall|i: int| 0 <= i < s0.len() ==> #[trigger] hs1@.contains(s0@[i]));
        assert(same ==> forall|i: int| 0 <= i < s1.len() ==> #[trigger] hs0@.contains(s1@[i]));
        assert(!same ==> (exists|i: int| 0 <= i < s0.len() && !hs1@.contains(s0@[i])) || (exists|i: int| 0 <= i < s1.len() && !hs0@.contains(s1@[i])));
    }
    same
}
// </vc-code>

fn main() {}
}