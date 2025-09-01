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
    ensures
        same <==> (forall |i: int| #![trigger] 0 <= i < s0.len() ==> s1@.contains(s0[i])) &&
                 (forall |i: int| #![trigger] 0 <= i < s1.len() ==> s0@.contains(s1[i]))
{
    let mut set0: HashSetWithView<u8> = HashSetWithView::new();
    proof {
        assert(set0@.finite());
    }
    for i in 0..s0.len()
        invariant
            forall |j: int| #![trigger] 0 <= j < i ==> set0@.contains((*s0.as_slice())@[j])
    {
        let c = s0[i];
        set0.insert(c);
        proof {
            axiom_u8_obeys_hash_table_key_model();
        }
    }
    let mut set1: HashSetWithView<u8> = HashSetWithView::new();
    proof {
        assert(set1@.finite());
    }
    for i in 0..s1.len()
        invariant
            forall |j: int| #![trigger] 0 <= j < i ==> set1@.contains((*s1.as_slice())@[j])
    {
        let c = s1[i];
        set1.insert(c);
        proof {
            axiom_u8_obeys_hash_table_key_model();
        }
    }
    proof {
        assert(forall |i: int| #![trigger] 0 <= i < s0.len() ==> set0@.contains(s0@[i]));
        assert(forall |i: int| #![trigger] 0 <= i < s1.len() ==> set1@.contains(s1@[i]));
        assert(set0@ == set1@ <==> 
            (forall |i: int| #![trigger] 0 <= i < s0.len() ==> s1@.contains(s0@[i])) &&
            (forall |i: int| #![trigger] 0 <= i < s1.len() ==> s0@.contains(s1@[i])));
    }
    same = set0@ == set1@;
}
// </vc-code>

fn main() {}
}