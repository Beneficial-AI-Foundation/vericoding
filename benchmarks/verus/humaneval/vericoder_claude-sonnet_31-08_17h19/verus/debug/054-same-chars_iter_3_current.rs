use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
proof fn lemma_hash_set_contains_equiv_seq_contains(s: Seq<u8>, hs: HashSetWithView<u8>, v: u8)
    requires
        forall|x: u8| s.contains(x) <==> hs@.contains(x),
    ensures
        s.contains(v) <==> hs@.contains(v),
{
}

proof fn lemma_forall_in_hash_set_means_forall_in_seq(s0: Seq<u8>, s1: Seq<u8>, hs1: HashSetWithView<u8>)
    requires
        forall|x: u8| s1.contains(x) <==> hs1@.contains(x),
    ensures
        (forall|i: int| #![auto] 0 <= i < s0.len() ==> hs1@.contains(s0[i])) <==>
        (forall|i: int| #![auto] 0 <= i < s0.len() ==> s1.contains(s0[i])),
{
    assert forall|i: int| #![auto] 0 <= i < s0.len() implies
        (hs1@.contains(s0[i]) <==> s1.contains(s0[i])) by {
        lemma_hash_set_contains_equiv_seq_contains(s1, hs1, s0[i]);
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
    broadcast use axiom_u8_obeys_hash_table_key_model;
    
    let mut set0 = HashSetWithView::<u8>::new();
    let mut set1 = HashSetWithView::<u8>::new();
    
    let mut i = 0;
    while i < s0.len()
        invariant
            0 <= i <= s0.len(),
            forall|j: int| #![auto] 0 <= j < i ==> set0@.contains(s0[j]),
            forall|x: u8| set0@.contains(x) ==> s0@.contains(x),
    {
        set0.insert(s0[i]);
        i += 1;
    }
    
    i = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            forall|j: int| #![auto] 0 <= j < i ==> set1@.contains(s1[j]),
            forall|x: u8| set1@.contains(x) ==> s1@.contains(x),
            forall|x: u8| s0@.contains(x) <==> set0@.contains(x),
    {
        set1.insert(s1[i]);
        i += 1;
    }
    
    assert forall|x: u8| s0@.contains(x) <==> set0@.contains(x) by {};
    assert forall|x: u8| s1@.contains(x) <==> set1@.contains(x) by {};
    
    if set0.len() != set1.len() {
        proof {
            lemma_forall_in_hash_set_means_forall_in_seq(s0@, s1@, set1);
            lemma_forall_in_hash_set_means_forall_in_seq(s1@, s0@, set0);
        }
        return false;
    }
    
    i = 0;
    while i < s0.len()
        invariant
            0 <= i <= s0.len(),
            forall|j: int| #![auto] 0 <= j < i ==> set1@.contains(s0[j]),
            forall|x: u8| s0@.contains(x) <==> set0@.contains(x),
            forall|x: u8| s1@.contains(x) <==> set1@.contains(x),
    {
        if !set1.contains(&s0[i]) {
            proof {
                lemma_forall_in_hash_set_means_forall_in_seq(s0@, s1@, set1);
                lemma_forall_in_hash_set_means_forall_in_seq(s1@, s0@, set0);
            }
            return false;
        }
        i += 1;
    }
    
    i = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            forall|j: int| #![auto] 0 <= j < i ==> set0@.contains(s1[j]),
            forall|k: int| #![auto] 0 <= k < s0.len() ==> set1@.contains(s0[k]),
            forall|x: u8| s0@.contains(x) <==> set0@.contains(x),
            forall|x: u8| s1@.contains(x) <==> set1@.contains(x),
    {
        if !set0.contains(&s1[i]) {
            proof {
                lemma_forall_in_hash_set_means_forall_in_seq(s0@, s1@, set1);
                lemma_forall_in_hash_set_means_forall_in_seq(s1@, s0@, set0);
            }
            return false;
        }
        i += 1;
    }
    
    proof {
        lemma_forall_in_hash_set_means_forall_in_seq(s0@, s1@, set1);
        lemma_forall_in_hash_set_means_forall_in_seq(s1@, s0@, set0);
    }
    
    true
}
// </vc-code>

fn main() {}
}