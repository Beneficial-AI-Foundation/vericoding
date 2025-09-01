use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
// No additional helpers needed
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
    // Create hash sets from both vectors
    let mut set0 = HashSetWithView::<u8>::new();
    let mut set1 = HashSetWithView::<u8>::new();
    
    // Add all elements from s0 to set0
    let mut i: usize = 0;
    while i < s0.len()
        invariant
            0 <= i <= s0.len(),
            forall|j: int| #![auto] 0 <= j < i ==> set0@.contains(s0[j]),
            forall|x: u8| #![auto] set0@.contains(x) ==> exists|j: int| 0 <= j < i && s0[j] == x,
    {
        set0.insert(&s0[i]);
        i = i + 1;
    }
    
    // Add all elements from s1 to set1
    i = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            forall|j: int| #![auto] 0 <= j < i ==> set1@.contains(s1[j]),
            forall|x: u8| #![auto] set1@.contains(x) ==> exists|j: int| 0 <= j < i && s1[j] == x,
    {
        set1.insert(&s1[i]);
        i = i + 1;
    }
    
    // Check if all elements in set0 are in s1
    let all_s0_in_s1 = set0.subset_of(&set1);
    
    // Check if all elements in set1 are in s0
    let all_s1_in_s0 = set1.subset_of(&set0);
    
    // Both conditions must be true for sets to be equal
    let result = all_s0_in_s1 && all_s1_in_s0;
    
    // Prove the postcondition
    proof {
        assert forall|j: int| #![auto] 0 <= j < s0.len() implies set0@.contains(s0[j]) by {
            assert(0 <= j < s0.len());
        }
        assert forall|j: int| #![auto] 0 <= j < s1.len() implies set1@.contains(s1[j]) by {
            assert(0 <= j < s1.len());
        }
        
        if result {
            assert forall|j: int| #![auto] 0 <= j < s0.len() implies s1@.contains(s0[j]) by {
                assert(set0@.contains(s0[j]));
                assert(set1@.contains(s0[j]));
            }
            assert forall|j: int| #![auto] 0 <= j < s1.len() implies s0@.contains(s1[j]) by {
                assert(set1@.contains(s1[j]));
                assert(set0@.contains(s1[j]));
            }
        }
        
        if !result {
            if !all_s0_in_s1 {
                assert(!forall|j: int| #![auto] 0 <= j < s0.len() ==> s1@.contains(s0[j]));
            } else {
                assert(!all_s1_in_s0);
                assert(!forall|j: int| #![auto] 0 <= j < s1.len() ==> s0@.contains(s1[j]));
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}