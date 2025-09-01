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
        set0.insert(s0[i]);
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
        set1.insert(s1[i]);
        i = i + 1;
    }
    
    // Check if all elements in s0 are in s1
    let mut all_s0_in_s1 = true;
    i = 0;
    while i < s0.len()
        invariant
            0 <= i <= s0.len(),
            all_s0_in_s1 <==> forall|j: int| #![auto] 0 <= j < i ==> set1@.contains(s0[j]),
    {
        if !set1.contains(&s0[i]) {
            all_s0_in_s1 = false;
        }
        i = i + 1;
    }
    
    // Check if all elements in s1 are in s0
    let mut all_s1_in_s0 = true;
    i = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            all_s1_in_s0 <==> forall|j: int| #![auto] 0 <= j < i ==> set0@.contains(s1[j]),
    {
        if !set0.contains(&s1[i]) {
            all_s1_in_s0 = false;
        }
        i = i + 1;
    }
    
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
            assert(all_s0_in_s1);
            assert(all_s1_in_s0);
            assert forall|j: int| #![auto] 0 <= j < s0.len() implies s1@.contains(s0[j]) by {
                assert(set0@.contains(s0[j]));
                assert(set1@.contains(s0[j]));
                // Since set1 contains all elements from s1, and s0[j] is in set1
                let k = choose|k: int| 0 <= k < s1.len() && s1[k] == s0[j];
                assert(s1@[k] == s0[j]);
            }
            assert forall|j: int| #![auto] 0 <= j < s1.len() implies s0@.contains(s1[j]) by {
                assert(set1@.contains(s1[j]));
                assert(set0@.contains(s1[j]));
                // Since set0 contains all elements from s0, and s1[j] is in set0
                let k = choose|k: int| 0 <= k < s0.len() && s0[k] == s1[j];
                assert(s0@[k] == s1[j]);
            }
        }
        
        if !result {
            if !all_s0_in_s1 {
                // There exists some element in s0 that is not in set1
                let j = choose|j: int| 0 <= j < s0.len() && !set1@.contains(s0[j]);
                assert(!s1@.contains(s0[j]));
            } else {
                assert(!all_s1_in_s0);
                // There exists some element in s1 that is not in set0
                let j = choose|j: int| 0 <= j < s1.len() && !set0@.contains(s1[j]);
                assert(!s0@.contains(s1[j]));
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}