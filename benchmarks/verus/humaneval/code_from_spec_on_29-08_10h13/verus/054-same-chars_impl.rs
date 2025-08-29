use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
spec fn vec_to_set(v: Seq<u8>) -> Set<u8>
    decreases v.len()
{
    if v.len() == 0 {
        Set::empty()
    } else {
        vec_to_set(v.drop_last()).insert(v.last())
    }
}

proof fn vec_to_set_contains(v: Seq<u8>, x: u8)
    ensures vec_to_set(v).contains(x) <==> v.contains(x)
    decreases v.len()
{
    if v.len() == 0 {
    } else {
        vec_to_set_contains(v.drop_last(), x);
        if x == v.last() {
        } else {
        }
    }
}

proof fn hashset_equiv_lemma(s0: Seq<u8>, s1: Seq<u8>)
    ensures (vec_to_set(s0) =~= vec_to_set(s1)) <==> 
            ((forall|i: int| #![auto] 0 <= i < s0.len() ==> s1.contains(s0[i])) && 
             (forall|i: int| #![auto] 0 <= i < s1.len() ==> s0.contains(s1[i])))
{
    assert forall|x: u8| vec_to_set(s0).contains(x) <==> s0.contains(x) by {
        vec_to_set_contains(s0, x);
    }
    assert forall|x: u8| vec_to_set(s1).contains(x) <==> s1.contains(x) by {
        vec_to_set_contains(s1, x);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def same_chars(s0: string, s1: string) -> Bool"
docstring: Check if two words have the same characters.
test_cases:
- input: ['eabcdzzzz', 'dddzzzzzzzddeddabc']
expected_output: True
- input: ['eabcd', 'dddddddabc']
expected_output: False
*/
// </vc-description>

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
    let mut set0 = HashSetWithView::<u8>::new();
    let mut i = 0;
    
    while i < s0.len()
        invariant 
            0 <= i <= s0.len(),
            forall|j: int| 0 <= j < i ==> set0.view().contains(s0[j]),
            forall|x: u8| set0.view().contains(x) ==> s0@.subrange(0, i as int).contains(x)
    {
        set0.insert(s0[i]);
        i = i + 1;
    }
    
    let mut set1 = HashSetWithView::<u8>::new();
    i = 0;
    
    while i < s1.len()
        invariant 
            0 <= i <= s1.len(),
            forall|j: int| 0 <= j < i ==> set1.view().contains(s1[j]),
            forall|x: u8| set1.view().contains(x) ==> s1@.subrange(0, i as int).contains(x)
    {
        set1.insert(s1[i]);
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 5): use exec mode for set comparison */
    proof {
        assert(s0@ =~= s0@.subrange(0, s0.len() as int));
        assert(s1@ =~= s1@.subrange(0, s1.len() as int));
        
        assert forall|j: int| 0 <= j < s0.len() implies set0.view().contains(s0[j]) by {}
        assert forall|x: u8| set0.view().contains(x) implies s0@.contains(x) by {}
        
        assert forall|j: int| 0 <= j < s1.len() implies set1.view().contains(s1[j]) by {}
        assert forall|x: u8| set1.view().contains(x) implies s1@.contains(x) by {}
        
        hashset_equiv_lemma(s0@, s1@);
    }
    
    let result = set0.ext_equal(&set1);
    result
}
// </vc-code>

}
fn main() {}