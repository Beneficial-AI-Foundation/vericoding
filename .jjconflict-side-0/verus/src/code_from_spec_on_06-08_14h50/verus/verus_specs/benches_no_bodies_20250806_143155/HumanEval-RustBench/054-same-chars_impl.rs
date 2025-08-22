use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

broadcast use axiom_u8_obeys_hash_table_key_model;

fn hash_set_from(s: &Vec<u8>) -> (res: HashSetWithView<u8>)
    // post-conditions-start
    ensures
        forall|i: int| #![auto] 0 <= i < s.len() ==> res@.contains(s[i]),
        forall|x: int|
            0 <= x < 256 ==> #[trigger] res@.contains(x as u8) ==> #[trigger] s@.contains(x as u8),
    // post-conditions-end
{
    let mut res = HashSetWithView::new();
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| #![auto] 0 <= j < i ==> res@.contains(s[j]),
            forall|x: int|
                0 <= x < 256 ==> #[trigger] res@.contains(x as u8) ==> #[trigger] s@.contains(x as u8),
        decreases s.len() - i
    {
        res.insert(s[i]);
        i = i + 1;
    }
    res
}

proof fn implies_contains(s0: Seq<u8>, s1: Seq<u8>, hs1: Set<u8>)
    // pre-conditions-start
    requires
        forall|i: int| #![trigger s0[i]] 0 <= i < s0.len() ==> 0 <= s0[i] < 256,
        forall|x: int|
            0 <= x < 256 ==> #[trigger] hs1.contains(x as u8) ==> #[trigger] s1.contains(x as u8),
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int|
            #![auto]
            0 <= i < s0.len() && 0 <= s0[i] < 256 && hs1.contains(s0[i]) ==> s1.contains(s0[i]),
    // post-conditions-end
{
    // impl-start
    assert forall|i: int|
        #![auto]
        0 <= i < s0.len() && 0 <= s0[i] < 256 && hs1.contains(s0[i]) implies s1.contains(s0[i]) by {
        let x = s0[i];
        assert(0 <= x < 256);
        assert(hs1.contains(x as u8));
        assert(s1.contains(x as u8));
    };
    // impl-end
}
// pure-end

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
    let hs0 = hash_set_from(s0);
    let hs1 = hash_set_from(s1);
    
    // Check if all chars in s0 are in s1
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < s0.len()
        invariant
            0 <= i <= s0.len(),
            forall|j: int| #![auto] 0 <= j < i ==> s1@.contains(s0[j]),
        decreases s0.len() - i
    {
        /* code modified by LLM (iteration 1): use exec contains method instead of spec contains */
        if !hs1.contains(&s0[i]) {
            return false;
        }
        i = i + 1;
    }
    
    // Check if all chars in s1 are in s0
    let mut j = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while j < s1.len()
        invariant
            0 <= j <= s1.len(),
            forall|k: int| #![auto] 0 <= k < j ==> s0@.contains(s1[k]),
            forall|k: int| #![auto] 0 <= k < s0.len() ==> s1@.contains(s0[k]),
        decreases s1.len() - j
    {
        /* code modified by LLM (iteration 1): use exec contains method instead of spec contains */
        if !hs0.contains(&s1[j]) {
            return false;
        }
        j = j + 1;
    }
    
    true
}

}
fn main() {}