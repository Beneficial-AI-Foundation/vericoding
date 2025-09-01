use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>

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
    let mut set0 = HashSetWithView::new();
    for i in 0..s0.len()
        invariant set0.view() == (s0@[0..(i as int)]).to_set()
    {
        set0.insert(s0[i]);
    }

    let mut set1 = HashSetWithView::new();
    for i in 0..s1.len()
        invariant set1.view() == (s1@[0..(i as int)]).to_set()
    {
        set1.insert(s1[i]);
    }

    if set0.len() != set1.len() {
        false
    } else {
        let mut all_contained = true;
        for i in 0..s0.len() {
            if !set1.contains(&s0[i]) {
                all_contained = false;
                break;
            }
        }
        if !all_contained {
            false
        } else {
            for i in 0..s1.len() {
                if !set0.contains(&s1[i]) {
                    all_contained = false;
                    break;
                }
            }
            all_contained
        }
    }
}
// </vc-code>

fn main() {}
}