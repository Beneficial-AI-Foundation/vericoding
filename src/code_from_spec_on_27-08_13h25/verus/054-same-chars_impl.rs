use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
broadcast use axiom_u8_obeys_hash_table_key_model;

fn hash_set_from(s: &Vec<u8>) -> (res: HashSetWithView<u8>)
    ensures
        forall|i: int| #![auto] 0 <= i < s.len() ==> res@.contains(s[i]),
        forall|x: int|
            0 <= x < 256 ==> #[trigger] res@.contains(x as u8) ==> #[trigger] s@.contains(x as u8),
{
    let mut res: HashSetWithView<u8> = HashSetWithView::new();
    for i in 0..s.len()
        invariant
            forall|j: int| #![auto] 0 <= j < i ==> res@.contains(s[j]),
            forall|x: int|
                0 <= x < 256 ==> #[trigger] res@.contains(x as u8) ==> (exists|j: int|
                    0 <= j < i && s[j] == x),
    {
        res.insert(s[i]);
    }
    res
}

proof fn implies_contains(s0: Seq<u8>, s1: Seq<u8>, hs1: Set<u8>)
    requires
        forall|i: int| #![trigger s0[i]] 0 <= i < s0.len() ==> 0 <= s0[i] < 256,
        forall|x: int|
            0 <= x < 256 ==> #[trigger] hs1.contains(x as u8) ==> #[trigger] s1.contains(x as u8),
    ensures
        forall|i: int|
            #![auto]
            0 <= i < s0.len() && 0 <= s0[i] < 256 && hs1.contains(s0[i]) ==> s1.contains(s0[i]),
{
    assert forall|i: int|
        #![auto]
        0 <= i < s0.len() && 0 <= s0[i] < 256 && hs1.contains(s0[i]) implies s1.contains(s0[i]) by {
        let x = s0[i];
        assert(0 <= x < 256);
        assert(hs1.contains(x as u8));
        assert(s1.contains(x as u8));
    };
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
    let hs0 = hash_set_from(s0);
    let hs1 = hash_set_from(s1);
    let mut i = 0;
    let mut all_s0_in_s1 = true;
    while i < s0.len()
        invariant
            0 <= i <= s0.len(),
            all_s0_in_s1 ==> forall|j: int| #![auto] 0 <= j < i ==> hs1@.contains(s0[j]),
    {
        if !hs1@.contains(s0[i]) {
            all_s0_in_s1 = false;
        }
        i = i + 1;
    }
    i = 0;
    let mut all_s1_in_s0 = true;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            all_s1_in_s0 ==> forall|j: int| #![auto] 0 <= j < i ==> hs0@.contains(s1[j]),
    {
        if !hs0@.contains(s1[i]) {
            all_s1_in_s0 = false;
        }
        i = i + 1;
    }
    all_s0_in_s1 && all_s1_in_s0
}
// </vc-code>

}
fn main() {}