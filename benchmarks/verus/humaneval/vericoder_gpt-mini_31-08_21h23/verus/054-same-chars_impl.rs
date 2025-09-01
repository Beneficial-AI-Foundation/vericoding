use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
// no helpers needed
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
    let mut i: int = 0;
    while i < s0.len() {
        invariant 0 <= i && i <= s0.len();
        invariant forall|k: int| #[trigger] 0 <= k < i ==> (exists|t: int| #[trigger] 0 <= t < s1.len() && s1[t] == s0[k]);
        decreases s0.len() - i;
        if !(exists|t: int| #[trigger] 0 <= t < s1.len() && s1[t] == s0[i]) {
            return false;
        }
        i += 1;
    }
    let mut j: int = 0;
    while j < s1.len() {
        invariant 0 <= j && j <= s1.len();
        invariant forall|k: int| #[trigger] 0 <= k < j ==> (exists|t: int| #[trigger] 0 <= t < s0.len() && s0[t] == s1[k]);
        decreases s1.len() - j;
        if !(exists|t: int| #[trigger] 0 <= t < s0.len() && s0[t] == s1[j]) {
            return false;
        }
        j += 1;
    }
    true
}
// </vc-code>

fn main() {}
}