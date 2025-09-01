use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
fn vec_contains(v: &Vec<u8>, x: u8) -> (res: bool)
    ensures
        res <==> (exists|i: int| 0 <= i < v.len() && v@[i] == x)
{
    let mut i: int = 0;
    while i < v.len() {
        invariant 0 <= i <= v.len();
        invariant forall|j: int| 0 <= j < i ==> v@[j] != x;
        if v@[i] == x {
            proof {
                assert(0 <= i && i < v.len() && v@[i] == x);
            }
            return true;
        }
        i += 1;
    }
    proof {
        assert(forall|j: int| 0 <= j < v.len() ==> v@[j] != x);
        assert(!(exists|k: int| 0 <= k < v.len() && v@[k] == x));
    }
    false
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
    // impl-start
    // check every element of s0 is contained in s1
    let mut i: int = 0;
    while i < s0.len() {
        invariant 0 <= i <= s0.len();
        invariant forall|j: int| 0 <= j < i ==>
            (exists|k: int| 0 <= k < s1.len() && s1@[k] == s0@[j]);
        let c = vec_contains(s1, s0@[i]);
        if !c {
            proof {
                // vec_contains ensures c <==> exists k . s1@[k] == s0@[i]
                assert(0 <= i && i < s0.len());
                assert(!(exists|k: int| 0 <= k < s1.len() && s1@[k] == s0@[i]));
                // witness that the universal for s0 fails at index i
                assert(exists|idx: int| 0 <= idx < s0.len() && !(exists|k: int| 0 <= k < s1.len() && s1@[k] == s0@[idx]));
                assert(!(forall|idx: int| 0 <= idx < s0.len() ==> (exists|k: int| 0 <= k < s1.len() && s1@[k] == s0@[idx])));
            }
            return false;
        } else {
            proof {
                // extract witness that s0[i] is in s1, to maintain invariant for i+1
                assert(exists|k: int| 0 <= k < s1.len() && s1@[k] == s0@[i]);
            }
        }
        i += 1;
    }

    // check every element of s1 is contained in s0
    let mut j: int = 0;
    while j < s1.len() {
        invariant 0 <= j <= s1.len();
        invariant forall|t: int| 0 <= t < j ==>
            (exists|k: int| 0 <= k < s0.len() && s0@[k] == s1@[t]);
        let c2 = vec_contains(s0, s1@[j]);
        if !c2 {
            proof {
                assert(0 <= j && j < s1.len());
                assert(!(exists|k: int| 0 <= k < s0.len() && s0@[k] == s1@[j]));
                assert(exists|idx: int| 0 <= idx < s1.len() && !(exists|k: int| 0 <= k < s0.len() && s0@[k] == s1@[idx]));
                assert(!(forall|idx: int| 0 <= idx < s1.len() ==> (exists|k: int| 0 <= k < s0.len() && s0@[k] == s1@[idx])));
            }
            return false;
        } else {
            proof {
                assert(exists|k: int| 0 <= k < s0.len() && s0@[k] == s1@[j]);
            }
        }
        j += 1;
    }

    proof {
        // From loop invariants at completion, both universal containment properties hold
        assert(forall|idx: int| 0 <= idx < s0.len() ==>
            (exists|k: int| 0 <= k < s1.len() && s1@[k] == s0@[idx]));
        assert(forall|idx: int| 0 <= idx < s1.len() ==>
            (exists|k: int| 0 <= k < s0.len() && s0@[k] == s1@[idx]));
    }
    true
    // impl-end
}
// </vc-code>

fn main() {}
}