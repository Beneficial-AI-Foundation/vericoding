use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;
use vstd::std_specs::hash::axiom_u8_obeys_hash_table_key_model;

verus! {

// <vc-helpers>
proof fn lemma_seq_contains_remove<A>(s: Seq<A>, a: A, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.contains(a) == (s[i] == a || s.remove(i).contains(a)),
{
}

proof fn lemma_forall_contains_after_remove<A>(s: Seq<A>, a: A, i: int)
    requires
        0 <= i < s.len(),
        forall|j: int| 0 <= j < s.len() ==> s.contains(s[j]),
    ensures
        forall|j: int| 0 <= j < s.remove(i).len() ==> s.remove(i).contains(s.remove(i)[j]),
{
}

spec fn set_from_seq(s: Seq<u8>) -> Set<u8> {
    Set::new(|x: u8| s.contains(x))
}

proof fn lemma_set_from_seq_eq(s0: Seq<u8>, s1: Seq<u8>)
    ensures
        set_from_seq(s0) =~= set_from_seq(s1) <==> 
        (forall|i: int| 0 <= i < s0.len() ==> s1.contains(s0[i])) && 
        (forall|i: int| 0 <= i < s1.len() ==> s0.contains(s1[i])),
{
}

spec fn seq_remove<A>(s: Seq<A>, i: int) -> Seq<A> {
    s.remove(i)
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
    let mut s0_copy = s0.clone();
    let mut s1_copy = s1.clone();
    
    while s0_copy.len() > 0
        invariant
            s0_copy@.subrange(s0@, 0, s0_copy.len() as int),
            s1_copy@.subrange(s1@, 0, s1_copy.len() as int),
            forall|i: int| 0 <= i < s0_copy.len() ==> s1@.contains(s0_copy@[i]) == s1_copy@.contains(s0_copy@[i]),
            exists|removed: Seq<u8>| s0@ =~= s0_copy@ + removed,
        decreases s0_copy.len(),
    {
        let c_opt = s0_copy.pop();
        let c = match c_opt {
            Some(byte) => byte,
            None => break,
        };
        proof {
            let idx = s0_copy.len() as int;
            lemma_seq_contains_remove(s0@, c, idx);
        }
        
        if s1_copy.contains(&c) {
            let mut found = false;
            let mut j = 0;
            while j < s1_copy.len()
                invariant
                    0 <= j <= s1_copy.len(),
                    !found ==> forall|k: int| 0 <= k < j ==> s1_copy@[k] != c,
                    found ==> s1_copy@.contains(c),
                decreases s1_copy.len() - j,
            {
                if s1_copy[j] == c {
                    s1_copy.remove(j);
                    found = true;
                    break;
                }
                j += 1;
            }
        } else {
            return false;
        }
    }
    
    while s1_copy.len() > 0
        invariant
            s1_copy@.subrange(s1@, 0, s1_copy.len() as int),
            forall|i: int| 0 <= i < s1_copy.len() ==> s0@.contains(s1_copy@[i]),
        decreases s1_copy.len(),
    {
        let c_opt = s1_copy.pop();
        let c = match c_opt {
            Some(byte) => byte,
            None => break,
        };
        if !s0.contains(&c) {
            return false;
        }
    }
    
    true
}
// </vc-code>

fn main() {}
}