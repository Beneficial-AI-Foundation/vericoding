// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn char_set(s: Seq<char>) -> Set<char> {
    s.to_set()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn same_chars(s0: Vec<char>, s1: Vec<char>) -> (result: bool)
    ensures result == (char_set(s0@) == char_set(s1@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariants and added lemmas to establish postconditions */
    let mut i: usize = 0;
    while i < s0.len()
        invariant
            i <= s0.len(),
            forall|j: int| 0 <= j < i ==> s1@.contains(s0@[j]),
        decreases s0.len() - i
    {
        let c = s0[i];
        let mut found = false;
        let mut j: usize = 0;
        while j < s1.len()
            invariant
                j <= s1.len(),
                found <==> exists|k: int| 0 <= k < j && s1@[k] == c,
            decreases s1.len() - j
        {
            if s1[j] == c {
                found = true;
            }
            j = j + 1;
        }
        
        assert(j == s1.len());
        assert(found <==> exists|k: int| 0 <= k < s1.len() && s1@[k] == c);
        assert(found <==> s1@.contains(c));
        
        if !found {
            assert(forall|k: int| 0 <= k < s1.len() ==> s1@[k] != c);
            assert(!s1@.contains(c));
            assert(char_set(s0@).contains(c));
            assert(!char_set(s1@).contains(c));
            assert(char_set(s0@) != char_set(s1@));
            return false;
        }
        assert(s1@.contains(c));
        i = i + 1;
    }
    
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            forall|j: int| 0 <= j < i ==> s0@.contains(s1@[j]),
        decreases s1.len() - i
    {
        let c = s1[i];
        let mut found = false;
        let mut j: usize = 0;
        while j < s0.len()
            invariant
                j <= s0.len(),
                found <==> exists|k: int| 0 <= k < j && s0@[k] == c,
            decreases s0.len() - j
        {
            if s0[j] == c {
                found = true;
            }
            j = j + 1;
        }
        
        assert(j == s0.len());
        assert(found <==> exists|k: int| 0 <= k < s0.len() && s0@[k] == c);
        assert(found <==> s0@.contains(c));
        
        if !found {
            assert(forall|k: int| 0 <= k < s0.len() ==> s0@[k] != c);
            assert(!s0@.contains(c));
            assert(char_set(s1@).contains(c));
            assert(!char_set(s0@).contains(c));
            assert(char_set(s0@) != char_set(s1@));
            return false;
        }
        assert(s0@.contains(c));
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < s0.len() ==> s1@.contains(s0@[j]));
    assert(forall|j: int| 0 <= j < s1.len() ==> s0@.contains(s1@[j]));
    assert(forall|c: char| s0@.contains(c) ==> s1@.contains(c));
    assert(forall|c: char| s1@.contains(c) ==> s0@.contains(c));
    assert(char_set(s0@) == char_set(s1@));
    true
}
// </vc-code>


}

fn main() {}