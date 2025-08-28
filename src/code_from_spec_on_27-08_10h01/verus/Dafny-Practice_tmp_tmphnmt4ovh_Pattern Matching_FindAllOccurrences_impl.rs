use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn matches_at(text: Seq<char>, pattern: Seq<char>, pos: nat) -> bool {
    pos + pattern.len() <= text.len() &&
    text.subrange(pos as int, (pos + pattern.len()) as int) == pattern
}

spec fn all_valid_offsets(text: Seq<char>, pattern: Seq<char>) -> Set<nat> {
    Set::new(|i: nat| matches_at(text, pattern, i))
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_all_occurrences(text: &str, pattern: &str) -> (offsets: Ghost<Set<nat>>)
    ensures 
        forall|i: nat| offsets@.contains(i) ==> i + pattern@.len() <= text@.len(),
        forall|i: nat| 0 <= i && i + pattern@.len() <= text@.len() 
                      ==> (text@.subrange(i as int, (i + pattern@.len()) as int) == pattern@) == offsets@.contains(i)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut offsets = Set::<nat>::empty();
    let text_len = text@.len();
    let pattern_len = pattern@.len();
    
    if pattern_len == 0 {
        return Ghost(Set::empty());
    }
    
    let mut i: usize = 0;
    while i + pattern_len <= text_len
        invariant
            i <= text_len,
            pattern_len > 0,
            forall|j: nat| j < i && matches_at(text@, pattern@, j) ==> offsets.contains(j),
            forall|j: nat| offsets.contains(j) ==> j < i && matches_at(text@, pattern@, j)
    {
        let mut matches = true;
        let mut j: usize = 0;
        
        while j < pattern_len
            invariant
                j <= pattern_len,
                i + pattern_len <= text_len,
                matches == (text@.subrange(i as int, (i + j) as int) == pattern@.subrange(0, j as int))
        {
            if text@[i + j] != pattern@[j] {
                matches = false;
                break;
            }
            j += 1;
        }
        
        if matches {
            proof {
                assert(text@.subrange(i as int, (i + pattern_len) as int) == pattern@);
            }
            offsets = offsets.insert(i as nat);
        }
        
        i += 1;
    }
    
    Ghost(offsets)
}
// </vc-code>

fn main() {}

}