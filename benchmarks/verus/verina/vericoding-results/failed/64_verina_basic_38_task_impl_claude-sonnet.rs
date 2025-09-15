// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all_characters_same(s: Seq<char>) -> (result: bool)
    requires true,
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 0 && exists|i: int| 0 <= i < s.len() && #[trigger] s[i] != s[0]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches and sequence indexing */
    if s.len() == 0nat {
        return true;
    }
    
    let first_char = s@[0int];
    
    for i in 0..s.len() as usize
        invariant
            forall|k: int| 0 <= k < i ==> s@[k] == first_char
    {
        if s@[i as int] != first_char {
            return false;
        }
    }
    
    true
}
// </vc-code>

}
fn main() {}