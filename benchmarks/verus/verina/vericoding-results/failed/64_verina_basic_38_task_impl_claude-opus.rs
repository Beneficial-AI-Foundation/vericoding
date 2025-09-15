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
    /* code modified by LLM (iteration 5): Fixed type errors with nat/usize conversions and sequence indexing with @ operator */
    if s.len() == 0nat {
        return true;
    }
    
    let first_char = s@[0int];
    let mut i: usize = 1;
    
    while i < s.len() as usize
        invariant
            0 <= i <= s.len() as usize,
            forall|j: int| 0 <= j < i as int ==> s@[j] == first_char,
    {
        if s@[i as int] != first_char {
            return false;
        }
        i = i + 1;
    }
    
    return true;
}
// </vc-code>

}
fn main() {}