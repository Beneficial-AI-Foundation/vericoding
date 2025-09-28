// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn char_at(s: Seq<char>, i: int) -> char
    requires 0 <= i < s.len()
{
    s[i]
}

proof fn lemma_different_chars_exist(s: Seq<char>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        s[i] != s[j]
    ensures exists|k: int| 0 <= k < s.len() && s[k] != s[0]
{
    if i == 0 {
        assert(s[j] != s[0]);
    } else {
        assert(s[i] != s[0] || s[j] != s[0]);
    }
}
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
    /* code modified by LLM (iteration 5): use ghost variable for first_char and ghost indexing */
    if s.len() == 0 {
        return true;
    }
    
    let ghost first_char = s[0int];
    let mut i: usize = 1;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int| 0 <= k < i ==> s[k] == first_char
    {
        let ghost current_char = s[i as int];
        if current_char != first_char {
            proof {
                lemma_different_chars_exist(s, 0, i as int);
            }
            return false;
        }
        i = i + 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}