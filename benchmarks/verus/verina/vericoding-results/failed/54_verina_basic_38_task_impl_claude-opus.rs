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
    /* code modified by LLM (iteration 5): Fixed ghost type usage - nat cannot be used in executable code */
    if s.len() == 0 {
        return true;
    }
    
    let first_char = s.index(0);
    let mut i: usize = 1;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i as int ==> s.index(j) == first_char,
    {
        let curr_char = s.index(i);
        if curr_char != first_char {
            proof {
                assert(s.index(i as int) != s.index(0));
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(forall|j: int| 0 <= j < s.len() ==> s.index(j) == first_char);
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s.index(i) == s.index(j));
    }
    true
}
// </vc-code>

}
fn main() {}