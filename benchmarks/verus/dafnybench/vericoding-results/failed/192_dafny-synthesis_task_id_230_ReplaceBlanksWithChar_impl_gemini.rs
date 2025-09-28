// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace_blanks_with_char(s: Seq<char>, ch: char) -> (v: Seq<char>)
    ensures 
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> {
            (s[i] == ' ' ==> v[i] == ch) &&
            (s[i] != ' ' ==> v[i] == s[i])
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected types from ghost (Seq, nat) to executable (Vec, usize) and used executable indexing. */
    let mut v: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v.len() == i,
            forall|j: int| 0 <= j < i as int ==> (
                (s@[j] == ' ' ==> v@[j] == ch) &&
                (s@[j] != ' ' ==> v@[j] == s@[j])
            ),
        decreases s.len() - i
    {
        if s[i] == ' ' {
            v.push(ch);
        } else {
            v.push(s[i]);
        }
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}