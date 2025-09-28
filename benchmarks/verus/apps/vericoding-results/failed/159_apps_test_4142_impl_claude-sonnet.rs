// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    1 <= s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'L' || s[i] == 'R' || s[i] == 'U' || s[i] == 'D'
}

spec fn easily_playable(s: Seq<char>) -> bool {
    (forall|i: int| 0 <= i < s.len() && i % 2 == 0 ==> s[i] != 'L') &&
    (forall|i: int| 0 <= i < s.len() && i % 2 == 1 ==> s[i] != 'R')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use string index notation instead of as_bytes() */
fn char_at(s: &str, i: usize) -> (result: char)
    requires
        i < s@.len(),
    ensures
        result == s@[i as int],
{
    s@[i as int]
}
// </vc-helpers>

// <vc-spec>
fn solve(s: String) -> (result: String)
    requires valid_input(s@)
    ensures result@ == seq!['Y', 'e', 's'] <==> easily_playable(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Directly use string indexing instead of helper */
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            forall|j: int| 0 <= j < i && j % 2 == 0 ==> s@[j] != 'L',
            forall|j: int| 0 <= j < i && j % 2 == 1 ==> s@[j] != 'R',
    {
        let ch = s@[i as int];
        if i % 2 == 0 && ch == 'L' {
            return "No".to_string();
        }
        if i % 2 == 1 && ch == 'R' {
            return "No".to_string();
        }
        i += 1;
    }
    "Yes".to_string()
}
// </vc-code>


}

fn main() {}