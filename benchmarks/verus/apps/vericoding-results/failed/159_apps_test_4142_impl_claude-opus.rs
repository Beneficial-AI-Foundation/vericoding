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

// </vc-helpers>

// <vc-spec>
fn solve(s: String) -> (result: String)
    requires valid_input(s@)
    ensures result@ == seq!['Y', 'e', 's'] <==> easily_playable(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed String to Vec<char> conversion using chars() */
    let s_vec: Vec<char> = s.chars().collect();
    let mut i: usize = 0;
    while i < s_vec.len()
        invariant
            0 <= i <= s_vec.len(),
            s_vec@.len() == s@.len(),
            s_vec@ == s@,
            forall|j: int| 0 <= j < i && j % 2 == 0 ==> s_vec@[j] != 'L',
            forall|j: int| 0 <= j < i && j % 2 == 1 ==> s_vec@[j] != 'R'
    {
        if i % 2 == 0 {
            if s_vec[i] == 'L' {
                return "No".to_string();
            }
        } else {
            if s_vec[i] == 'R' {
                return "No".to_string();
            }
        }
        i = i + 1;
    }
    "Yes".to_string()
}
// </vc-code>


}

fn main() {}