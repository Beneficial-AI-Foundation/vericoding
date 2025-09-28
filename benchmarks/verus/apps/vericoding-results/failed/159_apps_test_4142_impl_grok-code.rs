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
/* code modified by LLM (iteration 5): Fixed compilation error by manually building Vec<char> from String using loop and nth to avoid unsupported collect */
{
    let mut chars: Vec<char> = Vec::with_capacity(s.len());
    for i in 0..s.len() {
        let c = s.chars().nth(i).unwrap();
        chars.push(c);
    }
    assert(chars@ == s@);
    let len = chars.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            chars@ == s@,
            forall|j: int| 0 <= j < i ==> (j % 2 == 0 ==> s@[j] != 'L') && (j % 2 == 1 ==> s@[j] != 'R'),
        decreases (len as int - i as int)
    {
        if (i % 2 == 0 && chars[i] == 'L') || (i % 2 == 1 && chars[i] == 'R') {
            return "No".to_string();
        }
        i = i + 1;
    }
    "Yes".to_string()
}
// </vc-code>


}

fn main() {}