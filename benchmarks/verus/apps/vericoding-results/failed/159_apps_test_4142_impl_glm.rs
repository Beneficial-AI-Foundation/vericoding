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
    /* code modified by LLM (iteration 5): use sequence view s@ instead of as_bytes */
    let n = s@.len() as usize;
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= s@.len(),
            forall|j: int| 0 <= j < i as int && j % 2 == 0 ==> s@[j] != 'L',
            forall|j: int| 0 <= j < i as int && j % 2 == 1 ==> s@[j] != 'R',
        decreases (n - i) as int
    {
        let idx = i as int;
        let c = s@[idx];
        if idx % 2 == 0 {
            if c == 'L' {
                return "No".to_string();
            }
        } else {
            if c == 'R' {
                return "No".to_string();
            }
        }
        i += 1;
    }
    "Yes".to_string()
}
// </vc-code>


}

fn main() {}