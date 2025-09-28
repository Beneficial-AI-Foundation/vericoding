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
/* code modified by LLM (iteration 5): fixed type mismatches in loop condition, invariants, and decreases clause */
{
    let mut i: usize = 0;
    let mut is_playable = true;

    while i < s@.len() as usize
        invariant
            i as nat <= s@.len(),
            valid_input(s@),
            is_playable <==> easily_playable(s@.subrange(0, i as int)),
        decreases s@.len() - i as nat
    {
        let c = s.get_char(i);

        if i % 2 == 0 {
            if c == 'L' {
                is_playable = false;
            }
        } else {
            if c == 'R' {
                is_playable = false;
            }
        }

        i = i + 1;
    }

    if is_playable {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}