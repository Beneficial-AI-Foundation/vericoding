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
/* helper modified by LLM (iteration 2): provide simple yes sequence helper for postcondition comparison */
spec fn yes_seq() -> Seq<char> {
    seq!['Y', 'e', 's']
}
// </vc-helpers>

// <vc-spec>
fn solve(s: String) -> (result: String)
    requires valid_input(s@)
    ensures result@ == seq!['Y', 'e', 's'] <==> easily_playable(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): avoid calling spec in exec; compute check via bytes scan */
    let bytes = s.as_bytes();
    let mut ok: bool = true;
    let mut i: usize = 0;
    while i < bytes.len()
        decreases (bytes.len() as int) - (i as int)
    {
        let b = bytes[i];
        if i % 2 == 0 {
            if b == b'L' { ok = false; }
        } else {
            if b == b'R' { ok = false; }
        }
        i += 1;
    }
    if ok { "Yes".to_string() } else { "No".to_string() }
}
// </vc-code>


}

fn main() {}