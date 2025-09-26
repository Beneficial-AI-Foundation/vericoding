// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && s.len() <= 10 && 
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1' || s[i] == 'B'
}

spec fn simulate_keystrokes(keystrokes: Seq<char>) -> Seq<char>
    decreases keystrokes.len()
{
    if keystrokes.len() == 0 {
        Seq::<char>::empty()
    } else {
        let prev = simulate_keystrokes(keystrokes.subrange(0, keystrokes.len() - 1));
        let last_key = keystrokes[keystrokes.len() - 1];
        if last_key == 'B' {
            if prev.len() > 0 {
                prev.subrange(0, prev.len() - 1)
            } else {
                prev
            }
        } else {
            prev.push(last_key)
        }
    }
}

spec fn valid_output(result: Seq<char>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> result[i] == '0' || result[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(s@),
    ensures 
        valid_output(result@),
        result@ == simulate_keystrokes(s@),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}