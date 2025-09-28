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
/* helper modified by LLM (iteration 5): Add proper sequence conversion and length helper */
fn string_to_seq_chars(s: &String) -> (seq: Seq<char>)
    ensures seq == s@,
{
    s@
}

spec fn seq_len(s: Seq<char>) -> nat
    ensures result == s.len(),
{
    s.len()
}
// </vc-helpers>

// <vc-spec>
fn solve(s: String) -> (result: String)
    requires valid_input(s@)
    ensures result@ == seq!['Y', 'e', 's'] <==> easily_playable(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use sequence operations instead of Vec */
{
    let seq = string_to_seq_chars(&s);
    let len = seq_len(seq);
    
    let mut valid = true;
    let mut i: int = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            valid == (forall|j: int| 0 <= j < i ==> 
                (j % 2 == 0 ==> seq[j] != 'L') &&
                (j % 2 == 1 ==> seq[j] != 'R'))
    {
        let current_char = seq[i];
        if i % 2 == 0 {
            if current_char == 'L' {
                valid = false;
                break;
            }
        } else {
            if current_char == 'R' {
                valid = false;
                break;
            }
        }
        i += 1;
    }
    
    if valid {
        "Yes".to_string()
    } else {
        "No".to_string()
    }
}
// </vc-code>


}

fn main() {}