// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn clean_input(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        s
    } else if s[s.len() as int - 1] == '\n' || s[s.len() as int - 1] == '\r' || s[s.len() as int - 1] == ' ' {
        clean_input(s.subrange(0, s.len() as int - 1))
    } else {
        s
    }
}

spec fn contains_digit_nine(s: Seq<char>) -> bool
{
    exists|i: int| 0 <= i < s.len() && s[i] == '9'
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires stdin_input.len() > 0
    ensures result@ == "Yes\n"@ || result@ == "No\n"@
    ensures (result@ == "Yes\n"@) <==> contains_digit_nine(clean_input(stdin_input@))
    ensures (result@ == "No\n"@) <==> !contains_digit_nine(clean_input(stdin_input@))
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}