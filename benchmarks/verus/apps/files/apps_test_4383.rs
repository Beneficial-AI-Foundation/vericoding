// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && exists|i: int| 0 <= i < s.len() && '0' <= s[i] <= '9'
}

spec fn is_celebrated_age(age: int) -> bool {
    age == 3 || age == 5 || age == 7
}

spec fn parse_integer_value(s: Seq<char>) -> int {
    parse_integer_helper(s, 0)
}
spec fn parse_integer_helper(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos
{
    if pos >= s.len() {
        0
    } else if '0' <= s[pos] <= '9' {
        (s[pos] as int) - ('0' as int)
    } else {
        parse_integer_helper(s, pos + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires valid_input(stdin_input@)
    ensures ({
        let n = parse_integer_value(stdin_input@);
        (is_celebrated_age(n) ==> result@ == "YES\n"@) &&
        (!is_celebrated_age(n) ==> result@ == "NO\n"@) &&
        (result@ == "YES\n"@ || result@ == "NO\n"@)
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}