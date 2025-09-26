// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && exists|i: int| 0 <= i < s.len() && '0' <= s[i] && s[i] <= '9'
}

spec fn is_celebrated_age(age: int) -> bool {
    age == 3 || age == 5 || age == 7
}

spec fn parse_integer_value(s: Seq<char>) -> int {
    parse_integer_helper(s, 0)
}
spec fn parse_integer_helper(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos when 0 <= pos <= s.len()
{
    if pos >= s.len() {
        0
    } else if '0' <= s[pos] && s[pos] <= '9' {
        (s[pos] as int) - ('0' as int)
    } else {
        parse_integer_helper(s, pos + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (result: String)
    requires valid_input(stdin_input@.map_values(|b: u8| b as char))
    ensures result == if is_celebrated_age(parse_integer_value(stdin_input@.map_values(|b: u8| b as char))) { "YES\n" } else { "NO\n" }
// </vc-spec>
// <vc-code>
{
    assume(false);
    "NO\n".to_string()
}
// </vc-code>


}

fn main() {}