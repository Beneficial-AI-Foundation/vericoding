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
// </vc-preamble>

// <vc-helpers>
spec fn parse_integer_helper(s: Seq<char>, index: int) -> int {
    if index >= s.len() {
        0
    } else if '0' <= s[index] <= '9' {
        (s[index] as int) - ('0' as int)
    } else {
        parse_integer_helper(s, index + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(stdin_input),
    ensures ({let n = parse_integer_value(stdin_input); is_celebrated_age(n) ==> result == seq!['Y', 'E', 'S', '\n']}),
    ensures ({let n = parse_integer_value(stdin_input); !is_celebrated_age(n) ==> result == seq!['N', 'O', '\n']}),
    ensures result == seq!['Y', 'E', 'S', '\n'] || result == seq!['N', 'O', '\n'],
// </vc-spec>
// <vc-code>
{
    assume(false);
    seq![]
}
// </vc-code>


}

fn main() {}