// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: &str) -> bool {
    let lines = split_lines_spec(input);
    lines.len() >= 2 && is_valid_integer(&lines[0]) && is_valid_integer(&lines[1])
}

spec fn is_valid_integer(s: &str) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] && s[i] <= '9'
}

spec fn split_lines_spec(s: &str) -> Seq<Seq<char>> {
    if s.len() == 0 {
        seq![]
    } else if s[0] == '\n' {
        split_lines_spec(&s[1..])
    } else {
        let next_newline = find_next_newline(s, 0);
        if next_newline == -1 {
            seq![s@]
        } else {
            seq![s@.subrange(0, next_newline)] + split_lines_spec(&s[(next_newline + 1)..])
        }
    }
}

spec fn find_next_newline(s: &str, start: nat) -> int
    decreases s.len() - start
{
    if start >= s.len() {
        -1
    } else if s[start] == '\n' {
        start as int
    } else {
        find_next_newline(s, start + 1)
    }
}

spec fn parse_int_spec(s: &str) -> int {
    parse_int_helper(s, 0)
}

spec fn parse_int_helper(s: &str, pos: nat) -> int
    decreases s.len() - pos
{
    if pos >= s.len() || s[pos] == '\n' || s[pos] == '\r' {
        0
    } else if '0' <= s[pos] && s[pos] <= '9' {
        (s[pos] as int - '0' as int) + 10 * parse_int_helper(s, pos + 1)
    } else {
        parse_int_helper(s, pos + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires input.len() > 0
    ensures ({
        let lines = split_lines_spec(input);
        valid_input(input) ==> {
            let a = parse_int_spec(&lines[0]);
            let b = parse_int_spec(&lines[1]);
            (result == "LESS\n" <==> a < b) &&
            (result == "GREATER\n" <==> a > b) &&
            (result == "EQUAL\n" <==> a == b)
        }
    }),
    ensures !valid_input(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
    /* impl-start */
    assume(false);
    String::new()
    /* impl-end */
}
// </vc-code>


}

fn main() {}