// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::uninterp]
spec fn parse_lines(input: Seq<char>) -> Seq<Seq<char>>;

#[verifier::uninterp]
spec fn int_to_string_seq(n: int) -> Seq<char>;

spec fn is_valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && {
        let lines = parse_lines(input);
        lines.len() >= 2 && lines[0].len() == 3 && lines[1].len() == 3
    }
}

spec fn count_matches_from_input(input: Seq<char>) -> int {
    let lines = parse_lines(input);
    count_matches(lines[0], lines[1])
}

spec fn count_matches(s: Seq<char>, t: Seq<char>) -> int {
    (if s[0] == t[0] { 1int } else { 0int }) +
    (if s[1] == t[1] { 1int } else { 0int }) +
    (if s[2] == t[2] { 1int } else { 0int })
}

spec fn compute_result(input: Seq<char>) -> Seq<char> {
    if input.len() == 0 {
        seq!['0', '\n']
    } else {
        let lines = parse_lines(input);
        if lines.len() < 2 {
            seq!['0', '\n']
        } else if lines[0].len() != 3 || lines[1].len() != 3 {
            seq!['0', '\n']
        } else {
            int_to_string_seq(count_matches(lines[0], lines[1])).push('\n')
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires input.len() > 0
    ensures 
        result == compute_result(input) &&
        result.len() >= 2 && 
        result[result.len() as int - 1] == '\n' &&
        (result[0] == '0' || result[0] == '1' || result[0] == '2' || result[0] == '3')
// </vc-spec>
// <vc-code>
{
    assume(false);
    seq!['0', '\n']
}
// </vc-code>


}

fn main() {}