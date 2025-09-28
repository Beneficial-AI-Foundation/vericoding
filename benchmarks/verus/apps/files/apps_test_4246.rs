// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn parse_lines(input: Seq<char>) -> Seq<Seq<char>> {
    seq![seq!['S', 'C', 'R'], seq!['S', 'C', 'R']]
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else if n == 2 { seq!['2'] }
    else { seq!['3'] }
}
spec fn is_valid_input(input: Seq<char>) -> bool
    recommends input.len() > 0
{
    let lines = parse_lines(input);
    lines.len() >= 2 && lines[0].len() == 3 && lines[1].len() == 3
}

spec fn count_matches_from_input(input: Seq<char>) -> int
    recommends input.len() > 0 && is_valid_input(input)
{
    let lines = parse_lines(input);
    count_matches(lines[0], lines[1])
}

spec fn count_matches(s: Seq<char>, t: Seq<char>) -> int
    recommends s.len() == 3 && t.len() == 3
{
    (if s[0] == t[0] { 1int } else { 0int }) +
    (if s[1] == t[1] { 1int } else { 0int }) +
    (if s[2] == t[2] { 1int } else { 0int })
}

spec fn compute_result(input: Seq<char>) -> Seq<char>
    recommends input.len() > 0
{
    let lines = parse_lines(input);
    if lines.len() < 2 {
        seq!['0', '\n']
    } else if lines[0].len() != 3 || lines[1].len() != 3 {
        seq!['0', '\n']
    } else {
        int_to_string(count_matches(lines[0], lines[1])).add(seq!['\n'])
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires
        input.len() > 0,
    ensures
        result@ == compute_result(input@),
        result.len() >= 2 && result[result.len() - 1] == '\n',
        result[0] == '0' || result[0] == '1' || result[0] == '2' || result[0] == '3',
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}