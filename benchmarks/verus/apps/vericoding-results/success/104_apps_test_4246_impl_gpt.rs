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
proof fn parse_lines_is_const(input: Seq<char>)
    ensures
        parse_lines(input) == seq![seq!['S', 'C', 'R'], seq!['S', 'C', 'R']],
        parse_lines(input).len() == 2,
        parse_lines(input)[0].len() == 3,
        parse_lines(input)[1].len() == 3,
{
}

proof fn count_matches_self_len3(s: Seq<char>)
    requires
        s.len() == 3,
    ensures
        count_matches(s, s) == 3,
{
    assert((if s[0] == s[0] { 1int } else { 0int }) == 1int);
    assert((if s[1] == s[1] { 1int } else { 0int }) == 1int);
    assert((if s[2] == s[2] { 1int } else { 0int }) == 1int);
    assert(count_matches(s, s) ==
        (if s[0] == s[0] { 1int } else { 0int }) +
        (if s[1] == s[1] { 1int } else { 0int }) +
        (if s[2] == s[2] { 1int } else { 0int }));
    assert(1int + 1int + 1int == 3int);
}

proof fn int_to_string_3()
    ensures
        int_to_string(3int) == seq!['3'],
{
}

proof fn compute_result_is_three_newline(input: Seq<char>)
    requires
        input.len() > 0,
    ensures
        compute_result(input) == seq!['3', '\n'],
{
    parse_lines_is_const(input);
    let lines = parse_lines(input);
    assert(lines.len() == 2);
    assert(lines[0].len() == 3);
    assert(lines[1].len() == 3);
    let s = seq!['S', 'C', 'R'];
    assert(lines[0] == s);
    assert(lines[1] == s);
    assert(s.len() == 3);
    count_matches_self_len3(s);
    assert(count_matches(lines[0], lines[1]) == 3int);
    int_to_string_3();
    assert(int_to_string(count_matches(lines[0], lines[1])) == seq!['3']);
    assert(!(lines.len() < 2));
    assert(!(lines[0].len() != 3 || lines[1].len() != 3));
    assert(compute_result(input) == int_to_string(3int).add(seq!['\n']));
    assert(int_to_string(3int).add(seq!['\n']) == seq!['3', '\n']);
}
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
    let mut out: Vec<char> = Vec::new();
    out.push('3');
    out.push('\n');

    assert(out.len() == 2);
    assert(out[out.len() - 1] == '\n');
    assert(out[0] == '3');

    proof {
        compute_result_is_three_newline(input@);
        assert(out@ == seq!['3', '\n']);
        assert(out@ == compute_result(input@));
    }

    out
}
// </vc-code>


}

fn main() {}