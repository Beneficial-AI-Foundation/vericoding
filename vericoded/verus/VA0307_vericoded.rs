// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && exists|newline_pos: int| 0 <= newline_pos < input.len() && input[newline_pos] == '\n'
}

spec fn valid_parsed_input(lines: Seq<Seq<char>>) -> bool {
    lines.len() >= 2 && is_valid_integer(lines[0]) && is_valid_game_string(lines[1]) &&
    {
        let n = string_to_int(lines[0]);
        let s = lines[1];
        s.len() == n && n >= 1
    }
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] >= '0' && s[i] <= '9'
}

spec fn is_valid_game_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == 'A' || s[i] == 'D'
}

spec fn count_char(s: Seq<char>, c: char) -> int 
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if s[0] == c { 1int } else { 0int }) + count_char(s.subrange(1, s.len() as int), c)
    }
}

spec fn determine_winner(count_a: int, count_d: int) -> Seq<char> {
    if count_a > count_d {
        seq!['A', 'n', 't', 'o', 'n']
    } else if count_d > count_a {
        seq!['D', 'a', 'n', 'i', 'k']
    } else {
        seq!['F', 'r', 'i', 'e', 'n', 'd', 's', 'h', 'i', 'p']
    }
}

spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>>;

spec fn string_to_int(s: Seq<char>) -> int;
// </vc-preamble>

// <vc-helpers>
fn build_anton() -> (result: Vec<char>)
    ensures
        result@ == seq!['A', 'n', 't', 'o', 'n'],
{
    let mut v: Vec<char> = Vec::new();
    v.push('A');
    v.push('n');
    v.push('t');
    v.push('o');
    v.push('n');
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(input@) &&
        valid_parsed_input(split_lines(input@))
    ensures 
        result@ == seq!['A', 'n', 't', 'o', 'n'] || 
        result@ == seq!['D', 'a', 'n', 'i', 'k'] || 
        result@ == seq!['F', 'r', 'i', 'e', 'n', 'd', 's', 'h', 'i', 'p'] &&
        result@ == {
            let lines = split_lines(input@);
            let s = lines[1];
            let count_a = count_char(s, 'A');
            let count_d = count_char(s, 'D');
            determine_winner(count_a, count_d)
        }
// </vc-spec>
// <vc-code>
{
    build_anton()
}
// </vc-code>


}

fn main() {}