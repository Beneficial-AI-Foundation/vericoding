// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    let lines = split_lines(stdin_input);
    lines.len() >= 3 && {
        let n = parse_int(lines[0]);
        let x_line = parse_int_list(lines[1]);
        let y_line = parse_int_list(lines[2]);
        n >= 1 && x_line.len() > 0 && y_line.len() > 0 &&
        x_line[0] >= 0 && y_line[0] >= 0 &&
        x_line.len() >= (1 + x_line[0]) && y_line.len() >= (1 + y_line[0])
    }
}

spec fn get_expected_output(stdin_input: Seq<char>) -> Seq<char> {
    if valid_input(stdin_input) {
        let lines = split_lines(stdin_input);
        let n = parse_int(lines[0]);
        let x_line = parse_int_list(lines[1]);
        let y_line = parse_int_list(lines[2]);
        let x_levels = set_from_seq(x_line.subrange(1, 1 + x_line[0]));
        let y_levels = set_from_seq(y_line.subrange(1, 1 + y_line[0]));
        let all_levels = x_levels.union(y_levels);
        let required_levels = Set::new(|i: int| 1 <= i <= n);
        if required_levels.subset_of(all_levels) { 
            seq!['I', ' ', 'b', 'e', 'c', 'o', 'm', 'e', ' ', 't', 'h', 'e', ' ', 'g', 'u', 'y', '.'] 
        } else { 
            seq!['O', 'h', ',', ' ', 'm', 'y', ' ', 'k', 'e', 'y', 'b', 'o', 'a', 'r', 'd', '!'] 
        }
    } else {
        seq![]
    }
}

spec fn set_from_seq(s: Seq<int>) -> Set<int> {
    Set::new(|x: int| s.contains(x))
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let newline_pos = find_char(s, '\n');
        if newline_pos == -1 {
            seq![trim(s)]
        } else if 0 <= newline_pos < s.len() {
            seq![trim(s.subrange(0, newline_pos))].add(split_lines(s.subrange(newline_pos + 1, s.len() as int)))
        } else {
            seq![trim(s)]
        }
    }
}

spec fn trim(s: Seq<char>) -> Seq<char> {
    if s.len() == 0 {
        s
    } else if s[s.len() as int - 1] == '\r' {
        s.subrange(0, s.len() as int - 1)
    } else {
        s
    }
}

spec fn find_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        -1
    } else if s[0] == c {
        0
    } else {
        let rest = find_char(s.subrange(1, s.len() as int), c);
        if rest == -1 { -1 } else { rest + 1 }
    }
}

spec fn parse_int(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if s[0] == '-' {
        if is_valid_digits(s.subrange(1, s.len() as int)) { 
            -parse_int_helper(s.subrange(1, s.len() as int)) 
        } else { 
            0 
        }
    } else if is_valid_digits(s) {
        parse_int_helper(s)
    } else {
        0
    }
}

spec fn is_valid_digits(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> ('0' <= s[i] <= '9')
}

spec fn parse_int_helper(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        char_to_digit(s[0])
    } else {
        parse_int_helper(s.subrange(0, s.len() as int - 1)) * 10 + char_to_digit(s[s.len() as int - 1])
    }
}

spec fn char_to_digit(c: char) -> int {
    if '0' <= c <= '9' {
        (c as u32 as int) - ('0' as u32 as int)
    } else {
        0
    }
}

spec fn parse_int_list(s: Seq<char>) -> Seq<int> {
    let parts = split_by_char(s, ' ');
    Seq::new(parts.len(), |i: int| parse_int(parts[i]))
}

spec fn split_by_char(s: Seq<char>, delimiter: char) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let delim_pos = find_char(s, delimiter);
        if delim_pos == -1 {
            seq![s]
        } else if delim_pos == 0 {
            split_by_char(s.subrange(1, s.len() as int), delimiter)
        } else if 0 < delim_pos < s.len() {
            seq![s.subrange(0, delim_pos)].add(split_by_char(s.subrange(delim_pos + 1, s.len() as int), delimiter))
        } else {
            seq![s]
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(stdin_input)
    ensures result == get_expected_output(stdin_input)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}