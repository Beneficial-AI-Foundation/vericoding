// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_lines_spec(input);
    lines.len() >= 2 && is_valid_integer(lines[0]) && is_valid_integer(lines[1])
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> ('0' <= #[trigger] s[i] && s[i] <= '9')
}

spec fn split_lines_spec(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else if s[0] == '\n' {
        split_lines_spec(s.subrange(1, s.len() as int))
    } else {
        let next_newline = find_next_newline(s, 0);
        if next_newline == -1 {
            seq![s]
        } else if next_newline >= 0 && next_newline < s.len() && next_newline + 1 <= s.len() {
            seq![s.subrange(0, next_newline)] + split_lines_spec(s.subrange(next_newline + 1, s.len() as int))
        } else {
            seq![]
        }
    }
}

spec fn find_next_newline(s: Seq<char>, start: nat) -> int
    decreases s.len() - start
{
    if start >= s.len() {
        -1
    } else if s[start as int] == '\n' {
        start as int
    } else {
        find_next_newline(s, start + 1)
    }
}

spec fn parse_int_spec(s: Seq<char>) -> int {
    parse_int_helper(s, 0)
}

spec fn parse_int_helper(s: Seq<char>, pos: nat) -> int
    decreases s.len() - pos
{
    if pos >= s.len() || s[pos as int] == '\n' || s[pos as int] == '\r' {
        0
    } else if '0' <= s[pos as int] <= '9' {
        (s[pos as int] as int - '0' as int) + 10 * parse_int_helper(s, pos + 1)
    } else {
        parse_int_helper(s, pos + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
fn exec_is_valid_integer(s: &str) -> (result: bool)
    ensures result == is_valid_integer(s@)
{
    let mut i = 0;
    let n = s.len();
    if n == 0 {
        return false;
    }
    while i < n
        invariant
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> '0' <= s@[j] <= '9',
    {
        let c = s.as_bytes()[i] as char;
        if !('0' <= c && c <= '9') {
            return false;
        }
        i += 1;
    }
    true
}

fn exec_parse_int(s: &str) -> (result: Option<int>)
    ensures s@.len() > 0 ==> {
        if is_valid_integer(s@) {
            result == Some(parse_int_spec(s@))
        } else {
            result == None
        }
    }
{
    if !exec_is_valid_integer(s) {
        return None;
    }
    let mut value = 0;
    let mut i = 0;
    let n = s.len();
    while i < n
        invariant
            0 <= i <= n,
            value == parse_int_helper(s@, i as nat),
            forall|j: int| 0 <= j < i ==> '0' <= s@[j] <= '9',
    {
        let c = s.as_bytes()[i] as char;
        let digit = (c as u8) - ('0' as u8);
        value = value * 10 + (digit as int);
        i += 1;
    }
    Some(value)
}

fn exec_split_lines_spec(s: &str) -> (lines: Vec<&str>)
    ensures lines@ == split_lines_spec(s@)
{
    if s.len() == 0 {
        vec![]
    } else {
        let first_char = s.chars().next().unwrap();
        if first_char == '\n' {
            let rest = &s[1..];
            let mut lines = exec_split_lines_spec(rest);
            lines
        } else {
            let next_newline = s.find('\n').unwrap_or(s.len());
            let line = &s[..next_newline];
            let rest = &s[next_newline..];
            let mut lines = exec_split_lines_spec(rest);
            lines.insert(0, line);
            lines
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires input@.len() > 0
    ensures ({
        let input_seq = input@;
        valid_input(input_seq) ==> {
            let lines = split_lines_spec(input_seq);
            let a = parse_int_spec(lines[0]);
            let b = parse_int_spec(lines[1]);
            (result@ == "LESS\n"@) == (a < b) &&
            (result@ == "GREATER\n"@) == (a > b) &&
            (result@ == "EQUAL\n"@) == (a == b)
        }
    }) && ({
        let input_seq = input@;
        !valid_input(input_seq) ==> result@ == ""@
    })
// </vc-spec>
// <vc-code>
{
    let lines = exec_split_lines_spec(input);
    if lines.len() >= 2 {
        let line0 = lines[0];
        let line1 = lines[1];
        if exec_is_valid_integer(line0) && exec_is_valid_integer(line1) {
            let a = exec_parse_int(line0).unwrap();
            let b = exec_parse_int(line1).unwrap();
            if a < b {
                "LESS\n".to_string()
            } else if a > b {
                "GREATER\n".to_string()
            } else {
                "EQUAL\n".to_string()
            }
        } else {
            "".to_string()
        }
    } else {
        "".to_string()
    }
}
// </vc-code>


}

fn main() {}