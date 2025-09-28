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
fn parse_int(s: &str) -> (i: int) {
    let mut res: int = 0;
    let mut i: int = 0;
    let s_seq = s@;

    while i < s_seq.len()
        invariant
            0 <= i <= s_seq.len(),
            res == parse_int_helper(s_seq.subrange(0, i), 0),
            forall|j: int| 0 <= j < i ==> ('0' <= s_seq[j] && s_seq[j] <= '9')
        decreases s_seq.len() - i
    {
        let digit = s_seq[i] as int - '0' as int;
        res = res * 10 + digit;
        i = i + 1;
    }
    res
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
    let input_seq = input@;
    if !valid_input(input_seq) {
        return String::new();
    }

    let lines = split_lines_spec(input_seq);
    let line1 = lines[0];
    let line2 = lines[1];

    let a = parse_int(line1.to_string().as_str());
    let b = parse_int(line2.to_string().as_str());

    if a < b {
        "LESS\n".to_string()
    } else if a > b {
        "GREATER\n".to_string()
    } else {
        "EQUAL\n".to_string()
    }
}
// </vc-code>


}

fn main() {}