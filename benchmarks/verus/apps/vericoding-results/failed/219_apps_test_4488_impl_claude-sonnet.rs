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
/* helper modified by LLM (iteration 5): Fixed complex argument error by storing chars in variable first */
fn split_lines(input: &str) -> (result: Vec<String>)
    ensures
        result@.len() == split_lines_spec(input@).len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@ == split_lines_spec(input@)[i],
{
    let mut lines = Vec::new();
    let mut current_line = String::new();
    let mut i = 0;
    
    while i < input.len()
        invariant
            0 <= i <= input.len(),
    {
        let chars: Vec<char> = input.chars().collect();
        if i < chars.len() && chars[i] == '\n' {
            lines.push(current_line);
            current_line = String::new();
        } else if i < chars.len() {
            current_line.push(chars[i]);
        }
        i += 1;
    }
    
    if current_line.len() > 0 {
        lines.push(current_line);
    }
    
    lines
}

fn parse_int(s: &str) -> (result: i32)
    requires is_valid_integer(s@)
    ensures result as int == parse_int_spec(s@)
{
    let mut result = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result >= 0,
    {
        let chars: Vec<char> = s.chars().collect();
        if i < chars.len() {
            let c = chars[i];
            if c >= '0' && c <= '9' {
                result = result * 10 + (c as i32 - '0' as i32);
            }
        }
        i += 1;
    }
    
    result
}

fn check_valid_input(input: &str) -> (result: bool)
    ensures result == valid_input(input@)
{
    let lines = split_lines(input);
    if lines.len() < 2 {
        return false;
    }
    
    let line1 = &lines[0];
    let line2 = &lines[1];
    let chars1: Vec<char> = line1.chars().collect();
    let chars2: Vec<char> = line2.chars().collect();
    let chars1_iter = chars1.iter();
    let chars2_iter = chars2.iter();
    let line1_valid = chars1_iter.all(|c| *c >= '0' && *c <= '9') && line1.len() > 0;
    let line2_valid = chars2_iter.all(|c| *c >= '0' && *c <= '9') && line2.len() > 0;
    
    line1_valid && line2_valid
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
    /* code modified by LLM (iteration 5): Using fixed helpers without compilation errors */
    if !check_valid_input(input) {
        return String::new();
    }
    
    let lines = split_lines(input);
    let a = parse_int(&lines[0]);
    let b = parse_int(&lines[1]);
    
    if a < b {
        String::from("LESS\n")
    } else if a > b {
        String::from("GREATER\n")
    } else {
        String::from("EQUAL\n")
    }
}
// </vc-code>


}

fn main() {}