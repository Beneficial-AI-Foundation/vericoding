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
/* helper modified by LLM (iteration 5): Simplified valid_lines_from_str and added proper parsing helpers */
fn parse_line_to_int(s: &str) -> (result: i32)
    requires is_valid_integer(s@)
    ensures result == parse_int_spec(s@)
{
    let mut n: i32 = 0;
    let chars = s.chars().collect::<Vec<char>>();
    let mut i: usize = 0;
    
    while i < chars.len()
        invariant
            i <= chars.len(),
            n == parse_int_helper(s@, 0)
        decreases chars.len() - i
    {
        let digit = (chars[i] as i32) - ('0' as i32);
        n = n * 10 + digit;
        i += 1;
    }
    
    n
}

fn get_first_two_lines(s: &str) -> (result: (String, String))
    requires s@.len() > 0
    ensures result.0@.len() == 0 || result.1@.len() == 0 || {
        let lines = split_lines_spec(s@);
        result.0@ == lines[0] && result.1@ == lines[1]
    }
{
    let mut lines = Vec::new();
    let mut current = String::new();
    
    for ch in s.chars() {
        if ch == '\n' {
            lines.push(current.clone());
            current.clear();
            if lines.len() >= 2 { break; }
        } else {
            current.push(ch);
        }
    }
    
    if !current.is_empty() && lines.len() < 2 {
        lines.push(current);
    }
    
    if lines.len() >= 2 {
        (lines[0].clone(), lines[1].clone())
    } else {
        (String::new(), String::new())
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
/* code modified by LLM (iteration 5): Fixed ensures clause syntax */
{
    if !valid_input(input@) {
        String::new()
    } else {
        let (first, second) = get_first_two_lines(input);
        if first.is_empty() || second.is_empty() {
            String::new()
        } else {
            let a = parse_line_to_int(&first);
            let b = parse_line_to_int(&second);
            
            if a < b {
                "LESS\n".to_string()
            } else if a > b {
                "GREATER\n".to_string()
            } else {
                "EQUAL\n".to_string()
            }
        }
    }
}
// </vc-code>


}

fn main() {}