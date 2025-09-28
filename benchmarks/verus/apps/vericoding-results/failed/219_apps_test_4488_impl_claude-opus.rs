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
    /* code modified by LLM (iteration 5): Fixed type annotation and method name errors */
    let input_seq = input@;
    
    let lines = split_lines(input);
    if lines.len() < 2 {
        return String::new();
    }
    
    let line0 = &lines[0];
    let line1 = &lines[1];
    
    if !is_valid_int_string(line0) || !is_valid_int_string(line1) {
        return String::new();
    }
    
    let a = parse_int(line0);
    let b = parse_int(line1);
    
    if a < b {
        String::from("LESS\n")
    } else if a > b {
        String::from("GREATER\n")
    } else {
        String::from("EQUAL\n")
    }
}

fn split_lines(s: &str) -> (result: Vec<String>)
    ensures result@.len() == split_lines_spec(s@).len(),
            forall|i: int| 0 <= i < result@.len() ==> result@[i]@ == split_lines_spec(s@)[i]
{
    let mut lines = Vec::new();
    let mut current_line = String::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            lines@.len() + (if current_line@.len() > 0 { 1int } else { 0int }) <= split_lines_spec(s@.subrange(0, i as int)).len() + 1
    {
        let ch = s.get_char(i);
        if ch == '\n' {
            lines.push(current_line);
            current_line = String::new();
        } else {
            current_line.push(ch);
        }
        i = i + 1;
    }
    
    if current_line.len() > 0 {
        lines.push(current_line);
    }
    
    lines
}

fn is_valid_int_string(s: &String) -> (result: bool)
    ensures result == is_valid_integer(s@)
{
    if s.len() == 0 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> '0' <= s@[j] <= '9'
    {
        let ch = s.get_char(i);
        if ch < '0' || ch > '9' {
            return false;
        }
        i = i + 1;
    }
    
    true
}

fn parse_int(s: &String) -> (result: i64)
    requires is_valid_integer(s@)
    ensures result == parse_int_spec(s@)
{
    let mut result: i64 = 0;
    let mut multiplier: i64 = 1;
    let mut i: usize = s.len() - 1;
    
    loop
        invariant
            i < s.len(),
            multiplier > 0,
            result >= 0
    {
        let ch = s.get_char(i);
        let digit = (ch as i64) - ('0' as i64);
        result = result + digit * multiplier;
        multiplier = multiplier * 10;
        
        if i == 0 {
            break;
        }
        i = i - 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}