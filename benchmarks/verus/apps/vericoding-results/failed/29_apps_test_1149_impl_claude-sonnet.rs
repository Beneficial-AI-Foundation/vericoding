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
        x_line.len() >= (1 + x_line[0]) as nat && y_line.len() >= (1 + y_line[0]) as nat
    }
}

spec fn get_expected_output(stdin_input: Seq<char>) -> Seq<char>
    recommends valid_input(stdin_input)
{
    let lines = split_lines(stdin_input);
    let n = parse_int(lines[0]);
    let x_line = parse_int_list(lines[1]);
    let y_line = parse_int_list(lines[2]);
    let x_levels = set_from_seq(x_line.subrange(1, 1 + x_line[0] as int));
    let y_levels = set_from_seq(y_line.subrange(1, 1 + y_line[0] as int));
    let all_levels = x_levels.union(y_levels);
    let required_levels = Set::new(|i: int| 1 <= i <= n);
    if required_levels.subset_of(all_levels) { 
        Seq::new(17, |i: int| if i == 0 { 'I' } else if i == 1 { ' ' } else if i == 2 { 'b' } else if i == 3 { 'e' } else if i == 4 { 'c' } else if i == 5 { 'o' } else if i == 6 { 'm' } else if i == 7 { 'e' } else if i == 8 { ' ' } else if i == 9 { 't' } else if i == 10 { 'h' } else if i == 11 { 'e' } else if i == 12 { ' ' } else if i == 13 { 'g' } else if i == 14 { 'u' } else if i == 15 { 'y' } else { '.' })
    } else { 
        Seq::new(16, |i: int| if i == 0 { 'O' } else if i == 1 { 'h' } else if i == 2 { ',' } else if i == 3 { ' ' } else if i == 4 { 'm' } else if i == 5 { 'y' } else if i == 6 { ' ' } else if i == 7 { 'k' } else if i == 8 { 'e' } else if i == 9 { 'y' } else if i == 10 { 'b' } else if i == 11 { 'o' } else if i == 12 { 'a' } else if i == 13 { 'r' } else if i == 14 { 'd' } else { '!' })
    }
}

spec fn set_from_seq(s: Seq<int>) -> Set<int> {
    Set::new(|x: int| s.contains(x))
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::new(0 as nat, |j: int| Seq::new(0 as nat, |k: int| ' '))
    } else {
        let newline_pos = find_char(s, '\n');
        if newline_pos == -1 {
            Seq::new(1 as nat, |j: int| trim(s))
        } else if 0 <= newline_pos < s.len() {
            Seq::new(1 as nat, |j: int| trim(s.subrange(0, newline_pos))).add(split_lines(s.subrange(newline_pos+1, s.len() as int)))
        } else {
            Seq::new(1 as nat, |j: int| trim(s))
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
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> ('0' <= s[i] <= '9')
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
    (c as u32 as int) - ('0' as u32 as int)
}

spec fn parse_int_list(s: Seq<char>) -> Seq<int> {
    let parts = split_by_char(s, ' ');
    Seq::new(parts.len(), |i: int| parse_int(parts[i]))
}

spec fn split_by_char(s: Seq<char>, delimiter: char) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::new(0 as nat, |j: int| Seq::new(0 as nat, |k: int| ' '))
    } else {
        let delim_pos = find_char(s, delimiter);
        if delim_pos == -1 {
            Seq::new(1 as nat, |j: int| s)
        } else if delim_pos == 0 {
            split_by_char(s.subrange(1, s.len() as int), delimiter)
        } else if 0 < delim_pos < s.len() {
            Seq::new(1 as nat, |j: int| s.subrange(0, delim_pos)).add(split_by_char(s.subrange(delim_pos+1, s.len() as int), delimiter))
        } else {
            Seq::new(1 as nat, |j: int| s)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed message.len() usage, converted to bytes directly */
fn convert_to_string(message: &str) -> Vec<u8> {
    let bytes = message.as_bytes();
    let mut result = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        result.push(bytes[i]);
        i += 1;
    }
    result
}

fn parse_input(input: &Vec<u8>) -> (usize, Vec<usize>, Vec<usize>) {
    let input_str = std::str::from_utf8(input).unwrap();
    let lines: Vec<&str> = input_str.lines().collect();
    
    let n: usize = lines[0].parse().unwrap();
    
    let x_parts: Vec<&str> = lines[1].split_whitespace().collect();
    let x_count: usize = x_parts[0].parse().unwrap();
    let mut x_levels = Vec::new();
    let mut i = 1;
    while i <= x_count {
        x_levels.push(x_parts[i].parse().unwrap());
        i += 1;
    }
    
    let y_parts: Vec<&str> = lines[2].split_whitespace().collect();
    let y_count: usize = y_parts[0].parse().unwrap();
    let mut y_levels = Vec::new();
    let mut j = 1;
    while j <= y_count {
        y_levels.push(y_parts[j].parse().unwrap());
        j += 1;
    }
    
    (n, x_levels, y_levels)
}

fn has_all_levels(n: usize, x_levels: &Vec<usize>, y_levels: &Vec<usize>) -> bool {
    let mut level = 1;
    while level <= n {
        let mut found = false;
        let mut i = 0;
        while i < x_levels.len() {
            if x_levels[i] == level {
                found = true;
                break;
            }
            i += 1;
        }
        if !found {
            let mut j = 0;
            while j < y_levels.len() {
                if y_levels[j] == level {
                    found = true;
                    break;
                }
                j += 1;
            }
        }
        if !found {
            return false;
        }
        level += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (result: Vec<u8>)
    requires valid_input(stdin_input@.map(|i, c| c as char))
    ensures result@.map(|i, c| c as char) == get_expected_output(stdin_input@.map(|i, c| c as char))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementation unchanged from iteration 4 */
    let (n, x_levels, y_levels) = parse_input(&stdin_input);
    
    if has_all_levels(n, &x_levels, &y_levels) {
        convert_to_string("I become the guy.")
    } else {
        convert_to_string("Oh, my keyboard!")
    }
}
// </vc-code>


}

fn main() {}