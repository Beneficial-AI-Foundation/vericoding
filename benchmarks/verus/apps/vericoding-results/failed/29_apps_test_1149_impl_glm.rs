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
/* helper modified by LLM (iteration 3): Fixed return type syntax for tuple */
exec fn parse_input(input: &[u8]) -> (u32, Vec<u32>, Vec<u32>) {
    let s = std::str::from_utf8(input).unwrap();
    let mut lines = s.lines();
    let n_line = lines.next().unwrap();
    let n = n_line.parse().unwrap();
    let x_line = lines.next().unwrap();
    let y_line = lines.next().unwrap();

    let x_parts: Vec<u32> = x_line.split_whitespace().map(|s| s.parse().unwrap()).collect();
    let y_parts: Vec<u32> = y_line.split_whitespace().map(|s| s.parse().unwrap()).collect();

    (n, x_parts, y_parts)
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (result: Vec<u8>)
    requires valid_input(stdin_input@.map(|i, c| c as char))
    ensures result@.map(|i, c| c as char) == get_expected_output(stdin_input@.map(|i, c| c as char))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced byte string literals with arrays of bytes to fix compilation error */
{
    let (n, x_line, y_line) = parse_input(&stdin_input);
    let mut present = vec![false; n as usize + 1];

    // Process x_line: skip the first element (the count)
    let x_count = x_line[0] as usize;
    for i in 1..x_count+1 {
        let level = x_line[i];
        if level >= 1 && level <= n {
            present[level as usize] = true;
        }
    }

    // Process y_line: skip the first element (the count)
    let y_count = y_line[0] as usize;
    for i in 1..y_count+1 {
        let level = y_line[i];
        if level >= 1 && level <= n {
            present[level as usize] = true;
        }
    }

    // Check if all levels from 1 to n are present
    let mut all_present = true;
    for i in 1..(n+1) {
        if !present[i as usize] {
            all_present = false;
            break;
        }
    }

    if all_present {
        [73, 32, 98, 101, 99, 111, 109, 101, 32, 116, 104, 101, 32, 103, 117, 121, 46].to_vec()
    } else {
        [79, 104, 44, 32, 109, 121, 32, 107, 101, 121, 98, 111, 97, 114, 100, 33].to_vec()
    }
}
// </vc-code>


}

fn main() {}