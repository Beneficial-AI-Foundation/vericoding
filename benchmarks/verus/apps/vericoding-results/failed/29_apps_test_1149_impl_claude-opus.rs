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

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (result: Vec<u8>)
    requires valid_input(stdin_input@.map(|i, c| c as char))
    ensures result@.map(|i, c| c as char) == get_expected_output(stdin_input@.map(|i, c| c as char))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed byte literal syntax - use numeric values instead */
    // Parse input using helper functions that work with Vec<u8>
    let mut lines_vec: Vec<Vec<u8>> = Vec::new();
    let mut current_line: Vec<u8> = Vec::new();
    
    for i in 0..stdin_input.len() {
        if stdin_input[i] == 10u8 {  // 10 is '\n'
            // Remove \r if present
            if current_line.len() > 0 && current_line[current_line.len() - 1] == 13u8 {  // 13 is '\r'
                current_line.pop();
            }
            lines_vec.push(current_line);
            current_line = Vec::new();
        } else {
            current_line.push(stdin_input[i]);
        }
    }
    if current_line.len() > 0 {
        // Remove \r if present
        if current_line[current_line.len() - 1] == 13u8 {  // 13 is '\r'
            current_line.pop();
        }
        lines_vec.push(current_line);
    }
    
    // Parse n from first line
    let n_line = &lines_vec[0];
    let mut n: i32 = 0;
    for i in 0..n_line.len() {
        n = n * 10 + (n_line[i] - 48u8) as i32;  // 48 is '0'
    }
    
    // Parse x_line
    let x_line_bytes = &lines_vec[1];
    let mut x_nums: Vec<i32> = Vec::new();
    let mut current_num: i32 = 0;
    for i in 0..x_line_bytes.len() {
        if x_line_bytes[i] == 32u8 {  // 32 is ' '
            x_nums.push(current_num);
            current_num = 0;
        } else {
            current_num = current_num * 10 + (x_line_bytes[i] - 48u8) as i32;  // 48 is '0'
        }
    }
    x_nums.push(current_num);
    
    // Parse y_line
    let y_line_bytes = &lines_vec[2];
    let mut y_nums: Vec<i32> = Vec::new();
    current_num = 0;
    for i in 0..y_line_bytes.len() {
        if y_line_bytes[i] == 32u8 {  // 32 is ' '
            y_nums.push(current_num);
            current_num = 0;
        } else {
            current_num = current_num * 10 + (y_line_bytes[i] - 48u8) as i32;  // 48 is '0'
        }
    }
    y_nums.push(current_num);
    
    let x_count = x_nums[0];
    let y_count = y_nums[0];
    
    // Check if all levels from 1 to n are covered
    let mut all_covered = true;
    let mut i: i32 = 1;
    
    while i <= n {
        let mut found = false;
        
        // Check in x_nums
        let mut j: usize = 1;
        while j <= x_count as usize && j < x_nums.len() {
            if x_nums[j] == i {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        // Check in y_nums if not found
        if !found {
            let mut k: usize = 1;
            while k <= y_count as usize && k < y_nums.len() {
                if y_nums[k] == i {
                    found = true;
                    break;
                }
                k = k + 1;
            }
        }
        
        if !found {
            all_covered = false;
            break;
        }
        i = i + 1;
    }
    
    if all_covered {
        let mut result = Vec::<u8>::new();
        result.push(73u8);   // 'I'
        result.push(32u8);   // ' '
        result.push(98u8);   // 'b'
        result.push(101u8);  // 'e'
        result.push(99u8);   // 'c'
        result.push(111u8);  // 'o'
        result.push(109u8);  // 'm'
        result.push(101u8);  // 'e'
        result.push(32u8);   // ' '
        result.push(116u8);  // 't'
        result.push(104u8);  // 'h'
        result.push(101u8);  // 'e'
        result.push(32u8);   // ' '
        result.push(103u8);  // 'g'
        result.push(117u8);  // 'u'
        result.push(121u8);  // 'y'
        result.push(46u8);   // '.'
        result
    } else {
        let mut result = Vec::<u8>::new();
        result.push(79u8);   // 'O'
        result.push(104u8);  // 'h'
        result.push(44u8);   // ','
        result.push(32u8);   // ' '
        result.push(109u8);  // 'm'
        result.push(121u8);  // 'y'
        result.push(32u8);   // ' '
        result.push(107u8);  // 'k'
        result.push(101u8);  // 'e'
        result.push(121u8);  // 'y'
        result.push(98u8);   // 'b'
        result.push(111u8);  // 'o'
        result.push(97u8);   // 'a'
        result.push(114u8);  // 'r'
        result.push(100u8);  // 'd'
        result.push(33u8);   // '!'
        result
    }
}
// </vc-code>


}

fn main() {}