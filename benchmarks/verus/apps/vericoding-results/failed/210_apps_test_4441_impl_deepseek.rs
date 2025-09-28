// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0
}

spec fn expected_output(stdin_input: Seq<char>) -> Seq<char> {
    let lines = split_lines_func(stdin_input);
    if lines.len() >= 1 {
        let n = string_to_int(lines[0]);
        if n == 1 {
            seq!['H', 'e', 'l', 'l', 'o', ' ', 'W', 'o', 'r', 'l', 'd', '\n']
        } else if n != 1 && lines.len() >= 3 {
            let a = string_to_int(lines[1]);
            let b = string_to_int(lines[2]);
            int_to_string(a + b) + seq!['\n']
        } else {
            seq![]
        }
    } else {
        seq![]
    }
}

spec fn split_lines_func(s: Seq<char>) -> Seq<Seq<char>> {
    split_lines_func_helper(s, 0, seq![], seq![])
}

spec fn split_lines_func_helper(s: Seq<char>, i: int, current: Seq<char>, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases s.len() - i when 0 <= i <= s.len()
{
    if i >= s.len() {
        if current.len() == 0 { acc } else { acc.push(current) }
    } else if s[i] == '\n' {
        split_lines_func_helper(s, i + 1, seq![], acc.push(current))
    } else {
        split_lines_func_helper(s, i + 1, current.push(s[i]), acc)
    }
}

spec fn string_to_int(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if s[0] == '-' {
        -string_to_int_helper(s.subrange(1, s.len() as int))
    } else {
        string_to_int_helper(s)
    }
}

spec fn string_to_int_helper(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        string_to_int_helper(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] as int - '0' as int)
    }
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n < 0 {
        seq!['-'] + int_to_string_helper(-n)
    } else {
        int_to_string_helper(n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    decreases n when n >= 0
{
    if n <= 0 {
        seq![]
    } else {
        int_to_string_helper(n / 10) + seq![(n % 10 + '0' as int) as char]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parse_int implementation with proper ghost blocks and digit conversion */
fn split_lines(input: Vec<char>) -> (result: Vec<Vec<char>>)
    ensures
        result@ == split_lines_func(input@)
{
    let mut current: Vec<char> = Vec::new();
    let mut lines: Vec<Vec<char>> = Vec::new();
    let mut index: usize = 0;
    
    while index < input.len()
        invariant
            input@.subrange(0, index as int) == flatten_seq(lines@).push_seq(current@),
            lines@.len() >= 0,
            current@.len() >= 0,
            index as int <= input@.len(),
        decreases input.len() - index
    {
        if input[index] == '\n' {
            let current_clone = current.clone();
            lines.push(current_clone);
            current = Vec::new();
        } else {
            current.push(input[index]);
        }
        index += 1;
    }
    
    if current.len() > 0 {
        lines.push(current);
    }
    
    lines
}

spec fn flatten_seq(s: Seq<Seq<char>>) -> Seq<char> {
    if s.len() == 0 {
        Seq::empty()
    } else {
        flatten_seq(s.drop_last()) + s[s.len() - 1]
    }
}

fn parse_int(s: Vec<char>) -> (result: int)
    ensures
        result == string_to_int(s@),
        result >= 0
{
    let mut n: int = 0;
    let mut index: usize = 0;
    
    while index < s.len()
        invariant
            n == string_to_int_helper(s@.subrange(0, index as int)),
            index as int <= s@.len(),
        decreases s.len() - index
    {
        let digit_char: char = s[index];
        proof {
            let digit_value: int = digit_char as int - '0' as int;
            assert(digit_value >= 0);
        }
        n = n * 10 + (digit_char as u8 - b'0') as int;
        index += 1;
    }
    
    n
}

fn int_to_string_impl(n: int) -> (result: Vec<char>)
    requires
        n >= 0,
    ensures
        result@ == int_to_string_helper(n)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut digits: Vec<char> = Vec::new();
        let mut num = n;
        
        while num > 0
            invariant
                num >= 0,
                digits@ == int_to_string_helper(n).subrange(0, int_to_string_helper(n).len() - int_to_string_helper(num).len()),
            decreases num
        {
            let digit = num % 10;
            digits.push((digit as u8 + b'0') as char);
            num = num / 10;
        }
        
        digits.reverse();
        digits
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures result@ == expected_output(stdin_input@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed main logic using proper parsing and verified conversions */
{
    let lines = split_lines(stdin_input);
    
    if lines.len() >= 1 {
        let first_line = lines[0].clone();
        let n = parse_int(first_line);
        
        if n == 1 {
            return vec!['H', 'e', 'l', 'l', 'o', ' ', 'W', 'o', 'r', 'l', 'd', '\n'];
        } else if n != 1 && lines.len() >= 3 {
            let second_line = lines[1].clone();
            let third_line = lines[2].clone();
            
            let a = parse_int(second_line);
            let b = parse_int(third_line);
            
            let sum = a + b;
            let mut result = int_to_string_impl(sum);
            result.push('\n');
            return result;
        }
    }
    
    Vec::new()
}
// </vc-code>


}

fn main() {}