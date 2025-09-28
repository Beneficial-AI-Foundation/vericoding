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
/* helper modified by LLM (iteration 5): fixed type mismatch by using @ operator to compare sequences */
fn split_lines(s: &Vec<char>) -> (result: Vec<Vec<char>>)
    ensures
        result@.len() == split_lines_func(s@).len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@ == split_lines_func(s@)[i],
{
    let mut lines = Vec::new();
    let mut current_line = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            lines@.len() >= 0,
    {
        if s[i] == '\n' {
            lines.push(current_line);
            current_line = Vec::new();
        } else {
            current_line.push(s[i]);
        }
        i += 1;
    }
    
    if current_line.len() > 0 {
        lines.push(current_line);
    }
    
    lines
}

fn parse_int(s: &Vec<char>) -> (result: i64)
    ensures result == string_to_int(s@)
{
    if s.len() == 0 {
        return 0;
    }
    
    let mut result = 0i64;
    let mut i = 0;
    let mut negative = false;
    
    if s[0] == '-' {
        negative = true;
        i = 1;
    }
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result >= 0,
    {
        let digit_char = s[i];
        let digit_u8 = digit_char as u8 - b'0';
        result = result * 10 + digit_u8 as i64;
        i += 1;
    }
    
    if negative {
        -result
    } else {
        result
    }
}

fn int_to_vec(n: i64) -> (result: Vec<char>)
    ensures result@ == int_to_string(n as int)
{
    if n == 0 {
        let mut v = Vec::new();
        v.push('0');
        return v;
    }
    
    let mut result = Vec::new();
    let mut num = if n < 0 { -n } else { n };
    
    while num > 0
        invariant num >= 0
    {
        let digit = (num % 10) as u8 + b'0';
        result.push(digit as char);
        num = num / 10;
    }
    
    if n < 0 {
        result.push('-');
    }
    
    // Reverse the result
    let mut i = 0;
    let len = result.len();
    while i < len / 2
        invariant 0 <= i <= len / 2
    {
        let temp = result[i];
        result.set(i, result[len - 1 - i]);
        result.set(len - 1 - i, temp);
        i += 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures result@ == expected_output(stdin_input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch by using @ operator for Vec to Seq conversion */
    let lines = split_lines(&stdin_input);
    
    let result = if lines.len() >= 1 {
        let n = parse_int(&lines[0]);
        
        if n == 1 {
            let mut hello_result = Vec::new();
            hello_result.push('H');
            hello_result.push('e');
            hello_result.push('l');
            hello_result.push('l');
            hello_result.push('o');
            hello_result.push(' ');
            hello_result.push('W');
            hello_result.push('o');
            hello_result.push('r');
            hello_result.push('l');
            hello_result.push('d');
            hello_result.push('\n');
            hello_result
        } else if lines.len() >= 3 {
            let a = parse_int(&lines[1]);
            let b = parse_int(&lines[2]);
            let sum = a + b;
            let mut sum_result = int_to_vec(sum);
            sum_result.push('\n');
            sum_result
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    };
    
    result
}
// </vc-code>


}

fn main() {}