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

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures result@ == expected_output(stdin_input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed type annotation in invariant conditional expression */
    let lines = split_lines(&stdin_input);
    if lines.len() >= 1 {
        let n = parse_int(&lines[0]);
        if n == 1 {
            return vec!['H', 'e', 'l', 'l', 'o', ' ', 'W', 'o', 'r', 'l', 'd', '\n'];
        } else if n != 1 && lines.len() >= 3 {
            let a = parse_int(&lines[1]);
            let b = parse_int(&lines[2]);
            let sum = a + b;
            let mut result = int_to_vec(sum);
            result.push('\n');
            return result;
        }
    }
    vec![]
}

fn split_lines(s: &Vec<char>) -> (lines: Vec<Vec<char>>)
    ensures lines@.len() == split_lines_func(s@).len(),
            forall|i: int| 0 <= i < lines@.len() ==> lines@[i] == split_lines_func(s@)[i]
{
    let mut lines = Vec::new();
    let mut current = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            lines@.len() + (if current@.len() == 0 { 0int } else { 1int }) <= split_lines_func(s@).len(),
            forall|j: int| 0 <= j < lines@.len() ==> lines@[j] == split_lines_func(s@)[j]
    {
        if s[i] == '\n' {
            lines.push(current);
            current = Vec::new();
        } else {
            current.push(s[i]);
        }
        i = i + 1;
    }
    
    if current.len() > 0 {
        lines.push(current);
    }
    
    lines
}

fn parse_int(s: &Vec<char>) -> (n: i32)
    ensures n as int == string_to_int(s@)
{
    if s.len() == 0 {
        return 0;
    }
    
    if s[0] == '-' {
        let mut result: i32 = 0;
        let mut i: usize = 1;
        while i < s.len()
            invariant
                1 <= i <= s.len(),
                result >= 0
        {
            result = result * 10 + (s[i] as i32 - '0' as i32);
            i = i + 1;
        }
        return -result;
    } else {
        let mut result: i32 = 0;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                result >= 0
        {
            result = result * 10 + (s[i] as i32 - '0' as i32);
            i = i + 1;
        }
        return result;
    }
}

fn int_to_vec(n: i32) -> (v: Vec<char>)
    ensures v@ == int_to_string(n as int)
{
    if n == 0 {
        return vec!['0'];
    } else if n < 0 {
        let mut v = vec!['-'];
        let positive = int_to_vec_helper(-n);
        let mut i: usize = 0;
        while i < positive.len()
            invariant
                0 <= i <= positive.len(),
                v@.len() == 1 + i as int,
                v@[0] == '-',
                forall|j: int| 0 < j <= i as int ==> v@[j] == positive@[j-1]
        {
            v.push(positive[i]);
            i = i + 1;
        }
        return v;
    } else {
        return int_to_vec_helper(n);
    }
}

fn int_to_vec_helper(n: i32) -> (v: Vec<char>)
    requires n > 0
    ensures v@ == int_to_string_helper(n as int)
{
    let mut v = Vec::new();
    let mut num = n;
    let mut digits = Vec::new();
    
    while num > 0
        invariant
            num >= 0
    {
        let digit = ((num % 10) as u8 + b'0') as char;
        digits.push(digit);
        num = num / 10;
    }
    
    let mut i = digits.len();
    while i > 0
        invariant
            0 <= i <= digits.len(),
            v@.len() == (digits.len() - i) as int
    {
        i = i - 1;
        v.push(digits[i]);
    }
    
    v
}
// </vc-code>


}

fn main() {}