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
spec fn convert_vec_seq_to_seq_seq(vecs: Seq<Vec<char>>) -> Seq<Seq<char>> {
    vecs.map(|v: Vec<char>| v@)
}

/* helper modified by LLM (iteration 4): fixed map function to return tuple */
fn split_lines_exec(s: &Vec<char>) -> (lines: Vec<Vec<char>>)
    ensures lines@ == split_lines_func(s@)
{
    let mut i = 0;
    let mut lines: Vec<Vec<char>> = Vec::new();
    let mut current: Vec<char> = Vec::new();
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            split_lines_func(s@) == split_lines_func_helper(s@, i as int, current@, convert_vec_seq_to_seq_seq(lines@))
        decreases s.len() - i
    {
        if s[i] == '
' {
            lines.push(current);
            current = Vec::new();
        } else {
            current.push(s[i]);
        }
        i += 1;
    }
    if current.len() > 0 {
        lines.push(current);
    }
    lines
}

/* helper modified by LLM (iteration 3): changed parameter to slice */
fn string_to_int_exec(s: &Vec<char>) -> (n: i32)
    ensures (n as int) == string_to_int(s@)
{
    if s.len() == 0 {
        0
    } else if s[0] == '-' {
        let abs = string_to_int_helper_exec(&s[1..]);
        -abs
    } else {
        string_to_int_helper_exec(s)
    }
}

/* helper modified by LLM (iteration 3): changed parameter to slice and fixed invariant */
fn string_to_int_helper_exec(s: &[char]) -> (n: i32)
    ensures (n as int) == string_to_int_helper(s@)
{
    let mut i = 0;
    let mut n = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            (n as int) == string_to_int_helper(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        let digit = (s[i] as u8) - ('0' as u8);
        n = n * 10 + (digit as i32);
        i += 1;
    }
    n
}

/* helper modified by LLM (iteration 2): changed to use i32 for arithmetic */
fn int_to_string_exec(n: i32) -> (s: Vec<char>)
    ensures s@ == int_to_string(n as int)
{
    if n == 0 {
        vec!['0']
    } else if n < 0 {
        let abs_str = int_to_string_helper_exec(-n);
        let mut s = Vec::new();
        s.push('-');
        s.extend(abs_str);
        s
    } else {
        int_to_string_helper_exec(n)
    }
}

/* helper modified by LLM (iteration 2): changed to use i32 for arithmetic */
fn int_to_string_helper_exec(n: i32) -> (s: Vec<char>)
    requires n > 0
    ensures s@ == int_to_string_helper(n as int)
    decreases n as int
{
    let higher = n / 10;
    let mut s = if higher > 0 {
        int_to_string_helper_exec(higher)
    } else {
        Vec::new()
    };
    let last_digit = (n % 10) as u8;
    s.push((last_digit + ('0' as u8)) as char);
    s
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures result@ == expected_output(stdin_input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed type conversions */
    let lines = split_lines_exec(&stdin_input);
    if lines.len() >= 1 {
        let n = string_to_int_exec(&lines[0]);
        if n == 1 {
            vec!['H', 'e', 'l', 'l', 'o', ' ', 'W', 'o', 'r', 'l', 'd', '\n']
        } else if n != 1 && lines.len() >= 3 {
            let a = string_to_int_exec(&lines[1]);
            let b = string_to_int_exec(&lines[2]);
            let sum = a + b;
            let sum_str = int_to_string_exec(sum);
            let mut result = sum_str;
            result.push('\n');
            result
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    }
}
// </vc-code>


}

fn main() {}