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
/* helper modified by LLM (iteration 5): Corrected `unwrap_or` for `Seq<char>` and `add` type mismatch. */
fn split_lines(s: &Vec<char>) -> (result: Vec<Vec<char>>)
{
    let mut lines: Vec<Vec<char>> = Vec::new();
    let mut current_line: Vec<char> = Vec::new();
    let mut i: usize = 0;

    while i < s.len()
        invariant 
            i <= s.len(),
            lines@.add(split_lines_func_helper(s@.subrange(i as int, s.len() as int), 0, current_line@, Seq::empty())) == split_lines_func(s@),
            current_line@ == split_lines_func(s@.subrange(0, i as int)).last().unwrap_or(Seq::empty() as Seq<char>),
    {
        let c = s[i];
        if c == '\n' {
            lines.push(current_line);
            current_line = Vec::new();
        } else {
            current_line.push(c);
        }
        i = i + 1;
    }

    lines.push(current_line);
    lines
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures result@ == expected_output(stdin_input@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed integer type mismatches and `into_vec` to `to_vec`. */
{
    let lines = split_lines(&stdin_input);
    if lines.len() == 0 {
        return Vec::new();
    }

    let n_str = &lines[0];
    let n: int = string_to_int(n_str@);

    if n == (1 as int) {
        let hello_world: Vec<char> = vec!['H', 'e', 'l', 'l', 'o', ' ', 'W', 'o', 'r', 'l', 'd', '\n'];
        hello_world
    } else if n != (1 as int) && lines.len() >= 3 {
        let a = string_to_int(lines[1]@);
        let b = string_to_int(lines[2]@);
        let sum = a + b;
        let sum_str = int_to_string(sum);
        let mut result_vec = sum_str.to_vec(); // Changed into_vec to to_vec
        result_vec.push('\n');
        result_vec
    } else {
        Vec::new()
    }
}
// </vc-code>


}

fn main() {}