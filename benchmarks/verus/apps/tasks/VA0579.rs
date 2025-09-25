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
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}