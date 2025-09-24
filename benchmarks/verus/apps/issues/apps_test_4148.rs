// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>>
    requires input.len() > 0
{
    let newline_pos = find_newline(input, 0);
    if newline_pos == -1 {
        seq![input]
    } else if newline_pos >= 0 && newline_pos < input.len() {
        if newline_pos + 1 >= input.len() {
            seq![input.subrange(0, newline_pos), seq![]]
        } else {
            seq![input.subrange(0, newline_pos), input.subrange(newline_pos + 1, input.len() as int)]
        }
    } else {
        seq![input]
    }
}

spec fn find_newline(input: Seq<char>, start: int) -> int
    requires 0 <= start <= input.len()
    ensures find_newline(input, start) == -1 || (0 <= find_newline(input, start) < input.len())
    decreases input.len() - start
{
    if start >= input.len() {
        -1
    } else if input[start] == '\n' {
        start
    } else {
        find_newline(input, start + 1)
    }
}

spec fn is_valid_number(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9'
}

spec fn string_to_nat(s: Seq<char>) -> nat
    requires is_valid_number(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        (s[0] as int - '0' as int) as nat
    } else {
        (s[0] as int - '0' as int) as nat * 10 + string_to_nat(s.subrange(1, s.len() as int))
    }
}

spec fn caesar_shift(s: Seq<char>, n: nat) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let shifted_val = (s[0] as int - 'A' as int + n) % 26;
        let shifted_char = ('A' as int + shifted_val) as char;
        seq![shifted_char].add(caesar_shift(s.subrange(1, s.len() as int), n))
    }
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    (exists|i: int| 0 <= i < input.len() && input[i] == '\n') &&
    {
        let lines = split_lines(input);
        lines.len() >= 2 &&
        is_valid_number(lines[0]) &&
        string_to_nat(lines[0]) <= 26 &&
        lines[1].len() >= 1 && lines[1].len() <= 10000 &&
        (forall|j: int| 0 <= j < lines[1].len() ==> 'A' <= lines[1][j] <= 'Z')
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(input)
    ensures ({
        let lines = split_lines(input);
        let n = string_to_nat(lines[0]);
        let s = lines[1];
        result == caesar_shift(s, n).add(seq!['\n'])
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}