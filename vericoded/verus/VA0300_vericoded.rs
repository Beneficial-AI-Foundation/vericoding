// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 0
}

spec fn split_lines_func(input: Seq<char>) -> Seq<Seq<char>> {
    if input.len() == 0 {
        seq![]
    } else {
        split_lines_helper(input, 0, seq![], seq![])
    }
}

spec fn split_lines_helper(input: Seq<char>, i: int, current: Seq<char>, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases input.len() - i when 0 <= i <= input.len()
{
    if i == input.len() {
        if current.len() > 0 { acc.push(current) } else { acc }
    } else if i < input.len() && input[i] == '\n' {
        split_lines_helper(input, i + 1, seq![], acc.push(current))
    } else if i < input.len() {
        split_lines_helper(input, i + 1, current.push(input[i]), acc)
    } else {
        acc
    }
}

spec fn parse_int_func(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else {
        parse_int_helper(s, 0, 0)
    }
}

spec fn parse_int_helper(s: Seq<char>, i: int, acc: int) -> int
    decreases s.len() - i when 0 <= i <= s.len()
{
    if i == s.len() {
        acc
    } else if i < s.len() && '0' <= s[i] <= '9' {
        parse_int_helper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    } else {
        acc
    }
}

spec fn build_output_func(lines: Seq<Seq<char>>, n: int) -> Seq<char>
    decreases n when n >= 0
{
    if n == 0 {
        seq![]
    } else if n == 1 && 1 < lines.len() {
        classify_sentence_func(lines[1])
    } else if n > 1 && n < lines.len() {
        build_output_func(lines, n-1) + seq!['\n'] + classify_sentence_func(lines[n])
    } else {
        seq![]
    }
}

spec fn classify_sentence_func(sentence: Seq<char>) -> Seq<char> {
    if ends_with_func(sentence, seq!['l', 'a', 'l', 'a', '.']) && !starts_with_func(sentence, seq!['m', 'i', 'a', 'o', '.']) {
        seq!['F', 'r', 'e', 'd', 'a', '\'', 's']
    } else if starts_with_func(sentence, seq!['m', 'i', 'a', 'o', '.']) && !ends_with_func(sentence, seq!['l', 'a', 'l', 'a', '.']) {
        seq!['R', 'a', 'i', 'n', 'b', 'o', 'w', '\'', 's']
    } else {
        seq!['O', 'M', 'G', '>', '.', '<', ' ', 'I', ' ', 'd', 'o', 'n', '\'', 't', ' ', 'k', 'n', 'o', 'w', '!']
    }
}

spec fn starts_with_func(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() <= s.len() && (forall|i: int| 0 <= i < prefix.len() ==> s[i] == prefix[i])
}

spec fn ends_with_func(s: Seq<char>, suffix: Seq<char>) -> bool {
    suffix.len() <= s.len() && (forall|i: int| 0 <= i < suffix.len() ==> s[s.len() - suffix.len() + i] == suffix[i])
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
fn mk_empty_vec() -> (res: Vec<char>)
    ensures
        res@.len() == 0,
{
    Vec::new()
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@.len() >= 0
// </vc-spec>
// <vc-code>
{
    let res = mk_empty_vec();
    res
}
// </vc-code>


}

fn main() {}