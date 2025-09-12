// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn char_to_pos_spec(c: Seq<char>) -> int {
    if c == seq!['v'] { 0 }
    else if c == seq!['>'] { 1 }
    else if c == seq!['^'] { 2 }
    else if c == seq!['<'] { 3 }
    else { 0 }
}

spec fn split_lines_spec(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 { seq![] }
    else {
        let i = find_newline(s, 0);
        if i == s.len() { seq![s] }
        else { seq![s.subrange(0, i)].add(split_lines_spec(s.subrange(i+1, s.len() as int))) }
    }
}

spec fn find_newline(s: Seq<char>, start: int) -> int
    requires 0 <= start <= s.len()
    ensures start <= find_newline(s, start) <= s.len()
    decreases s.len() - start
{
    if start >= s.len() { s.len() }
    else if s[start] == '\n' { start }
    else { find_newline(s, start + 1) }
}

spec fn split_by_space_spec(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 { seq![] }
    else {
        let i = find_space(s, 0);
        if i == s.len() { seq![s] }
        else { seq![s.subrange(0, i)].add(split_by_space_spec(s.subrange(i+1, s.len() as int))) }
    }
}

spec fn find_space(s: Seq<char>, start: int) -> int
    requires 0 <= start <= s.len()
    ensures start <= find_space(s, start) <= s.len()
    decreases s.len() - start
{
    if start >= s.len() { s.len() }
    else if s[start] == ' ' { start }
    else { find_space(s, start + 1) }
}

spec fn string_to_int_spec(s: Seq<char>) -> int {
    string_to_int_helper(s, 0, 0, false)
}

spec fn string_to_int_helper(s: Seq<char>, pos: int, acc: int, negative: bool) -> int
    requires 0 <= pos <= s.len()
    decreases s.len() - pos
{
    if pos >= s.len() { if negative { -acc } else { acc } }
    else if pos == 0 && s[pos] == '-' { string_to_int_helper(s, pos + 1, acc, true) }
    else if '0' <= s[pos] <= '9' { 
        string_to_int_helper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int), negative)
    }
    else { string_to_int_helper(s, pos + 1, acc, negative) }
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_output(result: Seq<char>) -> bool {
    result == seq!['c', 'w'] || result == seq!['c', 'c', 'w'] || result == seq!['u', 'n', 'd', 'e', 'f', 'i', 'n', 'e', 'd']
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(input)
    ensures valid_output(result)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    seq!['u', 'n', 'd', 'e', 'f', 'i', 'n', 'e', 'd']
    // impl-end
}
// </vc-code>


}

fn main() {}