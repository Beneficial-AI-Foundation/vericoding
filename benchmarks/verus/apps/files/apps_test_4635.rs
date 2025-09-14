// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    (exists|lines: Seq<Seq<char>>| lines == split_by_newline(input) &&
     lines.len() >= 1 &&
     is_valid_integer(lines[0]) &&
     string_to_int_val(lines[0]) >= 0 &&
     lines.len() >= string_to_int_val(lines[0]) + 1 &&
     (forall|i: int| 1 <= i <= string_to_int_val(lines[0]) && i < lines.len() ==> valid_test_case_line(lines[i])))
}

spec fn valid_test_case_line(line: Seq<char>) -> bool {
    exists|parts: Seq<Seq<char>>| (parts == split_by_space(line) &&
                    parts.len() >= 2 &&
                    is_valid_integer(parts[0]) &&
                    is_valid_integer(parts[1]) &&
                    string_to_int_val(parts[0]) > 0 &&
                    string_to_int_val(parts[1]) > 0 &&
                    string_to_int_val(parts[1]) <= 26)
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 &&
    (s.len() == 1 || s[0] != '0' || s == seq!['0']) &&
    forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9'
}

spec fn string_to_int_val(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else
    if s.len() == 1 { (s[0] as int) - 48 } else {
        string_to_int_val(s.subrange(0, s.len() - 1)) * 10 + ((s[s.len() - 1] as int) - 48)
    }
}

spec fn cyclic_pattern_correct(n: int, k: int, output: Seq<char>) -> bool {
    n > 0 && k > 0 && k <= 26 ==>
    (output.len() == n &&
     (forall|j: int| 0 <= j < n ==> output[j] == ((j % k) + 97) as char))
}

spec fn split_by_newline(input: Seq<char>) -> Seq<Seq<char>> {
    seq![input]
}

spec fn split_by_space(line: Seq<char>) -> Seq<Seq<char>> {
    seq![line]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(stdin_input)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}