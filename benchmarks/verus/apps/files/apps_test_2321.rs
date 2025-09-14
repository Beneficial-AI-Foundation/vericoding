// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_string(s: Seq<char>) -> bool {
    s.len() > 0
}

spec fn is_valid_problem_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '>' || s[i] == '<'
}

spec fn is_valid_integer_string(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9'
}

spec fn string_to_int(s: Seq<char>) -> int {
    string_to_int_helper(s, s.len() as int)
}

spec fn string_to_int_helper(s: Seq<char>, pos: int) -> int
    decreases pos
{
    if pos == 0 { 0 }
    else { string_to_int_helper(s, pos - 1) * 10 + (s[pos - 1] as int - '0' as int) }
}

spec fn min_deletions_needed(s: Seq<char>) -> int {
    let first_greater = first_greater_from_left(s);
    let first_less_from_right = first_less_from_right(s);
    if first_greater < first_less_from_right { first_greater } else { first_less_from_right }
}

spec fn first_greater_from_left(s: Seq<char>) -> int {
    first_greater_from_left_helper(s, 0)
}

spec fn first_greater_from_left_helper(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos
{
    if pos >= s.len() { s.len() as int }
    else if s[pos] == '>' { pos }
    else { first_greater_from_left_helper(s, pos + 1) }
}

spec fn first_less_from_right(s: Seq<char>) -> int {
    first_less_from_right_helper(s, s.len() as int - 1)
}

spec fn first_less_from_right_helper(s: Seq<char>, pos: int) -> int
    decreases pos + 1
{
    if pos < 0 { s.len() as int }
    else if s[pos] == '<' { s.len() as int - 1 - pos }
    else { first_less_from_right_helper(s, pos - 1) }
}

spec fn min(a: int, b: int) -> int {
    if a < b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(lines: Seq<Seq<char>>) -> (results: Seq<int>)
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