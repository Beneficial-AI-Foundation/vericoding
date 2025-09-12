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
    if is_valid_integer_string(s) {
        string_to_int_helper(s, s.len() as int)
    } else {
        0
    }
}

spec fn string_to_int_helper(s: Seq<char>, pos: int) -> int
    decreases pos
{
    if pos <= 0 || pos > s.len() {
        0
    } else if pos == 1 && 0 < s.len() && '0' <= s[0] <= '9' {
        (s[0] as u32 - '0' as u32) as int
    } else if pos > 1 && 0 <= pos - 1 < s.len() && '0' <= s[pos - 1] <= '9' {
        string_to_int_helper(s, pos - 1) * 10 + (s[pos - 1] as u32 - '0' as u32) as int
    } else {
        0
    }
}

spec fn min_deletions_needed(s: Seq<char>) -> int {
    if is_valid_problem_string(s) {
        let first_greater = first_greater_from_left(s);
        let first_less_from_right = first_less_from_right(s);
        if first_greater < first_less_from_right { first_greater } else { first_less_from_right }
    } else {
        0
    }
}

spec fn first_greater_from_left(s: Seq<char>) -> int {
    if is_valid_problem_string(s) {
        first_greater_from_left_helper(s, 0)
    } else {
        s.len() as int
    }
}

spec fn first_greater_from_left_helper(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos
{
    if !is_valid_problem_string(s) || pos < 0 || pos >= s.len() {
        s.len() as int
    } else if s[pos] == '>' {
        pos
    } else {
        first_greater_from_left_helper(s, pos + 1)
    }
}

spec fn first_less_from_right(s: Seq<char>) -> int {
    if is_valid_problem_string(s) {
        first_less_from_right_helper(s, s.len() as int - 1)
    } else {
        s.len() as int
    }
}

spec fn first_less_from_right_helper(s: Seq<char>, pos: int) -> int
    decreases pos + 1
{
    if !is_valid_problem_string(s) || pos < 0 || pos >= s.len() {
        s.len() as int
    } else if s[pos] == '<' {
        s.len() as int - 1 - pos
    } else {
        first_less_from_right_helper(s, pos - 1)
    }
}

spec fn min(a: int, b: int) -> int {
    if a < b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(lines: Seq<Seq<char>>) -> (results: Seq<int>)
    requires lines.len() > 0
    requires forall|i: int| 0 <= i < lines.len() ==> is_valid_string(lines[i])
    requires is_valid_integer_string(lines[0])
    requires {
        let t = string_to_int(lines[0]);
        lines.len() >= 1 + 2 * t
    }
    requires forall|i: int| 0 <= i < string_to_int(lines[0]) ==> 
        is_valid_integer_string(lines[1 + 2*i]) && is_valid_problem_string(lines[2 + 2*i])
    ensures results.len() == string_to_int(lines[0])
    ensures forall|r: int| results.contains(r) ==> r >= 0
    ensures forall|i: int| 0 <= i < results.len() ==> 
        results[i] == min_deletions_needed(lines[2 + 2*i])
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}