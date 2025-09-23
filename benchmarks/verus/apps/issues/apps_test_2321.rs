// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_string(s: Seq<char>) -> bool {
    s.len() > 0
}

spec fn is_valid_problem_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == '>' || #[trigger] s[i] == '<'
}

spec fn is_valid_integer_string(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> '0' <= #[trigger] s[i] <= '9'
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
    } else if !forall|i: int| 0 <= i < pos ==> '0' <= #[trigger] s[i] <= '9' {
        0
    } else if pos == 0 { 
        0 
    } else { 
        string_to_int_helper(s, pos - 1) * 10 + (s[pos - 1] as int - '0' as int) 
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
    if !is_valid_problem_string(s) || pos < 0 || pos > s.len() {
        s.len() as int
    } else if pos >= s.len() { 
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
    if !is_valid_problem_string(s) || pos >= s.len() || pos < -1 {
        s.len() as int
    } else if pos < 0 { 
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
fn solve(lines: Vec<Vec<char>>) -> (results: Vec<i8>)
    requires 
        lines@.len() > 0,
        forall|i: int| 0 <= i < lines@.len() ==> is_valid_string(lines@[i]),
        is_valid_integer_string(lines@[0]),
        ({let t = string_to_int(lines@[0]); lines@.len() >= 1 + 2 * t}),
        forall|i: int| 0 <= i < string_to_int(lines@[0]) ==> 
            is_valid_integer_string(lines@[1 + 2*i]) && is_valid_problem_string(lines@[2 + 2*i])
    ensures 
        results@.len() == string_to_int(lines@[0]),
        forall|r: i8| #[trigger] results@.contains(r) ==> r as int >= 0,
        forall|i: int| 0 <= i < results@.len() ==> 
            #[trigger] results@[i] as int == min_deletions_needed(lines@[2 + 2*i])
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