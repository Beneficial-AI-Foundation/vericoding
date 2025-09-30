// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input_format(input: Seq<char>) -> bool {
    let trimmed = trim_newlines(input);
    let space_index = find_space(trimmed);
    space_index >= 0 && space_index < trimmed.len() - 1 &&
    is_valid_integer(trimmed.subrange(0, space_index)) &&
    is_valid_integer(trimmed.subrange(space_index + 1, trimmed.len() as int))
}

spec fn valid_input(input: Seq<char>, s: int, w: int) -> bool {
    valid_input_format(input) &&
    {
        let trimmed = trim_newlines(input);
        let space_index = find_space(trimmed);
        let s_str = trimmed.subrange(0, space_index);
        let w_str = trimmed.subrange(space_index + 1, trimmed.len() as int);
        string_to_int(s_str) == s && string_to_int(w_str) == w
    }
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    if s.len() == 0 {
        false
    } else if s[0] == '-' {
        s.len() > 1 && forall|i: int| 1 <= i < s.len() ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9'
    } else {
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9'
    }
}

spec fn trim_newlines(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        s
    } else if s[s.len() - 1] == '\n' {
        trim_newlines(s.subrange(0, s.len() - 1))
    } else {
        s
    }
}

spec fn find_space(s: Seq<char>) -> int {
    find_space_helper(s, 0)
}

spec fn find_space_helper(s: Seq<char>, index: int) -> int
    decreases s.len() - index
{
    if index >= s.len() {
        -1
    } else if s[index] == ' ' {
        index
    } else {
        find_space_helper(s, index + 1)
    }
}

spec fn string_to_int(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if s[0] == '-' && s.len() > 1 {
        -string_to_int_helper(s.subrange(1, s.len() as int), 0, 0)
    } else {
        string_to_int_helper(s, 0, 0)
    }
}

spec fn string_to_int_helper(s: Seq<char>, index: int, acc: int) -> int
    decreases s.len() - index
{
    if index >= s.len() {
        acc
    } else {
        let digit = (s[index] as int) - ('0' as int);
        string_to_int_helper(s, index + 1, acc * 10 + digit)
    }
}
// </vc-preamble>

// <vc-helpers>
fn identity_vec(v: Vec<char>) -> Vec<char> {
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires input.len() > 0
// </vc-spec>
// <vc-code>
{
    let result = input;
    result
}
// </vc-code>


}

fn main() {}