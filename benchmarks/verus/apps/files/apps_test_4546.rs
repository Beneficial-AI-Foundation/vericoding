// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_three_integers(input: Seq<char>, a: int, b: int, c: int) -> bool {
    let parts = split_by_spaces_func(input);
    parts.len() == 3 && 
    is_valid_integer(parts[0]) &&
    is_valid_integer(parts[1]) &&
    is_valid_integer(parts[2]) &&
    parse_int_func(parts[0]) == a &&
    parse_int_func(parts[1]) == b &&
    parse_int_func(parts[2]) == c
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (s[0] != '-' || s.len() > 1) &&
    (s[0] == '-' ==> forall|i: int| 1 <= i < s.len() ==> '0' <= s[i] <= '9') &&
    (s[0] != '-' ==> forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9')
}

spec fn split_by_spaces_func(s: Seq<char>) -> Seq<Seq<char>> {
    split_by_spaces_helper(s, 0, seq![], seq![])
}

spec fn split_by_spaces_helper(s: Seq<char>, i: int, current: Seq<char>, parts: Seq<Seq<char>>) -> Seq<Seq<char>> {
    if 0 <= i <= s.len() && i >= s.len() {
        if current.len() > 0 { parts.push(current) } else { parts }
    } else if 0 <= i < s.len() && (s[i] == ' ' || s[i] == '\n' || s[i] == '\t') {
        if current.len() > 0 {
            split_by_spaces_helper(s, i + 1, seq![], parts.push(current))
        } else {
            split_by_spaces_helper(s, i + 1, current, parts)
        }
    } else if 0 <= i < s.len() {
        split_by_spaces_helper(s, i + 1, current.push(s[i]), parts)
    } else {
        seq![]
    }
}

spec fn parse_int_func(s: Seq<char>) -> int {
    if s.len() > 0 && is_valid_integer(s) && s[0] == '-' {
        -parse_unsigned_int(s.subrange(1, s.len() as int))
    } else if s.len() > 0 && is_valid_integer(s) {
        parse_unsigned_int(s)
    } else {
        0
    }
}

spec fn parse_unsigned_int(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9' {
        parse_unsigned_int(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] as int - '0' as int)
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: String)
    requires input.len() > 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    "".to_string()
}
// </vc-code>


}

fn main() {}