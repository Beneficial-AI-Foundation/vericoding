// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_parseable(input: &str) -> bool {
    let parts = split_string_pure(input);
    parts.len() >= 4
}

spec fn all_parts_are_integers(input: &str) -> bool {
    let parts = split_string_pure(input);
    parts.len() >= 4 &&
    is_valid_integer(&parts[0]) &&
    is_valid_integer(&parts[1]) &&
    is_valid_integer(&parts[2]) &&
    is_valid_integer(&parts[3])
}

spec fn is_valid_integer(s: &str) -> bool {
    s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> ('0' <= s[i] && s[i] <= '9') || (i == 0 && s[i] == '-'))
}

spec fn valid_parse(input: &str, a: int, b: int, c: int, d: int) -> bool {
    let parts = split_string_pure(input);
    parts.len() >= 4 && 
    is_valid_integer(&parts[0]) &&
    is_valid_integer(&parts[1]) &&
    is_valid_integer(&parts[2]) &&
    is_valid_integer(&parts[3]) &&
    string_to_int_pure(&parts[0]) == a &&
    string_to_int_pure(&parts[1]) == b &&
    string_to_int_pure(&parts[2]) == c &&
    string_to_int_pure(&parts[3]) == d
}

spec fn split_string_pure(s: &str) -> Seq<String> {
    split_string_helper(s, 0, String::new(), Seq::empty())
}

spec fn split_string_helper(s: &str, i: int, current: String, acc: Seq<String>) -> Seq<String>
    decreases s.len() - i
{
    if i == s.len() {
        if current.len() > 0 { acc.push(current) } else { acc }
    } else if s[i] == ' ' || s[i] == '\n' || s[i] == '\t' {
        if current.len() > 0 {
            split_string_helper(s, i + 1, String::new(), acc.push(current))
        } else {
            split_string_helper(s, i + 1, String::new(), acc)
        }
    } else {
        split_string_helper(s, i + 1, current + s[i].to_string(), acc)
    }
}

spec fn string_to_int_pure(s: &str) -> int {
    if s.len() > 0 && s[0] == '-' {
        -string_to_int_helper_unsigned(s, 1, 0)
    } else {
        string_to_int_helper_unsigned(s, 0, 0)
    }
}

spec fn string_to_int_helper_unsigned(s: &str, i: int, acc: int) -> int
    decreases s.len() - i
{
    if i == s.len() {
        acc
    } else if '0' <= s[i] && s[i] <= '9' {
        string_to_int_helper_unsigned(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    } else {
        acc
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    ensures 
        (forall|a: int, b: int, c: int, d: int| 
            valid_parse(input, a, b, c, d) ==> 
            (result == "Left\n" <==> a + b > c + d) &&
            (result == "Right\n" <==> a + b < c + d) &&
            (result == "Balanced\n" <==> a + b == c + d)),
    ensures 
        valid_parseable(input) && all_parts_are_integers(input) ==> 
        (result == "Left\n" || result == "Right\n" || result == "Balanced\n"),
    ensures 
        (!valid_parseable(input) || !all_parts_are_integers(input)) ==> result == ""
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}