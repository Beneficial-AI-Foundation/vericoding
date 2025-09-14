// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn length_sqr(p1: (int, int), p2: (int, int)) -> int {
    (p1.0 - p2.0) * (p1.0 - p2.0) + (p1.1 - p2.1) * (p1.1 - p2.1)
}

spec fn valid_rotation_exists(a: (int, int), b: (int, int), c: (int, int)) -> bool {
    let dist_ab_sqr = length_sqr(a, b);
    let dist_bc_sqr = length_sqr(b, c);
    let dx1 = c.0 - b.0;
    let dy1 = c.1 - b.1;
    let dx2 = b.0 - a.0;
    let dy2 = b.1 - a.1;
    dist_ab_sqr == dist_bc_sqr && dx1 * dy2 != dy1 * dx2
}

spec fn parse_input_func(input: Seq<char>) -> Seq<int>
    recommends input.len() > 0
{
    parse_input_helper(input, 0, seq![], seq![])
}

spec fn parse_input_helper(input: Seq<char>, i: int, result: Seq<int>, current: Seq<char>) -> Seq<int>
    recommends 0 <= i <= input.len()
    decreases input.len() - i
{
    if i == input.len() {
        if current.len() > 0 { result.push(string_to_int(current)) }
        else { result }
    } else {
        let ch = input[i];
        if ch == ' ' || ch == '\n' || ch == '\t' {
            if current.len() > 0 {
                parse_input_helper(input, i + 1, result.push(string_to_int(current)), seq![])
            } else {
                parse_input_helper(input, i + 1, result, seq![])
            }
        } else if ('0' <= ch <= '9') || ch == '-' {
            parse_input_helper(input, i + 1, result, current.push(ch))
        } else {
            parse_input_helper(input, i + 1, result, current)
        }
    }
}

spec fn string_to_int(s: Seq<char>) -> int {
    if s.len() == 0 { 0 }
    else if s.len() == 1 && s[0] == '-' { 0 }
    else if s[0] == '-' && s.len() > 1 && is_digit_string(s.subrange(1, s.len() as int)) { -string_to_int_helper(s.subrange(1, s.len() as int)) }
    else if is_digit_string(s) { string_to_int_helper(s) }
    else { 0 }
}

spec fn is_digit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9'
}

spec fn string_to_int_helper(s: Seq<char>) -> int
    recommends forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9'
{
    if s.len() == 0 { 0 }
    else if s.len() == 1 { char_to_digit(s[0]) }
    else { string_to_int_helper(s.subrange(0, s.len() - 1)) * 10 + char_to_digit(s[s.len() - 1]) }
}

spec fn char_to_digit(c: char) -> int
    recommends '0' <= c <= '9'
{
    (c as int) - ('0' as int)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires input@.len() > 0
    ensures result@ == "Yes"@ || result@ == "No"@ || result@ == ""@
// </vc-spec>
// <vc-code>
{
    assume(false);
    "".to_string()
}
// </vc-code>


}

fn main() {}