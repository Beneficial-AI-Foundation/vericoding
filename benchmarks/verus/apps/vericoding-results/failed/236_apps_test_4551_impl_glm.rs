// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_parseable(input: Seq<char>) -> bool {
    let parts = split_string_pure(input);
    parts.len() >= 4
}

spec fn all_parts_are_integers(input: Seq<char>) -> bool {
    let parts = split_string_pure(input);
    parts.len() >= 4 &&
    is_valid_integer(parts[0]) &&
    is_valid_integer(parts[1]) &&
    is_valid_integer(parts[2]) &&
    is_valid_integer(parts[3])
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> ('0' <= s[i] <= '9') || (i == 0 && s[i] == '-'))
}

spec fn valid_parse(input: Seq<char>, a: int, b: int, c: int, d: int) -> bool {
    let parts = split_string_pure(input);
    parts.len() >= 4 && 
    is_valid_integer(parts[0]) &&
    is_valid_integer(parts[1]) &&
    is_valid_integer(parts[2]) &&
    is_valid_integer(parts[3]) &&
    string_to_int_pure(parts[0]) == a &&
    string_to_int_pure(parts[1]) == b &&
    string_to_int_pure(parts[2]) == c &&
    string_to_int_pure(parts[3]) == d
}

spec fn split_string_pure(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    split_string_helper(s, 0, seq![], seq![])
}

spec fn split_string_helper(s: Seq<char>, i: int, current: Seq<char>, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases s.len() - i
{
    if i < 0 || i > s.len() {
        acc
    } else if i == s.len() {
        if current.len() > 0 { acc.push(current) } else { acc }
    } else if s[i] == ' ' || s[i] == '\n' || s[i] == '\t' {
        if current.len() > 0 {
            split_string_helper(s, i + 1, seq![], acc.push(current))
        } else {
            split_string_helper(s, i + 1, seq![], acc)
        }
    } else {
        split_string_helper(s, i + 1, current.push(s[i]), acc)
    }
}

spec fn string_to_int_pure(s: Seq<char>) -> int {
    if !is_valid_integer(s) {
        0
    } else if s.len() > 0 && s[0] == '-' {
        -string_to_int_helper_unsigned(s, 1, 0)
    } else {
        string_to_int_helper_unsigned(s, 0, 0)
    }
}

spec fn string_to_int_helper_unsigned(s: Seq<char>, i: int, acc: int) -> int
    decreases s.len() - i
{
    if i < 0 || i >= s.len() {
        acc
    } else if '0' <= s[i] <= '9' {
        string_to_int_helper_unsigned(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    } else {
        acc
    }
}
// </vc-preamble>

// <vc-helpers>
fn parse_int(s: &str) -> (result: i64)
    requires
        is_valid_integer(s@)
    ensures
        result as int == string_to_int_pure(s@)
{
    let mut result: i64 = 0;
    let mut i = 0;
    let negative = if s.len() > 0 && s.as_bytes()[0] as char == '-' {
        i = 1;
        true
    } else {
        false
    };
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            if negative {
                result as int == -string_to_int_helper_unsigned(s@, i as int, 0)
            } else {
                result as int == string_to_int_helper_unsigned(s@, i as int, 0)
            }
        decreases s.len() - i
    {
        let c = s.as_bytes()[i] as char;
        if '0' <= c <= '9' {
            result = result * 10 + (c as i64 - '0' as i64);
        }
        i += 1;
    }
    
    if negative {
        -result
    } else {
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    ensures 
        (forall|a: int, b: int, c: int, d: int| 
            valid_parse(input@, a, b, c, d) ==> 
            ((result@ == "Left\n"@) <==> (a + b > c + d)) &&
            ((result@ == "Right\n"@) <==> (a + b < c + d)) &&
            ((result@ == "Balanced\n"@) <==> (a + b == c + d))) &&
        (valid_parseable(input@) && all_parts_are_integers(input@) ==> 
            (result@ == "Left\n"@ || result@ == "Right\n"@ || result@ == "Balanced\n"@)) &&
        ((!valid_parseable(input@) || !all_parts_are_integers(input@)) ==> result@ == ""@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use i64 for parsed integers and arithmetic */
    let parts = parse_string(input);
    
    if parts.len() < 4 {
        return "".to_string();
    }
    
    let a = parse_int(&parts[0]);
    let b = parse_int(&parts[1]);
    let c = parse_int(&parts[2]);
    let d = parse_int(&parts[3]);
    
    let left_sum = a + b;
    let right_sum = c + d;
    
    if left_sum > right_sum {
        "Left\n".to_string()
    } else if left_sum < right_sum {
        "Right\n".to_string()
    } else {
        "Balanced\n".to_string()
    }
}
// </vc-code>


}

fn main() {}