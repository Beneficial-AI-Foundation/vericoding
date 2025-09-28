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
/* helper modified by LLM (iteration 4): ASCII whitespace check using numeric u8 constants to avoid unsupported byte literals */
fn is_ascii_whitespace(b: u8) -> (r: bool)
{
    b == 32u8 || b == 10u8 || b == 9u8
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
    /* code modified by LLM (iteration 4): parse integers using numeric u8 constants instead of byte literals */
    let bytes = input.as_bytes();
    let n = bytes.len();
    let mut i: usize = 0;

    let mut a: i64 = 0;
    let mut b: i64 = 0;
    let mut c: i64 = 0;
    let mut d: i64 = 0;
    let mut count: usize = 0;

    while i < n && count < 4 {
        while i < n {
            let br = bytes[i];
            if br == 32u8 || br == 10u8 || br == 9u8 {
                i += 1;
            } else {
                break;
            }
        }
        if i >= n { break; }

        let mut neg = false;
        if bytes[i] == 45u8 {
            neg = true;
            i += 1;
        }

        if i >= n { return "".to_string(); }
        let mut acc: i64 = 0;
        let mut has_digit = false;
        while i < n {
            let br = bytes[i];
            if br >= 48u8 && br <= 57u8 {
                has_digit = true;
                acc = acc * 10 + ((br - 48u8) as i64);
                i += 1;
            } else {
                break;
            }
        }
        if !has_digit { return "".to_string(); }
        let val = if neg { -acc } else { acc };
        if count == 0 {
            a = val;
        } else if count == 1 {
            b = val;
        } else if count == 2 {
            c = val;
        } else {
            d = val;
        }
        count += 1;
    }

    if count < 4 {
        return "".to_string();
    }

    let left = a + b;
    let right = c + d;
    if left > right {
        "Left\n".to_string()
    } else if left < right {
        "Right\n".to_string()
    } else {
        "Balanced\n".to_string()
    }
}
// </vc-code>


}

fn main() {}