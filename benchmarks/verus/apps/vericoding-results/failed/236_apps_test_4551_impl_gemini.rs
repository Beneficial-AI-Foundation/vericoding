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
fn is_valid_integer_exec(s: &str) -> (b: bool)
    ensures b == is_valid_integer(s@),
{
    if s.len() == 0 {
        return false;
    }
    let s_bytes = s.as_bytes();

    if s_bytes[0] == b'-' {
        let mut i = 1;
        while i < s.len()
            invariant
                i <= s.len(),
                forall|j: int| 1 <= j < i as int ==> ('0' <= s@[j] && s@[j] <= '9'),
        {
            let c = s_bytes[i];
            if c < b'0' || c > b'9' {
                return false;
            }
            i += 1;
        }
    } else {
        let mut i = 0;
        while i < s.len()
            invariant
                i <= s.len(),
                forall|j: int| 0 <= j < i as int ==> ('0' <= s@[j] && s@[j] <= '9'),
        {
            let c = s_bytes[i];
            if c < b'0' || c > b'9' {
                return false;
            }
            i += 1;
        }
    }
    true
}

fn string_to_int_exec(s: &str) -> (r: int)
    requires is_valid_integer(s@),
    ensures r == string_to_int_pure(s@),
{
    let s_bytes = s.as_bytes();
    let mut i = 0;
    let negative = if s@[0] == '-' {
        i = 1;
        true
    } else {
        false
    };

    let mut acc = 0int;
    while i < s.len()
        invariant
            is_valid_integer(s@),
            i <= s.len(),
            negative <==> (s@[0] == '-'),
            string_to_int_pure(s@) == if negative {
                -string_to_int_helper_unsigned(s@, i as int, acc)
            } else {
                string_to_int_helper_unsigned(s@, i as int, acc)
            },
    {
        let c = s_bytes[i];
        let digit = (c - b'0') as int;
        acc = acc * 10 + digit;
        i += 1;
    }

    if negative { -acc } else { acc }
}

fn split_string_exec(s: &str) -> (parts: Vec<String>)
    ensures
        parts@ == split_string_pure(s@),
{
    let mut parts = Vec::new();
    let mut current = String::new();
    let s_bytes = s.as_bytes();

    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            split_string_pure(s@) == split_string_helper(s@, i as int, current@, parts@),
    {
        let c = s_bytes[i];
        if c == b' ' || c == b'\t' || c == b'\n' {
            if current.len() > 0 {
                parts.push(current);
                current = String::new();
            }
        } else {
            current.push(c as char);
        }
        i += 1;
    }

    if current.len() > 0 {
        parts.push(current);
    }
    
    parts
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
    let parts = split_string_exec(input);

    if parts.len() < 4 {
        return "".to_string();
    }

    let p0 = &parts[0];
    let p1 = &parts[1];
    let p2 = &parts[2];
    let p3 = &parts[3];

    if !is_valid_integer_exec(p0) || !is_valid_integer_exec(p1) || !is_valid_integer_exec(p2) || !is_valid_integer_exec(p3) {
        return "".to_string();
    }

    let a = string_to_int_exec(p0);
    let b = string_to_int_exec(p1);
    let c = string_to_int_exec(p2);
    let d = string_to_int_exec(p3);

    if a + b > c + d {
        "Left\n".to_string()
    } else if a + b < c + d {
        "Right\n".to_string()
    } else {
        "Balanced\n".to_string()
    }
}
// </vc-code>


}

fn main() {}