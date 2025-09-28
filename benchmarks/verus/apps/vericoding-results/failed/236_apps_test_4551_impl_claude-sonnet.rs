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
/* helper modified by LLM (iteration 5): use vstd String instead of std::string::String */ 
fn split_string(input: &str) -> (result: Vec<vstd::string::String>)
    ensures
        result@.len() == split_string_pure(input@).len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@ == split_string_pure(input@)[i]
{
    let mut parts: Vec<vstd::string::String> = Vec::new();
    let mut current = vstd::string::String::new();
    let mut i = 0;
    
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            parts@.len() <= split_string_pure(input@).len(),
            forall|j: int| 0 <= j < parts@.len() ==> parts@[j]@ == split_string_pure(input@)[j]
    {
        let input_bytes = input.as_bytes();
        let c = input_bytes[i] as char;
        if c == ' ' || c == '\n' || c == '\t' {
            if current.len() > 0 {
                parts.push(current.clone());
                current = vstd::string::String::new();
            }
        } else {
            current.push(c);
        }
        i += 1;
    }
    
    if current.len() > 0 {
        parts.push(current);
    }
    
    parts
}

fn parse_int(s: &str) -> (result: Option<i32>)
    ensures
        is_valid_integer(s@) ==> result.is_some() && result.unwrap() as int == string_to_int_pure(s@),
        !is_valid_integer(s@) ==> result.is_none()
{
    if s.len() == 0 {
        return None;
    }
    
    let chars: Vec<char> = s.chars().collect();
    let mut negative = false;
    let mut start = 0;
    
    if chars[0] == '-' {
        negative = true;
        start = 1;
        if chars.len() == 1 {
            return None;
        }
    }
    
    let mut result = 0i32;
    let mut i = start;
    
    while i < chars.len()
        invariant
            start <= i <= chars.len(),
            start == if negative { 1int } else { 0int },
            forall|j: int| start <= j < i ==> '0' <= chars[j] <= '9'
    {
        if chars[i] < '0' || chars[i] > '9' {
            return None;
        }
        
        let digit = (chars[i] as u8 - 48u8) as i32;
        result = result * 10 + digit;
        i += 1;
    }
    
    if negative {
        result = -result;
    }
    
    Some(result)
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
    /* code modified by LLM (iteration 5): use vstd String and as_str() */
    let parts = split_string(input);
    
    if parts.len() < 4 {
        return vstd::string::String::from_rust_string("".to_string());
    }
    
    let a_opt = parse_int(parts[0].as_str());
    let b_opt = parse_int(parts[1].as_str());
    let c_opt = parse_int(parts[2].as_str());
    let d_opt = parse_int(parts[3].as_str());
    
    if a_opt.is_none() || b_opt.is_none() || c_opt.is_none() || d_opt.is_none() {
        return vstd::string::String::from_rust_string("".to_string());
    }
    
    let a = a_opt.unwrap();
    let b = b_opt.unwrap();
    let c = c_opt.unwrap();
    let d = d_opt.unwrap();
    
    let left_sum = a + b;
    let right_sum = c + d;
    
    if left_sum > right_sum {
        vstd::string::String::from_rust_string("Left\n".to_string())
    } else if left_sum < right_sum {
        vstd::string::String::from_rust_string("Right\n".to_string())
    } else {
        vstd::string::String::from_rust_string("Balanced\n".to_string())
    }
}
// </vc-code>


}

fn main() {}