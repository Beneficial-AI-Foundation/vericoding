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
/* helper modified by LLM (iteration 5): Fixed map function signature and string conversion */
fn string_to_int(s: &Vec<char>) -> (result: i32)
    requires
        is_valid_integer(s@),
    ensures
        result as int == string_to_int_pure(s@),
{
    let mut acc: i32 = 0;
    let mut i: usize = 0;
    let is_negative = s.len() > 0 && s[0] == '-';
    
    if is_negative {
        i = 1;
    }
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_valid_integer(s@),
            acc >= 0,
            is_negative ==> i >= 1,
            is_negative ==> acc as int == string_to_int_helper_unsigned(s@, 1, 0) - string_to_int_helper_unsigned(s@, i as int, 0),
            !is_negative ==> acc as int == string_to_int_helper_unsigned(s@, 0, 0) - string_to_int_helper_unsigned(s@, i as int, 0),
    {
        let digit = (s[i] as i32) - ('0' as i32);
        acc = acc * 10 + digit;
        i = i + 1;
    }
    
    if is_negative {
        return -acc;
    } else {
        return acc;
    }
}

fn split_string(s: &Vec<char>) -> (result: Vec<Vec<char>>)
    ensures
        result@.map(|i: int, v: Vec<char>| v@) == split_string_pure(s@),
{
    let mut parts: Vec<Vec<char>> = Vec::new();
    let mut current: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            parts@.map(|j: int, v: Vec<char>| v@).push(current@) == split_string_helper(s@, 0, seq![], seq![]).take(parts@.len() as int + 1),
    {
        let ch = s[i];
        if ch == ' ' || ch == '\n' || ch == '\t' {
            if current.len() > 0 {
                parts.push(current);
                current = Vec::new();
            }
        } else {
            current.push(ch);
        }
        i = i + 1;
    }
    
    if current.len() > 0 {
        parts.push(current);
    }
    
    parts
}

fn str_to_vec_char(s: &str) -> (result: Vec<char>)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == s@[i],
{
    let mut chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            chars@.len() == i as int,
            forall|j: int| 0 <= j < i ==> chars@[j] == s@[j],
    {
        let ch = s.get_char(i);
        chars.push(ch);
        i = i + 1;
    }
    
    chars
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
/* code modified by LLM (iteration 5): Use str_to_vec_char helper to convert string */
{
    let chars = str_to_vec_char(input);
    let parts = split_string(&chars);
    
    if parts.len() < 4 {
        return "".to_string();
    }
    
    let part0 = &parts[0];
    let part1 = &parts[1];
    let part2 = &parts[2];
    let part3 = &parts[3];
    
    if !is_valid_integer(part0@) || !is_valid_integer(part1@) || 
       !is_valid_integer(part2@) || !is_valid_integer(part3@) {
        return "".to_string();
    }
    
    let a = string_to_int(part0);
    let b = string_to_int(part1);
    let c = string_to_int(part2);
    let d = string_to_int(part3);
    
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