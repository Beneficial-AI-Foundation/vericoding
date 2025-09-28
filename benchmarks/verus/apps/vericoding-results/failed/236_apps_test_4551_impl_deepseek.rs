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
/* helper modified by LLM (iteration 4): Fixed integer conversion to use proper executable types */
fn parse_integer_at(input_seq: Seq<char>, start: usize) -> (result: (i64, usize))
    requires
        start <= input_seq.len(),
    ensures
        result.1 >= start,
        result.1 <= input_seq.len(),
        result.0 as int == string_to_int_pure(input_seq.subrange(start, result.1)),
        is_valid_integer(input_seq.subrange(start, result.1)),
{
    let mut index = start;
    let mut is_negative = false;
    let mut value: i64 = 0;
    
    if index < input_seq.len() && input_seq[index] == '-' {
        is_negative = true;
        index = index + 1;
    }
    
    proof {
        assert(value == 0);
    }
    
    let mut digits_found = false;
    
    while index < input_seq.len() && '0' <= input_seq[index] && input_seq[index] <= '9'
        invariant
            index >= start,
            index <= input_seq.len(),
            value >= 0,
            value as int == string_to_int_pure(input_seq.subrange(start + (if is_negative { 1 } else { 0 }), index)),
            is_valid_integer(input_seq.subrange(start + (if is_negative { 1 } else { 0 }), index)),
        decreases input_seq.len() - index,
    {
        let digit_char = input_seq[index];
        let digit_value: u32 = (digit_char as u32) - ('0' as u32);
        value = value * 10 + (digit_value as i64);
        index = index + 1;
        digits_found = true;
        
        proof {
            assert(value >= 0);
        }
    }
    
    if is_negative {
        value = -value;
    }
    
    assert(digits_found || !is_negative) by {
        if is_negative && !digits_found {
            assert(!is_valid_integer(input_seq.subrange(start, index)));
        } else {
            assert(is_valid_integer(input_seq.subrange(start, index)));
        }
    };
    
    (value, index)
}

fn find_next_token_start(input_seq: Seq<char>, start: usize) -> (result: usize)
    requires
        start <= input_seq.len(),
    ensures
        result >= start,
        result <= input_seq.len(),
        (result < input_seq.len() ==> !(input_seq[result] == ' ' || input_seq[result] == '\n' || input_seq[result] == '\t')),
        forall|i: int| start <= i < result ==> (input_seq[i] == ' ' || input_seq[i] == '\n' || input_seq[i] == '\t'),
{
    let mut index = start;
    
    while index < input_seq.len() && (input_seq[index] == ' ' || input_seq[index] == '\n' || input_seq[index] == '\t')
        invariant
            index >= start,
            index <= input_seq.len(),
            forall|i: int| start <= i < index ==> (input_seq[i] == ' ' || input_seq[i] == '\n' || input_seq[i] == '\t'),
        decreases input_seq.len() - index,
    {
        index = index + 1;
    }
    
    index
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
/* code modified by LLM (iteration 4): Fixed type usage and proper conversion logic */
{
    let s = input.to_string();
    let chars: Vec<char> = s.chars().collect();
    let input_seq = Seq::new(chars.len(), |i: int| chars[i]);
    let mut index: usize = 0;
    
    if index >= input_seq.len() {
        return "".to_string();
    }
    
    index = find_next_token_start(input_seq, index);
    if index >= input_seq.len() {
        return "".to_string();
    }
    let (a_value, a_end) = parse_integer_at(input_seq, index);
    index = a_end;
    
    index = find_next_token_start(input_seq, index);
    if index >= input_seq.len() {
        return "".to_string();
    }
    let (b_value, b_end) = parse_integer_at(input_seq, index);
    index = b_end;
    
    index = find_next_token_start(input_seq, index);
    if index >= input_seq.len() {
        return "".to_string();
    }
    let (c_value, c_end) = parse_integer_at(input_seq, index);
    index = c_end;
    
    index = find_next_token_start(input_seq, index);
    if index >= input_seq.len() {
        return "".to_string();
    }
    let (d_value, d_end) = parse_integer_at(input_seq, index);
    index = d_end;
    
    let sum_left = a_value + b_value;
    let sum_right = c_value + d_value;
    
    if sum_left > sum_right {
        "Left\n".to_string()
    } else if sum_left < sum_right {
        "Right\n".to_string()
    } else {
        "Balanced\n".to_string()
    }
}
// </vc-code>


}

fn main() {}