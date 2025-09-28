// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, digits: Seq<char>) -> bool {
    n > 0 && digits.len() == n && forall|i: int| 0 <= i < digits.len() ==> #[trigger] digits[i] >= '0' && #[trigger] digits[i] <= '9'
}

spec fn modify_string(s: Seq<char>, index: int) -> Seq<char> {
    let key = if s[index] == '0' { 0 } else { 10 - (s[index] as int - '0' as int) };
    let transformed = transform_digits(s, key);
    rotate_string(transformed, index)
}

spec fn transform_digits(s: Seq<char>, key: int) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let digit = (s[0] as int - '0' as int + key) % 10;
        seq![('0' as int + digit) as char].add(transform_digits(s.skip(1), key))
    }
}

spec fn rotate_string(s: Seq<char>, index: int) -> Seq<char> {
    if s.len() == 0 {
        seq![]
    } else {
        s.skip(index).add(s.take(index))
    }
}

spec fn is_all_digits(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9'
}

spec fn parse_input(input: Seq<char>) -> Seq<Seq<char>>
    decreases input.len()
{
    parse_input_helper(input, 0, seq![], seq![])
}

spec fn parse_input_helper(input: Seq<char>, i: int, current_line: Seq<char>, lines: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases input.len() - i
{
    if i >= input.len() {
        if current_line.len() > 0 { lines.push(current_line) } else { lines }
    } else if input[i] == '\n' {
        parse_input_helper(input, i + 1, seq![], lines.push(current_line))
    } else {
        parse_input_helper(input, i + 1, current_line.push(input[i]), lines)
    }
}

spec fn parse_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if !('0' <= s[0] <= '9') {
        0
    } else {
        (s[0] as int - '0' as int) + 10 * parse_int(s.skip(1))
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if !('0' <= s[0] <= '9') {
        string_to_int(s.skip(1))
    } else {
        (s[0] as int - '0' as int) * pow(10, (s.len() - 1) as nat) + string_to_int(s.skip(1))
    }
}

spec fn pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn parse_input_preserves_structure(input: Seq<char>)
    ensures
        parse_input(input).len() >= 0,
        forall|i: int| 0 <= i < parse_input(input).len() ==> parse_input(input)[i].len() >= 0
{
}

proof fn string_to_int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        is_all_digits(s1),
        is_all_digits(s2),
        s1.len() == s2.len(),
    ensures
        (forall|i: int| 0 <= i < s1.len() ==> s1[i] <= s2[i]) ==> string_to_int(s1) <= string_to_int(s2)
{
}

proof fn modify_string_preserves_length(s: Seq<char>, index: int)
    requires
        is_all_digits(s),
        0 <= index < s.len(),
    ensures
        modify_string(s, index).len() == s.len(),
        is_all_digits(modify_string(s, index))
{
}

fn exec_parse_input(input: Vec<u8>) -> (result: Vec<Vec<char>>)
    ensures
        result@.len() >= 0,
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() >= 0
{
    let mut lines = Vec::new();
    let mut current_line = Vec::new();
    
    for ch in input.iter()
        invariant
            lines@.len() >= 0,
            current_line@.len() >= 0
    {
        let c = *ch as char;
        if c == '\n' {
            lines.push(current_line);
            current_line = Vec::new();
        } else {
            current_line.push(c);
        }
    }
    
    if current_line.len() > 0 {
        lines.push(current_line);
    }
    
    lines
}

fn exec_string_to_int(s: &[char]) -> (result: usize)
    requires
        s@.len() > 0,
        forall|i: int| 0 <= i < s@.len() ==> s@[i] >= '0' && s@[i] <= '9'
    ensures
        result >= 0
{
    let mut result = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            result >= 0
    {
        let digit = (s[i] as u8 - '0' as u8) as usize;
        result = result * 10 + digit;
        i += 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: String) -> (result: String)
    requires
        stdin_input@.len() > 0,
        (exists|i: int| 0 <= i < stdin_input@.len() && stdin_input@[i] == '\n'),
    ensures
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        ({
            let lines = parse_input(stdin_input@);
            if lines.len() >= 2 {
                let n = parse_int(lines[0]);
                let digits = lines[1];
                if valid_input(n, digits) {
                    let min_result = result@.take(result@.len() - 1);
                    min_result.len() == n &&
                    (forall|i: int| 0 <= i < min_result.len() ==> #[trigger] min_result[i] >= '0' && #[trigger] min_result[i] <= '9') &&
                    (exists|index: int| 0 <= index < n && min_result == modify_string(digits, index)) &&
                    (forall|index: int| 0 <= index < n ==> string_to_int(min_result) <= string_to_int(modify_string(digits, index)))
                } else {
                    result@ == seq!['\n']
                }
            } else {
                result@ == seq!['\n']
            }
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Convert string to Vec<u8> to avoid as_bytes() */
    let input_bytes: Vec<u8> = stdin_input.chars().map(|c| c as u8).collect();
    let lines = exec_parse_input(input_bytes);
    
    if lines.len() < 2 {
        return "\n".to_string();
    }
    
    let first_line = &lines[0];
    if first_line.len() == 0 {
        return "\n".to_string();
    }
    
    let mut is_valid_num = true;
    for ch in first_line.iter() {
        if *ch < '0' || *ch > '9' {
            is_valid_num = false;
            break;
        }
    }
    
    if !is_valid_num {
        return "\n".to_string();
    }
    
    let n = exec_string_to_int(&first_line);
    
    if n == 0 || lines.len() < 2 {
        return "\n".to_string();
    }
    
    let digits = &lines[1];
    
    if digits.len() != n {
        return "\n".to_string();
    }
    
    for ch in digits.iter() {
        if *ch < '0' || *ch > '9' {
            return "\n".to_string();
        }
    }
    
    let mut min_result = String::new();
    let mut min_value = usize::MAX;
    let mut found_valid = false;
    
    for index in 0..n {
        let key = if digits[index] == '0' { 
            0 
        } else { 
            10 - (digits[index] as u8 - '0' as u8) as usize 
        };
        
        let mut transformed = Vec::new();
        for ch in digits.iter() {
            let digit = (*ch as u8 - '0' as u8) as usize;
            let new_digit = (digit + key) % 10;
            transformed.push(('0' as u8 + new_digit as u8) as char);
        }
        
        let mut rotated = Vec::new();
        for i in index..transformed.len() {
            rotated.push(transformed[i]);
        }
        for i in 0..index {
            rotated.push(transformed[i]);
        }
        
        let current_value = exec_string_to_int(&rotated);
        
        if !found_valid || current_value < min_value {
            min_value = current_value;
            min_result = rotated.iter().collect();
            found_valid = true;
        }
    }
    
    min_result + "\n"
}
// </vc-code>


}

fn main() {}