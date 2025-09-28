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
fn compute_min_string(s: &Vec<char>, n: usize) -> (usize, String)
    requires
        n > 0,
        s@.len() == n as int,
        forall|i: int| 0 <= i < s@.len() ==> #[trigger] s@[i] >= '0' && #[trigger] s@[i] <= '9'
    ensures
        let (index, result) = result;
        index < n as int,
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] >= '0' && #[trigger] result@[i] <= '9',
        result@ == modify_string(s@, index as int),
        forall|i: int| 0 <= i < s@.len() ==> string_to_int(result@) <= string_to_int(modify_string(s@, i))
{
    let mut min_val = 0x7FFFFFFF;
    let mut min_index = 0;
    let mut min_string = vec![];
    
    let mut index = 0;
    while index < n
        invariant
            index <= n,
            min_index < n,
            min_string@.len() == s@.len(),
            forall|i: int| 0 <= i < min_string@.len() ==> #[trigger] min_string@[i] >= '0' && #[trigger] min_string@[i] <= '9',
            min_string@ == modify_string(s@, min_index as int),
            forall|j: int| 0 <= j < index as int ==> string_to_int(min_string@) <= string_to_int(modify_string(s@, j)),
            min_val == string_to_int(min_string@)
    {
        let transformed = modify_string_at_index(s, index);
        let current_val = string_to_int_proof(&transformed, transformed.len());
        
        if current_val < min_val {
            min_val = current_val;
            min_index = index;
            min_string = transformed;
        }
        
        index += 1;
    }
    
    (min_index, String::from_iter(min_string))
}

fn modify_string_at_index(s: &Vec<char>, index: usize) -> Vec<char>
    requires
        s@.len() > 0,
        index < s@.len() as int,
        forall|i: int| 0 <= i < s@.len() ==> #[trigger] s@[i] >= '0' && #[trigger] s@[i] <= '9'
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] >= '0' && #[trigger] result@[i] <= '9',
        result@ == modify_string(s@, index as int)
{
    let key: i32;
    proof {
        let key_spec = if s@[index as int] == '0' { 0 } else { 10 - (s@[index as int] as int - '0' as int) };
        key = key_spec as i32;
    }
    
    let transformed = transform_digits_impl(s, key);
    rotate_string_impl(&transformed, index)
}

fn transform_digits_impl(s: &Vec<char>, key: i32) -> Vec<char>
    requires
        s@.len() >= 0,
        key >= 0 && key <= 9,
        forall|i: int| 0 <= i < s@.len() ==> #[trigger] s@[i] >= '0' && #[trigger] s@[i] <= '9'
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] >= '0' && #[trigger] result@[i] <= '9',
        result@ == transform_digits(s@, key as int)
{
    let mut result = Vec::with_capacity(s.len());
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@.len() == i as int,
            result@ == transform_digits(s@.take(i as int), key as int)
    {
        let digit_char = s[i];
        let digit_val = digit_char as i32 - '0' as i32;
        let transformed_digit = (digit_val + key) % 10;
        let result_char = ('0' as i32 + transformed_digit) as char;
        result.push(result_char);
        i += 1;
    }
    result
}

fn rotate_string_impl(s: &Vec<char>, index: usize) -> Vec<char>
    requires
        s@.len() > 0,
        index < s@.len() as int
    ensures
        result@.len() == s@.len(),
        result@ == rotate_string(s@, index as int)
{
    let mut result = Vec::with_capacity(s.len());
    let mut i = index;
    while i < s.len()
        invariant
            index <= i <= s.len(),
            result@.len() == (i - index) as int,
            result@ == s@.skip(index as int).take(i - index)
    {
        result.push(s[i]);
        i += 1;
    }
    
    let mut j = 0;
    while j < index
        invariant
            0 <= j <= index,
            result@.len() == (s.len() - index + j) as int,
            result@ == s@.skip(index as int).add(s@.take(j as int))
    {
        result.push(s[j]);
        j += 1;
    }
    result
}

fn string_to_int_proof(s: &Vec<char>, len: usize) -> i32
    requires
        s@.len() == len as int,
        forall|i: int| 0 <= i < s@.len() ==> #[trigger] s@[i] >= '0' && #[trigger] s@[i] <= '9'
    ensures
        result == string_to_int(s@)
{
    if s.is_empty() {
        return 0;
    }
    
    let mut result = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == string_to_int(s@.take(i as int))
    {
        let digit = s[i] as i32 - '0' as i32;
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
    /* code modified by LLM (iteration 5): Fixed while loop condition compilation error */
    let input_chars: Vec<char> = stdin_input.chars().collect();
    
    let mut lines = Vec::new();
    let mut current_line = Vec::new();
    let mut i = 0;
    
    while i < input_chars.len()
        invariant
            i <= input_chars.len(),
            parse_input_helper(input_chars@, 0, seq![], seq![]) == parse_input_helper(input_chars@, i as int, current_line@, Seq::from_vec(lines.clone()))
    {
        if input_chars[i] == '\n' {
            lines.push(current_line.clone());
            current_line.clear();
        } else {
            current_line.push(input_chars[i]);
        }
        i += 1;
    }
    
    if !current_line.is_empty() {
        lines.push(current_line.clone());
    }
    
    if lines.len() < 2 {
        return String::from("\n");
    }
    
    let n_line = &lines[0];
    let digits_line = &lines[1];
    
    let n_val = string_to_int_proof(n_line, n_line.len());
    
    if n_val <= 0 || digits_line.len() as i32 != n_val {
        return String::from("\n");
    }
    
    for i in 0..digits_line.len() {
        if digits_line[i] < '0' || digits_line[i] > '9' {
            return String::from("\n");
        }
    }
    
    let (min_index, min_string) = compute_min_string(digits_line, digits_line.len());
    
    let mut result = min_string;
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}