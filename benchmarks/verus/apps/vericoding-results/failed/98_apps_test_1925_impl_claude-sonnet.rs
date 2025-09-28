// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && 
    parse_three_ints_func(input).1 > 0
}

spec fn parse_three_ints_func(s: Seq<char>) -> (int, int, int) 
    recommends s.len() > 0
{
    let nums = parse_numbers(s, 0, seq![], 0, false);
    if nums.len() >= 3 { 
        (nums[0], if nums[1] > 0 { nums[1] } else { 1 }, nums[2])
    } else { 
        (0, 1, 0) 
    }
}

spec fn parse_numbers(s: Seq<char>, i: int, nums: Seq<int>, current: int, in_number: bool) -> Seq<int>
    recommends 0 <= i <= s.len()
    decreases s.len() - i
{
    if i >= s.len() {
        if in_number && nums.len() < 3 { nums.push(current) } else { nums }
    } else if nums.len() >= 3 {
        nums
    } else {
        let c = s[i];
        if c >= '0' && c <= '9' {
            let digit = c as int - '0' as int;
            if !in_number {
                parse_numbers(s, i + 1, nums, digit, true)
            } else {
                parse_numbers(s, i + 1, nums, current * 10 + digit, true)
            }
        } else if in_number {
            parse_numbers(s, i + 1, nums.push(current), 0, false)
        } else {
            parse_numbers(s, i + 1, nums, current, false)
        }
    }
}

spec fn int_to_string_func(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n < 0 { seq!['-'].add(int_to_string_helper_func(-n)) }
    else { int_to_string_helper_func(n) }
}

spec fn int_to_string_helper_func(n: int) -> Seq<char> 
    recommends n > 0
    decreases n
{
    if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string_helper_func(n / 10).add(seq![('0' as int + (n % 10)) as char])
    }
}

spec fn compute_max_value(a: int, b: int, n: int) -> int 
    recommends b > 0
{
    let min_val = if b - 1 < n { b - 1 } else { n };
    (a * min_val) / b
}
// </vc-preamble>

// <vc-helpers>
fn parse_three_ints(input: &str) -> (result: (i32, i32, i32))
    requires input@.len() > 0
    ensures ({
        let spec_result = parse_three_ints_func(input@);
        spec_result.0 == result.0 && spec_result.1 == result.1 && spec_result.2 == result.2
    })
{
    let mut nums = Vec::new();
    let mut current = 0i32;
    let mut in_number = false;
    
    for c in input.chars()
        invariant nums@.len() <= 3
    {
        if c >= '0' && c <= '9' {
            let digit = (c as u8 - '0' as u8) as i32;
            if !in_number {
                current = digit;
                in_number = true;
            } else {
                current = current * 10 + digit;
            }
        } else if in_number {
            nums.push(current);
            current = 0;
            in_number = false;
            if nums.len() >= 3 {
                break;
            }
        }
    }
    
    if in_number && nums.len() < 3 {
        nums.push(current);
    }
    
    let a = if nums.len() > 0 { nums[0] } else { 0 };
    let b = if nums.len() > 1 && nums[1] > 0 { nums[1] } else { 1 };
    let c = if nums.len() > 2 { nums[2] } else { 0 };
    
    (a, b, c)
}

/* helper modified by LLM (iteration 5): replaced String concatenation with format! to avoid codegen errors */
fn int_to_string(n: i32) -> (result: String)
    ensures result@ == int_to_string_func(n as int)
{
    if n == 0 {
        "0".to_string()
    } else if n < 0 {
        format!("-{}", int_to_string_helper(-n))
    } else {
        int_to_string_helper(n)
    }
}

fn int_to_string_helper(n: i32) -> (result: String)
    requires n > 0
    ensures result@ == int_to_string_helper_func(n as int)
{
    if n < 10 {
        let digit_char = ('0' as u8 + n as u8) as char;
        digit_char.to_string()
    } else {
        let mut result = int_to_string_helper(n / 10);
        let digit_char = ('0' as u8 + (n % 10) as u8) as char;
        result.push(digit_char);
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires 
        input@.len() > 0,
        valid_input(input@),
    ensures ({
        let parts = parse_three_ints_func(input@);
        let a = parts.0;
        let b = parts.1;  
        let n = parts.2;
        b > 0 &&
        result@ == int_to_string_func(compute_max_value(a, b, n)).add(seq!['\n'])
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed parse_three_ints return value naming */
    let (a, b, n) = parse_three_ints(&input);
    let min_val = if b - 1 < n { b - 1 } else { n };
    let max_value = (a * min_val) / b;
    let mut result = int_to_string(max_value);
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}