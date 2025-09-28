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
/* helper modified by LLM (iteration 3): Fixed compilation error by replacing c.is_digit(10) with character range check and computed digit using char as u32 */
fn exec_parse_three_ints(input: &Vec<char>) -> (i64, i64, i64)
{
    let mut i: usize = 0;
    let mut nums: Vec<i64> = Vec::new();
    let mut current: i64 = 0;
    let mut in_number: bool = false;
    while i < input.len()
        invariant
            0 <= (i as int) <= (input.len() as int),
        decreases (input.len() as int) - (i as int)
    {
        let c = input[i];
        if c >= '0' && c <= '9' {
            let digit = ((c as u32) - ('0' as u32)) as i64;
            if !in_number {
                current = digit;
                in_number = true;
            } else {
                current = current * 10 + digit;
            }
        } else if in_number {
            if nums.len() < 3 {
                nums.push(current);
            }
            current = 0;
            in_number = false;
        }
        i += 1;
    }
    if in_number && nums.len() < 3 {
        nums.push(current);
    }
    if nums.len() >= 3 {
        (nums[0], if nums[1] > 0 { nums[1] } else { 1 }, nums[2])
    } else {
        (0, 1, 0)
    }
}

/* helper modified by LLM (iteration 5): Fixed compilation error by using usize for indexing and avoiding int type in exec code */
fn exec_int_to_string(n: i64) -> Vec<char>
{
    if n == 0 {
        return vec!['0'];
    }
    let mut result = Vec::new();
    if n < 0 {
        result.push('-');
    }
    let mut nn = if n < 0 { -n } else { n };
    let mut num_chars = Vec::new();
    while nn > 0
        invariant
            nn >= 0,
        decreases nn as nat
    {
        let digit = (nn % 10) as u32;
        num_chars.push((('0' as u32) + digit) as char);
        nn /= 10;
    }
    let mut i: usize = 0;
    while i < num_chars.len()
        invariant
            0 <= i <= num_chars.len(),
        decreases num_chars.len() - i
    {
        result.push(num_chars[num_chars.len() - 1 - i]);
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 2): Updated exec_compute_max_value to use i64 */
fn exec_compute_max_value(a: i64, b: i64, n: i64) -> i64
    requires
        b > 0,
{
    let min_val = if b - 1 < n { b - 1 } else { n };
    (a * min_val) / b
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
    /* code modified by LLM (iteration 4): Replaced collect for Vec<char> to String with loop */
    let input_vec: Vec<char> = input.chars().collect::<Vec<char>>();
    let parts = exec_parse_three_ints(&input_vec);
    let a = parts.0;
    let b = parts.1;
    let n = parts.2;
    let computed = exec_compute_max_value(a, b, n);
    let mut str_vec = exec_int_to_string(computed);
    str_vec.push('\n');
    let mut result_string = String::new();
    let mut i = 0;
    while i < str_vec.len()
        invariant
            0 <= i <= str_vec.len(),
        decreases str_vec.len() - i
    {
        result_string.push(str_vec[i]);
        i += 1;
    }
    result_string
}
// </vc-code>


}

fn main() {}