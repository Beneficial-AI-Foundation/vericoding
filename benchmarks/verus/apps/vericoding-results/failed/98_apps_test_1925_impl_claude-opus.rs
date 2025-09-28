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
/* helper modified by LLM (iteration 5): Fixed parse_three_ints and int_to_string helpers */
fn parse_three_ints(s: &Vec<char>) -> (res: (i64, i64, i64))
    requires
        s@.len() > 0,
        valid_input(s@),
    ensures
        res.0 == parse_three_ints_func(s@).0,
        res.1 == parse_three_ints_func(s@).1,
        res.2 == parse_three_ints_func(s@).2,
{
    let mut nums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut current: i64 = 0;
    let mut in_number: bool = false;
    
    while i < s.len() && nums.len() < 3
        invariant
            0 <= i <= s.len(),
            nums.len() <= 3,
    {
        let c = s[i];
        if c >= '0' && c <= '9' {
            let digit = (c as u8 - '0' as u8) as i64;
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
        }
        i = i + 1;
    }
    
    if in_number && nums.len() < 3 {
        nums.push(current);
    }
    
    if nums.len() >= 3 {
        let b_val = if nums[1] > 0 { nums[1] } else { 1 };
        (nums[0], b_val, nums[2])
    } else {
        (0, 1, 0)
    }
}

fn int_to_string(n: i64) -> (res: Vec<char>)
    ensures
        res@ == int_to_string_func(n as int),
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    } else if n < 0 {
        let mut result = Vec::new();
        result.push('-');
        let positive_part = int_to_string_helper(-n);
        let mut j: usize = 0;
        while j < positive_part.len()
            invariant
                0 <= j <= positive_part.len(),
                result.len() == 1 + j,
        {
            result.push(positive_part[j]);
            j = j + 1;
        }
        return result;
    } else {
        int_to_string_helper(n)
    }
}

fn int_to_string_helper(n: i64) -> (res: Vec<char>)
    requires
        n > 0,
    ensures
        res@ == int_to_string_helper_func(n as int),
    decreases n,
{
    if n < 10 {
        let mut result = Vec::new();
        result.push(('0' as u8 + (n as u8)) as char);
        return result;
    } else {
        let mut result = int_to_string_helper(n / 10);
        result.push(('0' as u8 + ((n % 10) as u8)) as char);
        return result;
    }
}

/* helper modified by LLM (iteration 5): Build String from Vec<char> using String::new and push_str */
fn vec_char_to_string(chars: &Vec<char>) -> (res: String)
    ensures
        res@ == chars@,
{
    let mut result = String::new();
    let mut i: usize = 0;
    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j] == chars@[j],
    {
        result.push_char(chars[i]);
        i = i + 1;
    }
    result
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
    /* code modified by LLM (iteration 5): Pass Vec<char> by reference to vec_char_to_string */
    let mut chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            chars@.len() == i as int,
            forall|j: int| 0 <= j < i ==> chars@[j] == input@[j],
    {
        chars.push(input.get_char(i));
        i = i + 1;
    }
    
    let parts = parse_three_ints(&chars);
    let a = parts.0;
    let b = parts.1;
    let n = parts.2;
    
    let min_val = if b - 1 < n { b - 1 } else { n };
    let max_value = (a * min_val) / b;
    
    let mut result_chars = int_to_string(max_value);
    result_chars.push('\n');
    
    let result_string = vec_char_to_string(&result_chars);
    result_string
}
// </vc-code>


}

fn main() {}