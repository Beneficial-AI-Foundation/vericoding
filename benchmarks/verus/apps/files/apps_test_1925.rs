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
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}