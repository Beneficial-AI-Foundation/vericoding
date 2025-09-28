// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 0
}

spec fn sum_of_numbers_in_string(s: Seq<char>) -> int {
    let numbers = extract_numbers_from_string(s);
    sum_sequence(numbers)
}

spec fn extract_numbers_from_string(s: Seq<char>) -> Seq<int> {
    extract_numbers_helper(s, 0, 0, false, seq![])
}

spec fn sum_sequence(numbers: Seq<int>) -> int
    decreases numbers.len()
{
    if numbers.len() == 0 {
        0int
    } else {
        numbers[0] + sum_sequence(numbers.subrange(1, numbers.len() as int))
    }
}
spec fn extract_numbers_helper(s: Seq<char>, i: int, current_number: int, in_number: bool, numbers: Seq<int>) -> Seq<int>
    decreases s.len() - i when 0 <= i <= s.len() && current_number >= 0
{
    if 0 <= i <= s.len() && current_number >= 0 {
        if i == s.len() {
            if in_number { numbers.push(current_number) } else { numbers }
        } else {
            let c = s[i];
            if '0' <= c && c <= '9' {
                let digit = c as int - '0' as int;
                extract_numbers_helper(s, i + 1, current_number * 10 + digit, true, numbers)
            } else {
                if in_number {
                    extract_numbers_helper(s, i + 1, 0, false, numbers.push(current_number))
                } else {
                    extract_numbers_helper(s, i + 1, 0, false, numbers)
                }
            }
        }
    } else {
        seq![]
    }
}
// </vc-preamble>

// <vc-helpers>
fn extract_numbers(s: &Vec<char>) -> (result: Vec<u32>)
    decreases s.len()
{
    if s.len() == 0 {
        Vec::new()
    } else {
        extract_numbers_help(s, 0, 0, false, Vec::new())
    }
}

/* helper modified by LLM (iteration 2): rename to avoid naming conflict with spec function */
fn extract_numbers_help(s: &Vec<char>, i: usize, current_number: u64, in_number: bool, mut numbers: Vec<u32>) -> Vec<u32>
    requires i <= s.len()
    decreases s.len() - i
{
    if i == s.len() {
        if in_number && current_number <= u32::MAX as u64 {
            numbers.push(current_number as u32);
        }
        numbers
    } else {
        let c = s[i];
        if '0' <= c && c <= '9' {
            let digit = (c as u64 - '0' as u64);
            let new_current = current_number * 10 + digit;
            extract_numbers_help(s, i + 1, new_current, true, numbers)
        } else {
            if in_number && current_number <= u32::MAX as u64 {
                numbers.push(current_number as u32);
            }
            extract_numbers_help(s, i + 1, 0, false, numbers)
        }
    }
}

/* helper modified by LLM (iteration 4): changed parameter to &[u32] for slice recursion and removed invalid subrange call */
fn sum_numbers(nums: &[u32]) -> (sum: u32)
    decreases nums.len()
{
    if nums.is_empty() {
        0u32
    } else {
        nums[0] + sum_numbers(&nums[1..])
    }
}
// </vc-helpers>

// <vc-spec>
fn fruit_distribution(s: &Vec<char>, n: u32) -> (mangoes: u32)
    requires valid_input(n as int)
    ensures mangoes as int == (n as int) - sum_of_numbers_in_string(s@),
            (mangoes as int >= 0) <==> ((n as int) >= sum_of_numbers_in_string(s@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed casting in extract_numbers_help */
    let numbers = extract_numbers(s);
    let summed = sum_numbers(&numbers);
    n - summed
}
// </vc-code>


}

fn main() {}