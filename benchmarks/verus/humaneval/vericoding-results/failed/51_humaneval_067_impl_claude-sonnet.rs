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
/* helper modified by LLM (iteration 5): added proof assertions to establish postcondition */
fn extract_numbers_from_string_exec(s: &Vec<char>) -> (numbers: Vec<u32>)
    ensures numbers@.map(|i: int, x: u32| x as int) == extract_numbers_from_string(s@)
{
    let mut numbers = Vec::new();
    let mut i = 0;
    let mut current_number = 0u32;
    let mut in_number = false;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            current_number <= u32::MAX,
        decreases s.len() - i
    {
        let c = s[i];
        if '0' <= c && c <= '9' {
            let digit = (c as u32) - ('0' as u32);
            if current_number <= (u32::MAX - digit) / 10 {
                current_number = current_number * 10 + digit;
                in_number = true;
            }
        } else {
            if in_number {
                numbers.push(current_number);
                current_number = 0;
                in_number = false;
            }
        }
        i += 1;
    }
    
    if in_number {
        numbers.push(current_number);
    }
    
    proof {
        assert(numbers@.map(|i: int, x: u32| x as int) == extract_numbers_from_string(s@));
    }
    
    numbers
}

fn sum_numbers(numbers: &Vec<u32>) -> (sum: u32)
    ensures sum as int == sum_sequence(numbers@.map(|i: int, x: u32| x as int))
{
    let mut sum = 0u32;
    let mut i = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            sum <= u32::MAX,
        decreases numbers.len() - i
    {
        if sum <= u32::MAX - numbers[i] {
            sum = sum + numbers[i];
        }
        i += 1;
    }
    
    proof {
        assert(sum as int == sum_sequence(numbers@.map(|i: int, x: u32| x as int)));
    }
    
    sum
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
    /* code modified by LLM (iteration 5): added proof assertions for postconditions */
    let numbers = extract_numbers_from_string_exec(s);
    let sum = sum_numbers(&numbers);
    
    proof {
        assert(sum as int == sum_of_numbers_in_string(s@));
    }
    
    let result = if n >= sum {
        n - sum
    } else {
        0
    };
    
    proof {
        assert(result as int == (n as int) - sum_of_numbers_in_string(s@));
        assert((result as int >= 0) <==> ((n as int) >= sum_of_numbers_in_string(s@)));
    }
    
    result
}
// </vc-code>


}

fn main() {}