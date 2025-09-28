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
fn exec_extract_numbers_from_string(s: &Vec<char>) -> (numbers: Vec<int>)
    ensures numbers@ == extract_numbers_from_string(s@)
{
    exec_extract_numbers_helper(s, 0, 0, false)
}

fn exec_extract_numbers_helper(s: &Vec<char>, i: usize, current_number: int, in_number: bool) -> (numbers: Vec<int>)
    requires
        0 <= i <= s.len(),
        current_number >= 0,
    decreases s.len() - i
    ensures
        let spec_result = extract_numbers_helper(s@, i as int, current_number, in_number, seq![]);
        numbers@ == spec_result
{
    if i == s.len() {
        if in_number {
            vec![current_number]
        } else {
            Vec::new()
        }
    } else {
        let c = s[i];
        if '0' <= c && c <= '9' {
            let digit = (c as int) - ('0' as int);
            exec_extract_numbers_helper(s, i+1, current_number * 10 + digit, true)
        } else {
            if in_number {
                let mut rest = exec_extract_numbers_helper(s, i+1, 0, false);
                rest.insert(0, current_number);
                rest
            } else {
                exec_extract_numbers_helper(s, i+1, 0, false)
            }
        }
    }
}

fn exec_sum_of_numbers_in_string(s: &Vec<char>) -> (sum: int)
    ensures sum == sum_of_numbers_in_string(s@)
{
    let numbers = exec_extract_numbers_from_string(s);
    let mut total = 0;
    for i in 0..numbers.len()
        invariant
            0 <= i <= numbers.len(),
            total == sum_sequence(numbers@.subrange(0, i as int))
        decreases numbers.len() - i
    {
        total += numbers[i];
    }
    total
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
    let sum = exec_sum_of_numbers_in_string(s);
    let diff = (n as int) - sum;
    let mangoes = diff as u32;
    mangoes
}
// </vc-code>


}

fn main() {}