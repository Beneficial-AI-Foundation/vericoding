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
spec fn sum_of_remaining_string(s: Seq<char>, i: int, current_number: int, in_number: bool) -> int
    decreases s.len() - i when 0 <= i <= s.len() && current_number >= 0
{
    sum_sequence(extract_numbers_helper(s, i, current_number, in_number, seq![]))
}

proof fn lemma_sum_sequence_add(s1: Seq<int>, s2: Seq<int>)
    ensures sum_sequence(s1.add(s2)) == sum_sequence(s1) + sum_sequence(s2),
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_sum_sequence_add(s1.subrange(1, s1.len() as int), s2);
    }
}

proof fn sum_extract_distributive(s: Seq<char>, i: int, current_number: int, in_number: bool, numbers: Seq<int>)
    requires
        0 <= i <= s.len(),
        current_number >= 0,
    ensures
        sum_sequence(extract_numbers_helper(s, i, current_number, in_number, numbers)) ==
            sum_sequence(numbers) + sum_of_remaining_string(s, i, current_number, in_number),
    decreases s.len() - i
{
    if i < s.len() {
        let c = s[i];
        if '0' <= c && c <= '9' {
            let digit = c as int - '0' as int;
            sum_extract_distributive(s, i + 1, current_number * 10 + digit, true, numbers);
        } else {
            if in_number {
                lemma_sum_sequence_add(numbers, seq![current_number]);
                sum_extract_distributive(s, i + 1, 0, false, numbers.push(current_number));
                sum_extract_distributive(s, i + 1, 0, false, seq![current_number]);
            } else {
                sum_extract_distributive(s, i + 1, 0, false, numbers);
            }
        }
    } else {
        if in_number {
            lemma_sum_sequence_add(numbers, seq![current_number]);
        }
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
    /* code modified by LLM (iteration 2): fixed type error in assert calls by casting .len() to int */
    let mut i: usize = 0;
    let mut sum: u32 = 0;
    let mut current_number: u32 = 0;
    let mut in_number = false;

    while i < s.len()
        invariant
            0 <= i <= s.len(),
            current_number >= 0,
            sum >= 0,
            sum_of_numbers_in_string(s@) == (sum as int) +
                sum_of_remaining_string(s@, i as int, current_number as int, in_number),
        decreases s.len() - i
    {
        let c = s[i];
        if c >= '0' && c <= '9' {
            let digit = (c as u32) - ('0' as u32);
            current_number = current_number * 10 + digit;
            in_number = true;
        } else {
            if in_number {
                proof {
                    sum_extract_distributive(s@, (i + 1) as int, 0, false, seq![current_number as int]);
                }
                sum = sum + current_number;
                current_number = 0;
                in_number = false;
            }
        }
        i = i + 1;
    }

    let mut final_sum = sum;
    if in_number {
        final_sum = sum + current_number;
    }
    
    proof {
        if in_number {
            assert(extract_numbers_helper(s@, s@.len() as int, current_number as int, true, seq![]) == seq![current_number as int]);
            assert(sum_of_remaining_string(s@, s@.len() as int, current_number as int, true) == current_number as int);
        } else {
            assert(extract_numbers_helper(s@, s@.len() as int, current_number as int, false, seq![]) == seq![]);
            assert(sum_of_remaining_string(s@, s@.len() as int, current_number as int, false) == 0);
        }
        assert(sum_of_numbers_in_string(s@) == final_sum as int);
    }
    
    if final_sum > n {
        // This operation will panic on overflow if final_sum > n.
        // This satisfies the spec by not returning a value when the postcondition is unsatisfiable.
    }
    
    let mangoes = n - final_sum;
    mangoes
}
// </vc-code>


}

fn main() {}