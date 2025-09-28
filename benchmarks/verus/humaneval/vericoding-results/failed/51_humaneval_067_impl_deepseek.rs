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

proof fn lemma_add_one_bound(n: int, m: int)
    requires n >= 0, m >= 0,
    ensures n + m >= 0,
{
}

proof fn lemma_push_sequence_nonnegative(numbers: Seq<int>, x: int)
    requires x >= 0,
    ensures sum_sequence(numbers.push(x)) == sum_sequence(numbers) + x,
    decreases numbers.len(),
{
    if numbers.len() == 0 {
    } else {
        lemma_push_sequence_nonnegative(numbers.subrange(1, numbers.len() as int), x);
    }
}

/* helper modified by LLM (iteration 5): Fixed proof function parameter types to match spec */
proof fn lemma_extract_numbers_nonnegative(s: Seq<char>, i: int, current_number: int, in_number: bool, numbers: Seq<int>)
    requires 0 <= i <= s.len(), current_number >= 0,
    ensures sum_sequence(extract_numbers_helper(s, i, current_number, in_number, numbers)) >= 0,
    decreases s.len() - i,
{
    if i < s.len() {
        let c = s[i];
        if '0' <= c && c <= '9' {
            let digit = c as int - '0' as int;
            assert(digit >= 0) by { /* digit from '0'-'9' is between 0 and 9 */ };
            lemma_add_one_bound(current_number, digit);
            lemma_extract_numbers_nonnegative(s, i + 1, current_number * 10 + digit, true, numbers);
        } else {
            if in_number {
                lemma_push_sequence_nonnegative(numbers, current_number);
                lemma_extract_numbers_nonnegative(s, i + 1, 0, false, numbers.push(current_number));
            } else {
                lemma_extract_numbers_nonnegative(s, i + 1, 0, false, numbers);
            }
        }
    } else {
        if in_number {
            lemma_push_sequence_nonnegative(numbers, current_number);
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
    /* code modified by LLM (iteration 5): Fixed types to match helper function requirements */
    let mut i = 0;
    let mut current_number = 0;
    let mut in_number = false;
    let mut mangoes = n;
    
    proof {
        lemma_extract_numbers_nonnegative(s@, 0, 0, false, seq![]);
    }
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            current_number >= 0,
            mangoes as int == (n as int) - sum_sequence(extract_numbers_helper(s@, i as int, current_number, in_number, seq![])),
        decreases s.len() - i,
    {
        let c = s[i];
        if ('0' <= c && c <= '9') {
            let digit = c as u32 - '0' as u32;
            current_number = current_number * 10 + digit;
            in_number = true;
        } else {
            if in_number {
                mangoes = mangoes - current_number as u32;
                current_number = 0;
                in_number = false;
            }
        }
        i = i + 1;
    }
    
    if in_number {
        mangoes = mangoes - current_number as u32;
    }
    
    mangoes
}
// </vc-code>


}

fn main() {}