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
/* helper modified by LLM (iteration 5): Removed redundant helper for `sum_sequence` to avoid confusion. */
// </vc-helpers>

// <vc-spec>
fn fruit_distribution(s: &Vec<char>, n: u32) -> (mangoes: u32)
    requires valid_input(n as int)
    ensures mangoes as int == (n as int) - sum_of_numbers_in_string(s@),
            (mangoes as int >= 0) <==> ((n as int) >= sum_of_numbers_in_string(s@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected casting within loop to `char` instead of `int`. */
{
    let mut total_numbers_in_string: int = 0;
    let mut current_number: int = 0;
    let mut in_number: bool = false;

    let s_seq = s@;

    let mut i: int = 0;
    while i < s_seq.len()
        invariant
            0 <= i <= s_seq.len(),
            current_number >= 0,
            total_numbers_in_string >= 0,
        decreases s_seq.len() - i
    {
        let c = s_seq[i];
        if '0' <= c && c <= '9' {
            let digit: int = (c as char) as int - ('0' as char) as int;
            current_number = current_number * 10 + digit;
            in_number = true;
        } else {
            if in_number {
                total_numbers_in_string = total_numbers_in_string + current_number;
                current_number = 0;
                in_number = false;
            }
        }
        i = i + 1;
    }

    if in_number {
        total_numbers_in_string = total_numbers_in_string + current_number;
    }

    let sum_val: int = total_numbers_in_string;

    let mangoes_val: int = n as int - sum_val;

    (mangoes_val as u32)
}
// </vc-code>


}

fn main() {}