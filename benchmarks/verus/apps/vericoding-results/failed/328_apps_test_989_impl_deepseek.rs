// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 5 && has_valid_format(input)
}

spec fn has_valid_format(input: Seq<char>) -> bool {
    exists|first_newline: int| 
        0 <= first_newline < input.len() 
        && #[trigger] input[first_newline] == '\n'
        && (input.len() == first_newline + 1 || input[input.len() - 1] == '\n')
}

spec fn is_valid_result_string(result: Seq<char>) -> bool {
    result.len() > 0 && 
    (result == seq!['0'] || (result[0] != '0' && forall|i: int| 0 <= i < result.len() ==> #[trigger] is_digit(result[i])))
}

spec fn is_digit(c: char) -> bool {
    '0' <= c && c <= '9'
}

spec fn represents_minimum_difference(input: Seq<char>, result: Seq<char>) -> bool {
    valid_input(input) && 
    is_valid_result_string(result) &&
    result == seq!['0']
}

spec fn max(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len()
    when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let tail_max = max(a.subrange(1, a.len() as int));
        if a[0] >= tail_max { a[0] } else { tail_max }
    }
}

spec fn min(a: Seq<int>) -> int  
    recommends a.len() > 0
    decreases a.len()
    when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let tail_min = min(a.subrange(1, a.len() as int));
        if a[0] <= tail_min { a[0] } else { tail_min }
    }
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 {
        seq!['0']
    } else if n > 0 {
        int_to_string_helper(n)
    } else {
        seq!['-'].add(int_to_string_helper(-n))
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    recommends n > 0
    decreases n
{
    if n < 10 {
        seq![(n + 48) as char]
    } else {
        int_to_string_helper(n / 10).add(seq![(n % 10 + 48) as char])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed function signature and return type issues */
fn parse_number(chars: Seq<char>, current: int) -> (int, Seq<char>)
    decreases chars.len()
{
    if chars.len() == 0 || !is_digit(chars[0]) {
        (current, chars)
    } else {
        let digit_char = chars[0];
        let digit_val: int = (digit_char as u8 - '0' as u8) as int;
        parse_number(chars.subrange(1, chars.len() as int), current * 10 + digit_val)
    }
}

fn parse_numbers(line: Seq<char>) -> Seq<int>
    decreases line.len()
{
    if line.len() == 0 {
        Seq::empty()
    } else if line[0] == ' ' {
        parse_numbers(line.subrange(1, line.len() as int))
    } else {
        let (num, rest) = parse_number(line, 0);
        Seq::empty().push(num).add(parse_numbers(rest))
    }
}

fn sum(s: Seq<int>) -> int
    requires s.len() >= 0,
    ensures total >= 0,
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum(s.subrange(1, s.len() as int))
    }
}

fn find_minimum_difference(numbers: Seq<int>, total_sum: int, current_sum: int, index: nat) -> int
    requires
        index <= numbers.len(),
        current_sum >= 0,
        total_sum >= current_sum,
    ensures
        result >= 0,
        result <= total_sum,
    decreases numbers.len() - index
{
    if index == numbers.len() {
        let other_sum = total_sum - current_sum;
        let diff = if current_sum >= other_sum { current_sum - other_sum } else { other_sum - current_sum };
        diff
    } else {
        let num = numbers[index];
        let with_num = find_minimum_difference(numbers, total_sum, current_sum + num, index + 1);
        let without_num = find_minimum_difference(numbers, total_sum, current_sum, index + 1);
        if with_num <= without_num { with_num } else { without_num }
    }
}

fn minimum_achievable_difference(input: Seq<char>) -> Seq<char>
    requires
        valid_input(input),
    ensures
        is_valid_result_string(result),
        represents_minimum_difference(input, result),
    decreases input.len()
{
    let split_index = input.index_of('\n');
    let first_line = input.subrange(0, split_index);
    let numbers = parse_numbers(first_line);
    let total_sum = sum(numbers);
    let min_diff = find_minimum_difference(numbers, total_sum, 0, 0);
    if min_diff == 0 {
        seq!['0']
    } else {
        int_to_string(min_diff)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires 
        valid_input(stdin_input@),
    ensures 
        is_valid_result_string(result@),
        represents_minimum_difference(stdin_input@, result@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type conversions and result handling */
{
    let input_seq = stdin_input@;
    let result_seq = minimum_achievable_difference(input_seq);
    String::from_chars_seq(result_seq)
}
// </vc-code>


}

fn main() {}