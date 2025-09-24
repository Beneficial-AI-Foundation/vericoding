// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn contains_three_space_separated_integers(input: Seq<char>) -> bool {
    exists|i: int, j: int, k: int| (0 <= i < j < k <= input.len() &&
    is_valid_integer_substring(input, 0, i) &&
    input[i] == ' ' &&
    is_valid_integer_substring(input, i+1, j) &&
    input[j] == ' ' &&
    is_valid_integer_substring(input, j+1, k) &&
    (k == input.len() || input[k] == '\n'))
}

spec fn exactly_two_are_equal(input: Seq<char>) -> bool {
    let nums = parse_three_numbers(input);
    (nums.0 == nums.1 && nums.0 != nums.2) ||
    (nums.0 == nums.2 && nums.0 != nums.1) ||
    (nums.1 == nums.2 && nums.1 != nums.0)
}

spec fn is_valid_integer_string(s: Seq<char>) -> bool {
    if s.len() == 0 { false }
    else if s.len() == 1 && s[0] == '0' { true }
    else if s.len() > 0 && s[0] == '-' { 
        s.len() > 1 && is_digit_sequence(s.subrange(1, s.len() as int)) && s[1] != '0'
    }
    else { is_digit_sequence(s) && s[0] != '0' }
}

spec fn is_digit_sequence(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && s[i] <= '9'
}

spec fn is_valid_integer_substring(s: Seq<char>, start: int, end: int) -> bool {
    if start == end { false }
    else {
        let substr = s.subrange(start, end);
        is_valid_integer_string(substr)
    }
}

spec fn find_different_number(input: Seq<char>) -> Seq<char> {
    let nums = parse_three_numbers(input);
    let different = if nums.0 == nums.1 { nums.2 }
                    else if nums.0 == nums.2 { nums.1 }
                    else { nums.0 };
    int_to_string_pure(different)
}
spec fn parse_three_numbers(input: Seq<char>) -> (int, int, int) {
    (0, 0, 0) /* placeholder for parsing logic */
}

spec fn int_to_string_pure(n: int) -> Seq<char> {
    Seq::<char>::new(1 as nat, |i: int| '0') /* placeholder for conversion logic */
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires 
        input@.len() > 0,
        contains_three_space_separated_integers(input@),
        exactly_two_are_equal(input@),
    ensures
        result@.len() > 0,
        is_valid_integer_string(result@),
        result@ == find_different_number(input@),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}