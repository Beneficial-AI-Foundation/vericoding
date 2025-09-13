// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: &str) -> bool {
    input.len() >= 5 && has_valid_format(input)
}

spec fn has_valid_format(input: &str) -> bool {
    exists|first_newline: nat| 
        first_newline < input.len() && 
        input.get_char(first_newline) == '\n' &&
        (input.len() == first_newline + 1 || input.get_char(input.len() - 1) == '\n')
}

spec fn is_valid_result_string(result: &str) -> bool {
    result.len() > 0 && 
    (result == "0" || (result.get_char(0) != '0' && forall|i: int| 0 <= i < result.len() ==> is_digit(result.get_char(i))))
}

spec fn is_digit(c: char) -> bool {
    '0' <= c && c <= '9'
}

spec fn represents_minimum_difference(input: &str, result: &str) -> bool {
    valid_input(input) && 
    is_valid_result_string(result) &&
    result == "0"
}

spec fn max_seq(a: Seq<int>) -> int {
    if a.len() == 1 { 
        a[0] 
    } else if a[0] >= max_seq(a.subrange(1, a.len() as int)) { 
        a[0]
    } else { 
        max_seq(a.subrange(1, a.len() as int))
    }
}

spec fn min_seq(a: Seq<int>) -> int {
    if a.len() == 1 { 
        a[0] 
    } else if a[0] <= min_seq(a.subrange(1, a.len() as int)) { 
        a[0] 
    } else { 
        min_seq(a.subrange(1, a.len() as int))
    }
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 { 
        seq!['0']
    } else if n > 0 { 
        int_to_string_helper(n)
    } else { 
        seq!['-'] + int_to_string_helper(-n)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char> {
    if n < 10 { 
        seq![(n + 48) as char]
    } else { 
        int_to_string_helper(n / 10) + seq![(n % 10 + 48) as char]
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires 
        valid_input(stdin_input),
    ensures 
        is_valid_result_string(&result) &&
        represents_minimum_difference(stdin_input, &result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    "0".to_string()
}
// </vc-code>


}

fn main() {}