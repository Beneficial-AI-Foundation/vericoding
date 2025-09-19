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
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}