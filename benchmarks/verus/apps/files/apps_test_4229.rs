// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_to_string(i: int) -> Seq<char> {
    seq!['1']
}

spec fn parse_int_from_string(s: Seq<char>) -> int {
    1
}

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0
}

spec fn sum_of_non_fizzbuzz_numbers(n: int) -> int
    decreases n
{
    if n == 0 { 
        0 
    } else {
        let num = n;
        if num % 3 > 0 && num % 5 > 0 {
            sum_of_non_fizzbuzz_numbers(n - 1) + num
        } else {
            sum_of_non_fizzbuzz_numbers(n - 1)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(stdin_input)
    ensures result.len() > 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}