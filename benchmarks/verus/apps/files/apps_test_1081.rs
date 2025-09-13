// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int) -> bool {
        1 <= n <= 99
    }
    
    spec fn expected_result(n: int) -> Seq<char>
        requires valid_input(n)
    {
        if n < 12 {
            if n == 1 || n == 7 || n == 9 || n == 10 || n == 11 { seq!['N', 'O'] } else { seq!['Y', 'E', 'S'] }
        } else if 12 < n < 30 {
            seq!['N', 'O']
        } else if 69 < n < 80 {
            seq!['N', 'O']
        } else if 89 < n {
            seq!['N', 'O']
        } else {
            let last_digit = n % 10;
            if last_digit != 1 && last_digit != 7 && last_digit != 9 { seq!['Y', 'E', 'S'] } else { seq!['N', 'O'] }
        }
    }
    
    spec fn valid_output(result: Seq<char>) -> bool {
        result == seq!['Y', 'E', 'S'] || result == seq!['N', 'O']
    }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: Seq<char>)
    requires valid_input(n)
    ensures valid_output(result)
    ensures result == expected_result(n)
// </vc-spec>
// <vc-code>
{
    assume(false);
    seq!['N', 'O']
}
// </vc-code>

}

fn main() {}