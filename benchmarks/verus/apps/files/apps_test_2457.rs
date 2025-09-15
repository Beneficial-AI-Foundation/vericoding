// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    true
}

spec fn valid_test_case(n: int, a: int, b: int, c: int, d: int) -> bool {
    n >= 1 && n <= 1000 &&
    a >= 0 && a <= 1000 &&
    b >= 0 && b < a &&
    c >= 0 && c <= 1000 &&
    d >= 0 && d < c
}

spec fn can_achieve_weight(n: int, a: int, b: int, c: int, d: int) -> bool {
    let min_weight = (a - b) * n;
    let max_weight = (a + b) * n;
    let target_min = c - d;
    let target_max = c + d;
    !(min_weight > target_max || max_weight < target_min)
}

spec fn valid_output(output: Seq<char>) -> bool {
    true
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires
        valid_input(input),
    ensures
        valid_output(result),
        (input.len() == 0 || (input.len() == 1 && input[0] == '\n')) ==> result.len() == 0,
        !(input.len() == 0 || (input.len() == 1 && input[0] == '\n')) ==> 
            (result.len() > 0 ==> 
                result[result.len() - 1] == '\n' || 
                (result.len() > 3 && (result.subrange(result.len() - 4, result.len() as int) == seq!['Y', 'e', 's', '\n'] || 
                                     result.subrange(result.len() - 3, result.len() as int) == seq!['N', 'o', '\n']))),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}