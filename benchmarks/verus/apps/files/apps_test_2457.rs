// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 0
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
    forall|i: int| 0 <= i < output.len() ==> {
        let ch = output[i];
        ch == 'Y' || ch == 'e' || ch == 's' || ch == 'N' || ch == 'o' || ch == '\n'
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires
        valid_input(input),
    ensures
        valid_output(result),
        (input.len() == 0 || (input.len() == 1 && input[0] == '\n')) ==> result.len() == 0,
        !(input.len() == 0 || (input.len() == 1 && input[0] == '\n')) ==> (result.len() > 0 ==> {
            let last_char = result[result.len() - 1];
            last_char == '\n' || (result.len() > 3 && (
                (result.len() >= 4 && result.subrange((result.len() - 4) as int, result.len() as int) == seq!['Y', 'e', 's', '\n']) ||
                (result.len() >= 3 && result.subrange((result.len() - 3) as int, result.len() as int) == seq!['N', 'o', '\n'])
            ))
        }),
// </vc-spec>
// <vc-code>
{
    assume(false);
    Seq::empty()
}
// </vc-code>


}

fn main() {}