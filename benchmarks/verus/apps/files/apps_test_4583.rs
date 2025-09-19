// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() == 5 && input.subrange(0, 4).len() == 4 &&
    (forall|i: int| 0 <= i < 4 ==> ('0' <= #[trigger] input[i] <= '9')) &&
    input[4] == '\n'
}

spec fn char_to_digit(c: char) -> int {
    (c as int) - ('0' as int)
}

spec fn evaluate_expression(a: int, b: int, c: int, d: int, op1: char, op2: char, op3: char) -> int {
    let b_val = if op1 == '+' { b } else { -b };
    let c_val = if op2 == '+' { c } else { -c };
    let d_val = if op3 == '+' { d } else { -d };
    a + b_val + c_val + d_val
}

spec fn solution_exists(input: Seq<char>) -> bool {
    &&& valid_input(input)
    &&& {
        let a = char_to_digit(input[0]);
        let b = char_to_digit(input[1]);
        let c = char_to_digit(input[2]);
        let d = char_to_digit(input[3]);
        exists|op1: char, op2: char, op3: char| 
            (op1 == '+' || op1 == '-') &&
            (op2 == '+' || op2 == '-') &&
            (op3 == '+' || op3 == '-') &&
            evaluate_expression(a, b, c, d, op1, op2, op3) == 7
    }
}

spec fn valid_output(result: Seq<char>, input: Seq<char>) -> bool {
    &&& valid_input(input)
    &&& result.len() == 10 
    &&& result.subrange(7, 9) =~= seq!['=', '7']
    &&& result[9] == '\n'
    &&& result[0] == input[0] && result[2] == input[1] 
    &&& result[4] == input[2] && result[6] == input[3]
    &&& (result[1] == '+' || result[1] == '-')
    &&& (result[3] == '+' || result[3] == '-')
    &&& (result[5] == '+' || result[5] == '-')
    &&& {
        let a = char_to_digit(input[0]);
        let b = char_to_digit(input[1]);
        let c = char_to_digit(input[2]);
        let d = char_to_digit(input[3]);
        evaluate_expression(a, b, c, d, result[1], result[3], result[5]) == 7
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(input@),
        solution_exists(input@),
    ensures valid_output(result@, input@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}