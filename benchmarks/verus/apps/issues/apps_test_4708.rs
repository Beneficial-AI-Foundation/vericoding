// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_string(input, '\n');
    lines.len() >= 4 &&
    is_valid_integer(lines[0]) &&
    is_valid_integer(lines[1]) &&
    is_valid_integer(lines[2]) &&
    is_valid_integer(lines[3]) &&
    {
        let n = string_to_int(lines[0]);
        let k = string_to_int(lines[1]);
        let x = string_to_int(lines[2]);
        let y = string_to_int(lines[3]);
        1 <= n <= 10000 && 1 <= k <= 10000 && 1 <= y < x <= 10000
    }
}

spec fn valid_output(output: Seq<char>, input: Seq<char>) -> bool {
    let lines = split_string(input, '\n');
    if lines.len() >= 4 && 
       is_valid_integer(lines[0]) &&
       is_valid_integer(lines[1]) &&
       is_valid_integer(lines[2]) &&
       is_valid_integer(lines[3]) {
        let n = string_to_int(lines[0]);
        let k = string_to_int(lines[1]);
        let x = string_to_int(lines[2]);
        let y = string_to_int(lines[3]);
        let expected_ans = if k < n { k * x + (n - k) * y } else { n * x };
        output == int_to_string(expected_ans) + seq!['\n']
    } else {
        output.len() == 0
    }
}

spec fn split_string(s: Seq<char>, delimiter: char) -> Seq<Seq<char>> {
    seq![]
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    true
}

spec fn string_to_int(s: Seq<char>) -> int {
    0
}

spec fn int_to_string(n: int) -> Seq<char> {
    seq![]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (output: Seq<char>)
    requires input.len() > 0
    ensures valid_output(output, input)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}