// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>> {
    seq![seq![]]
}

spec fn is_valid_number(s: Seq<char>) -> bool {
    true
}

spec fn parse_int(s: Seq<char>) -> int
    recommends is_valid_number(s)
{
    0
}

spec fn is_binary_string(s: Seq<char>) -> bool {
    true
}

spec fn ends_with_newline(s: Seq<char>) -> bool {
    s.len() > 0 && s[s.len() - 1] == '\n'
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    input[input.len() - 1] == '\n' &&
    {
        let lines = split_lines(input);
        lines.len() >= 2 &&
        is_valid_number(lines[0]) &&
        {
            let t = parse_int(lines[0]);
            t >= 1 && t <= 100 &&
            lines.len() == t + 1 &&
            forall|i: int| 1 <= i < lines.len() ==> 
                is_binary_string(lines[i]) && lines[i].len() >= 1 && lines[i].len() <= 1000
        }
    }
}

spec fn valid_output(result: Seq<char>) -> bool {
    result.len() > 0 &&
    (ends_with_newline(result) || result.len() == 0) &&
    {
        let output_lines = split_lines(result);
        output_lines.len() >= 1 &&
        (forall|i: int| 0 <= i < output_lines.len() - 1 ==> is_valid_number(output_lines[i])) &&
        (forall|i: int| 0 <= i < output_lines.len() - 1 ==> parse_int(output_lines[i]) >= 0)
    }
}

spec fn correct_result(input: Seq<char>, result: Seq<char>) -> bool
    recommends valid_input(input)
{
    {
        let input_lines = split_lines(input);
        let t = parse_int(input_lines[0]);
        let output_lines = split_lines(result);
        output_lines.len() == t + 1 &&
        forall|test_case: int| 0 <= test_case < t ==> #[trigger] parse_int(output_lines[test_case]) == min_operations_to_make_good(input_lines[test_case + 1])
    }
}

spec fn min_operations_to_make_good(s: Seq<char>) -> int
    recommends is_binary_string(s)
{
    if s.len() == 0 { 0 } else { min_ops_helper(s, 0, s.len() as int) }
}

spec fn min_ops_helper(s: Seq<char>, start: int, end: int) -> int {
    0
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
        correct_result(input, result),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}