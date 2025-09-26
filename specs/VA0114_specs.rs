// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_func(input: Seq<char>, delimiter: char) -> Seq<Seq<char>> {
    seq![]
}

spec fn parse_int_func(s: Seq<char>) -> int {
    0
}

spec fn process_test_cases_helper(input: Seq<char>, lines: Seq<Seq<char>>, line_idx: int, case_idx: int, total_cases: int, acc: Seq<int>) -> Seq<int> {
    seq![]
}

spec fn format_output_helper(results: Seq<int>, idx: int, acc: Seq<char>) -> Seq<char> {
    seq![]
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    {
        let lines = split_func(input, '\n');
        lines.len() >= 1 &&
        parse_int_func(lines[0]) >= 0 &&
        lines.len() >= 1 + 3 * parse_int_func(lines[0])
    }
}

spec fn process_test_cases(input: Seq<char>) -> Seq<int> {
    if valid_input(input) {
        let lines = split_func(input, '\n');
        let t = parse_int_func(lines[0]);
        process_test_cases_helper(input, lines, 1, 0, t, seq![])
    } else {
        seq![]
    }
}

spec fn format_output(results: Seq<int>) -> Seq<char> {
    format_output_helper(results, 0, seq![])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires
        input.len() > 0,
        valid_input(input),
    ensures
        result.len() >= 0,
        result == format_output(process_test_cases(input)),
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