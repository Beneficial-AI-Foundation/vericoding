// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: String) -> bool {
    input.len() > 0
}

spec fn valid_output(input: String, output: String) -> bool {
    let input_pairs = get_input_pairs(input);
    let expected_results = Seq::new(input_pairs.len() as nat, |i: int| 
        if 0 <= i < input_pairs.len() {
            if input_pairs[i].0 > 0 && input_pairs[i].1 >= 0 {
                compute_minimum_cost(input_pairs[i].0, input_pairs[i].1)
            } else {
                0
            }
        } else {
            0
        }
    );
    output == format_results(expected_results)
}

spec fn compute_minimum_cost(c: int, s: int) -> int {
    if c > 0 && s >= 0 {
        let a = s / c;
        let r = s % c;
        (c - r) * a * a + r * (a + 1) * (a + 1)
    } else {
        0
    }
}

spec fn get_input_pairs(input: String) -> Seq<(int, int)> {
    if input.len() > 0 {
        let lines = split_lines(input);
        if lines.len() == 0 {
            seq![]
        } else {
            let n = parse_int(lines[0]);
            get_pairs_from_lines(lines, 1, n)
        }
    } else {
        seq![]
    }
}

spec fn format_results(results: Seq<int>) -> String {
    format_results_helper(results, 0, "")
}

#[verifier::external_body]
spec fn split_lines(input: String) -> Seq<String> {
    seq![]
}

#[verifier::external_body]
spec fn parse_int(line: String) -> int {
    0
}

#[verifier::external_body]
spec fn get_pairs_from_lines(lines: Seq<String>, start: int, n: int) -> Seq<(int, int)> {
    seq![]
}

#[verifier::external_body]
spec fn format_results_helper(results: Seq<int>, index: int, acc: &str) -> String {
    String::new()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires valid_input(input)
    ensures valid_output(input, result)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    String::new()
    // impl-end
}
// </vc-code>


}

fn main() {}