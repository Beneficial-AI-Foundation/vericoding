// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_output(input: Seq<char>, output: Seq<char>) -> bool {
    &&& valid_input(input)
    &&& {
        let input_pairs = get_input_pairs(input);
        let expected_results = Seq::new(input_pairs.len(), |i: int| 
            if input_pairs[i].0 > 0 && input_pairs[i].1 >= 0 {
                compute_minimum_cost(input_pairs[i].0, input_pairs[i].1)
            } else {
                0
            });
        output == format_results(expected_results)
    }
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

spec fn get_input_pairs(input: Seq<char>) -> Seq<(int, int)> {
    if input.len() > 0 {
        let lines = split_lines(input);
        if lines.len() == 0 {
            Seq::new(0, |i: int| (0, 0))
        } else {
            let n = parse_int(lines[0]);
            get_pairs_from_lines(lines, 1, n)
        }
    } else {
        Seq::new(0, |i: int| (0, 0))
    }
}

spec fn format_results(results: Seq<int>) -> Seq<char> {
    if forall|j: int| 0 <= j < results.len() ==> results[j] >= 0 {
        format_results_helper(results, 0, Seq::new(0, |i: int| 'a'))
    } else {
        Seq::new(0, |i: int| 'a')
    }
}

#[verifier::external_body]
spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>> {
    Seq::new(0, |i: int| Seq::new(0, |j: int| 'a'))
}

#[verifier::external_body]
spec fn parse_int(line: Seq<char>) -> int {
    0
}

#[verifier::external_body]
spec fn get_pairs_from_lines(lines: Seq<Seq<char>>, start: int, n: int) -> Seq<(int, int)> {
    Seq::new(0, |i: int| (0, 0))
}

#[verifier::external_body]
spec fn format_results_helper(results: Seq<int>, index: int, acc: Seq<char>) -> Seq<char> {
    Seq::new(0, |i: int| 'a')
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(input)
    ensures valid_output(input, result)
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