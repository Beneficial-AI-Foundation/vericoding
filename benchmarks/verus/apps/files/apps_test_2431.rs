// <vc-preamble>
use vstd::prelude::*;

verus! {

struct TestCase {
    n: nat,
    x: nat,
    y: nat,
    z: nat,
    castles: Seq<nat>,
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    valid_input_structure(input)
}

spec fn valid_input_structure(input: Seq<char>) -> bool {
    true /* TODO: implement input validation */
}

spec fn valid_output(input: Seq<char>, output: Seq<char>) -> bool
    recommends valid_input(input)
{
    output.len() > 0 &&
    valid_output_structure(input, output)
}

spec fn valid_output_structure(input: Seq<char>, output: Seq<char>) -> bool {
    true /* TODO: implement output validation */
}

spec fn get_test_count(s: Seq<char>) -> nat
    recommends valid_input(s)
{
    1 /* TODO: implement test count parsing */
}

spec fn get_test_case(s: Seq<char>, i: nat) -> TestCase
    recommends valid_input(s) && i < get_test_count(s)
{
    TestCase {
        n: 1,
        x: 1,
        y: 1,
        z: 1,
        castles: seq![1],
    }
}

spec fn count_winning_first_moves(tc: TestCase) -> nat {
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures valid_output(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}

fn main() {}