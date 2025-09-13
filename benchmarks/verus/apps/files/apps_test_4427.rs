// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn parse_input_pure(input: &str) -> Seq<int> {
    Seq::<int>::empty()
}

spec fn int_to_string(val: int) -> Seq<char> {
    Seq::<char>::empty()
}

spec fn valid_input(input: &str) -> bool
    recommends input.len() > 0
{
    let tokens = parse_input_pure(input);
    tokens.len() == 3 && 
    2 <= tokens[0] <= 5 &&
    1 <= tokens[1] <= 100 &&
    tokens[1] < tokens[2] <= 200
}

spec fn calculate_recurrence(r: int, d: int, x0: int, n: int) -> int
    recommends n >= 1
    decreases n
{
    if n == 1 { r * x0 - d }
    else { r * calculate_recurrence(r, d, x0, n - 1) - d }
}

spec fn generate_expected_output(r: int, d: int, x0: int) -> Seq<char> {
    generate_output_up_to_iteration(r, d, x0, 10)
}

spec fn generate_output_up_to_iteration(r: int, d: int, x0: int, iterations: int) -> Seq<char>
    recommends iterations >= 0
{
    if iterations == 0 { Seq::<char>::empty() }
    else { 
        let current_value = calculate_recurrence(r, d, x0, iterations);
        let previous_output = generate_output_up_to_iteration(r, d, x0, iterations - 1);
        previous_output + int_to_string(current_value) + seq!['\n']
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires 
        input.len() > 0,
        valid_input(input)
    ensures ({
        let tokens = parse_input_pure(input);
        result@ == generate_expected_output(tokens[0], tokens[1], tokens[2])
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}