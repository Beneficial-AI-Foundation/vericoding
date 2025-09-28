// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool
    recommends input.len() > 0
{
    let tokens = parse_input_pure(input);
    tokens.len() == 3 && 
    2 <= tokens[0] <= 5 &&
    1 <= tokens[1] <= 100 &&
    tokens[1] < tokens[2] && tokens[2] <= 200
}

spec fn calculate_recurrence(r: int, d: int, x0: int, n: int) -> int
    recommends n >= 1
    decreases n when n >= 1
{
    if n == 1 { r * x0 - d }
    else if n >= 2 { r * calculate_recurrence(r, d, x0, n - 1) - d }
    else { 0 }
}

spec fn generate_expected_output(r: int, d: int, x0: int) -> Seq<char> {
    generate_output_up_to_iteration(r, d, x0, 10)
}

spec fn generate_output_up_to_iteration(r: int, d: int, x0: int, iterations: int) -> Seq<char>
    recommends iterations >= 0
    decreases iterations when iterations >= 0
{
    if iterations == 0 { 
        Seq::empty() 
    } else if iterations >= 1 { 
        let current_value = calculate_recurrence(r, d, x0, iterations);
        let previous_output = generate_output_up_to_iteration(r, d, x0, iterations - 1);
        previous_output + int_to_string(current_value) + seq!['\n']
    } else {
        Seq::empty()
    }
}

spec fn parse_input_pure(input: Seq<char>) -> Seq<int> {
    seq![1, 1, 100]  /* placeholder */
}

spec fn int_to_string(n: int) -> Seq<char> {
    seq!['0']  /* placeholder */
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): parse_input_pure implementation */
spec fn parse_input_pure(input: Seq<char>) -> Seq<int>
{
    let lines = split_by_whitespace(input);
    if lines.len() != 3 {
        seq![0, 0, 0] // Should not happen given valid_input implies 3 tokens
    } else {
        let r_str = lines[0];
        let d_str = lines[1];
        let x0_str = lines[2];
        seq![parse_int_from_slice(r_str), parse_int_from_slice(d_str), parse_int_from_slice(x0_str)]
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires 
        input@.len() > 0,
        valid_input(input@),
    ensures 
        result@ == generate_expected_output(
            parse_input_pure(input@)[0], 
            parse_input_pure(input@)[1], 
            parse_input_pure(input@)[2]
        )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix type errors for `nat` and `int` in conditions */
{
    let input_seq = input@;
    let tokens: Seq<int> = parse_input_pure(input_seq);

    let r_val = tokens.index(0);
    let d_val = tokens.index(1);
    let x0_val = tokens.index(2);

    let mut output: Seq<char> = Seq::empty();
    let mut current_x = x0_val;

    let mut i: nat = 1;
    while i <= 10
        invariant
            1 <= i as int <= 11,
            (i == 1) ==> current_x == x0_val,
            (i > 1) ==> current_x == calculate_recurrence(r_val, d_val, x0_val, i as int - 1),
            output == generate_output_up_to_iteration(r_val, d_val, x0_val, i as int - 1),
        decreases 10 - (i as int)
    {
        if i > 1 {
            current_x = r_val * current_x - d_val;
        }

        let val_str = int_to_string(current_x);
        output = output.add(val_str).add(seq!['\n']);
        i = i + 1;
    }

    String::from_str_ascii(output)
}
// </vc-code>


}

fn main() {}