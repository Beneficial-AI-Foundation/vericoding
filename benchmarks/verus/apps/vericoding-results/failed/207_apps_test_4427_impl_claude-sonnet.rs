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
fn parse_input(input: &str) -> (result: (i32, i32, i32))
    requires
        input@.len() > 0,
        valid_input(input@),
    ensures
        result.0 == parse_input_pure(input@)[0],
        result.1 == parse_input_pure(input@)[1],
        result.2 == parse_input_pure(input@)[2],
{
    let input_str = input.to_string();
    let parts: Vec<&str> = input_str.split_whitespace().collect();
    let r = parts[0].parse::<i32>().unwrap();
    let d = parts[1].parse::<i32>().unwrap();
    let x0 = parts[2].parse::<i32>().unwrap();
    (r, d, x0)
}

fn calculate_sequence_value(r: i32, d: i32, x0: i32, n: i32) -> (result: i32)
    requires
        n >= 1,
    ensures
        result == calculate_recurrence(r as int, d as int, x0 as int, n as int),
{
    /* helper modified by LLM (iteration 3): fixed to avoid iterators */
    let mut current = x0;
    let mut i = 1;
    
    while i < n
        invariant
            1 <= i <= n,
            current == calculate_recurrence(r as int, d as int, x0 as int, i as int),
        decreases n - i
    {
        current = r * current - d;
        i += 1;
    }
    
    if n == 1 {
        r * x0 - d
    } else {
        current = r * current - d;
        current
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
{
    /* code modified by LLM (iteration 3): fixed compilation by avoiding iterators */
    let (r, d, x0) = parse_input(input);
    let mut output = String::new();
    
    let mut i = 1;
    while i <= 10
        invariant
            1 <= i <= 11,
            output@.len() >= 0,
        decreases 10 - i
    {
        let value = calculate_sequence_value(r, d, x0, i);
        output.push_str(&value.to_string());
        output.push('\n');
        i += 1;
    }
    
    output
}
// </vc-code>


}

fn main() {}