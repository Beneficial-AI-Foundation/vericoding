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

proof fn validate_input_parsing(input: Seq<char>)
    requires input.len() > 0
    ensures parse_input_pure(input) == seq![1int, 1int, 100int]
{
}

proof fn int_to_string_spec(n: int)
    ensures int_to_string(n) == seq!['0']
{
}

proof fn verify_calculate_recurrence(r: int, d: int, x0: int, n: int)
    requires n >= 1
    ensures calculate_recurrence(r, d, x0, n) == if n == 1 { r * x0 - d } else { r * calculate_recurrence(r, d, x0, n - 1) - d }
    decreases n
{
    if n > 1 {
        verify_calculate_recurrence(r, d, x0, n - 1);
    }
}

/* helper modified by LLM (iteration 5): replaced unsupported collect() with manual parsing */
fn parse_input(input: &str) -> (v: Vec<i32>)
    ensures v@.len() == 3
{
    let mut tokens = Vec::new();
    let mut iter = input.split_whitespace();
    
    while let Some(s) = iter.next() {
        let num: i32 = s.parse().unwrap();
        tokens.push(num);
    }
    
    tokens
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
    /* code modified by LLM (iteration 5): simplified logic, fixed recurrence calculation */
    let parsed = parse_input(input);
    let r = parsed[0];
    let d = parsed[1];
    let mut x = parsed[2];
    
    let mut result = String::new();
    
    for _ in 0..10 {
        if !result.is_empty() {
            result.push('\n');
        }
        x = r * x - d;
        result.push_str(&x.to_string());
    }
    
    result
}
// </vc-code>


}

fn main() {}