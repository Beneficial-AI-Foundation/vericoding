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
    /* code modified by LLM (iteration 4): Use @ operator for indexing spec sequences */
    let tokens = parse_input_pure(input@);
    let r = tokens@[0];
    let d = tokens@[1];
    let x0 = tokens@[2];
    
    let mut output = String::new();
    let mut current = x0;
    let mut i: usize = 1;
    
    while i <= 10
        invariant
            1 <= i <= 11,
            i <= 10 ==> current == if i == 1 { x0 } else { calculate_recurrence(r, d, x0, i - 1) },
            i > 10 ==> current == calculate_recurrence(r, d, x0, 10),
            output@ == generate_output_up_to_iteration(r, d, x0, (i - 1) as int),
            2 <= r <= 5,
            1 <= d <= 100,
            d < x0 <= 200,
        decreases 11 - i
    {
        current = r * current - d;
        output = output + &current.to_string() + "\n";
        
        proof {
            assert(current == calculate_recurrence(r, d, x0, i as int));
            assert(output@ == generate_output_up_to_iteration(r, d, x0, (i - 1) as int) + int_to_string(current) + seq!['\n']);
            assert(output@ == generate_output_up_to_iteration(r, d, x0, i as int));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == 11);
        assert(output@ == generate_output_up_to_iteration(r, d, x0, 10));
        assert(output@ == generate_expected_output(r, d, x0));
    }
    
    output
}
// </vc-code>


}

fn main() {}