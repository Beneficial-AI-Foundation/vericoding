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
/* helper modified by LLM (iteration 2): fixed function return types */
spec fn parse_input_pure(input: Seq<char>) -> Seq<int> {
    let space1 = input.index_of(' ');
    let token1 = input.subrange(0, space1 as int);
    let rest1 = input.subrange(space1 as int + 1, input.len());

    let space2 = rest1.index_of(' ');
    let token2 = rest1.subrange(0, space2 as int);
    let token3 = rest1.subrange(space2 as int + 1, rest1.len());

    seq![parse_int_spec(token1), parse_int_spec(token2), parse_int_spec(token3)]
}

spec fn parse_int_spec(token: Seq<char>) -> int {
    if token.len() == 0 {
        0
    } else {
        let first = token[0];
        let first_digit = (first as int) - ('0' as int);
        let rest_value = parse_int_spec(token.subrange(1, token.len()));
        first_digit * 10^(token.len()-1) + rest_value
    }
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n < 0 {
        seq!['-'] + int_to_string(-n)
    } else if n == 0 {
        seq!['0']
    } else {
        let last_digit = n % 10;
        let rest = n / 10;
        if rest == 0 {
            seq![('0' as int + last_digit) as char]
        } else {
            int_to_string(rest) + seq![('0' as int + last_digit) as char]
        }
    }
}

fn parse_input_exec(input: &str) -> (int, int, int)
    ensures 
        parse_input_pure(input@) == seq![r, d, x0]
{
    let tokens: Vec<&str> = input.split_whitespace().collect();
    assert(tokens.len() == 3);
    let r = parse_int_exec(tokens[0]);
    let d = parse_int_exec(tokens[1]);
    let x0 = parse_int_exec(tokens[2]);
    (r, d, x0)
}

fn parse_int_exec(s: &str) -> int
    ensures 
        n >= 0
{
    let mut n = 0;
    for c in s.chars() {
        let digit = (c as int) - ('0' as int);
        assert(0 <= digit <= 9);
        n = n * 10 + digit;
    }
    n
}

fn int_to_string_exec(n: int) -> String
    ensures 
        s@ == int_to_string(n)
{
    if n < 0 {
        let mut s = String::from("-");
        s.push_str(&int_to_string_exec(-n));
        s
    } else if n == 0 {
        "0".to_string()
    } else {
        let mut s = String::new();
        let mut num = n;
        let mut digits = Vec::new();
        while num > 0
            invariant 
                num >= 0
        {
            let digit = num % 10;
            let c = ('0' as int + digit) as char;
            digits.push(c);
            num = num / 10;
        }
        digits.reverse();
        for c in digits {
            s.push(c);
        }
        s
    }
}

fn generate_expected_output_exec(r: int, d: int, x0: int) -> String
    ensures 
        s@ == generate_expected_output(r, d, x0)
{
    let mut output = String::new();
    let mut current = x0;
    let mut i = 1;
    while i <= 10
        invariant
            output@ == generate_output_up_to_iteration(r, d, x0, i-1),
            1 <= i <= 11,
            current == calculate_recurrence(r, d, x0, i-1)
        decreases 11 - i
    {
        let next = r * current - d;
        let next_str = int_to_string_exec(next);
        output.push_str(&next_str);
        output.push_str("\n");
        current = next;
        i += 1;
    }
    output
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
    /* code modified by LLM (iteration 2): implemented main logic */
    let (r, d, x0) = parse_input_exec(input);
    let result = generate_expected_output_exec(r, d, x0);
    result
}
// </vc-code>


}

fn main() {}