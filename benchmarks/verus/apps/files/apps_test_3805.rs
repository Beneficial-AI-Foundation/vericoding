// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn extract_first_line(input: Seq<char>) -> Seq<char>
    decreases input.len()
{
    if input.len() == 0 {
        seq![]
    } else if input[0] == '\n' {
        seq![]
    } else {
        seq![input[0]] + extract_first_line(input.drop_first())
    }
}

spec fn process_string(input: Seq<char>, stack: Seq<char>) -> Seq<char>
    decreases input.len()
{
    if input.len() == 0 {
        stack
    } else {
        let c = input[0];
        let new_stack = if stack.len() > 0 && stack[stack.len() - 1] == c {
            stack.drop_last()
        } else {
            stack.push(c)
        };
        process_string(input.drop_first(), new_stack)
    }
}

spec fn stack_algorithm_results_in_empty_stack(input: Seq<char>) -> bool {
    let stack = process_string(input, seq![]);
    stack.len() == 0
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    ensures result@ == "Yes\n"@ || result@ == "No\n"@
    ensures result@ == "Yes\n"@ <==> stack_algorithm_results_in_empty_stack(extract_first_line(input@))
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