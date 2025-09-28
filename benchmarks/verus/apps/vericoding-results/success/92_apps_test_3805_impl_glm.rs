// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn extract_first_line(input: Seq<char>) -> Seq<char>
    decreases input.len()
{
    if input.len() == 0 {
        Seq::empty()
    } else if input[0] == '\n' {
        Seq::empty()
    } else {
        seq![input[0]] + extract_first_line(input.subrange(1, input.len() as int))
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
            stack.subrange(0, stack.len() - 1)
        } else {
            stack.push(c)
        };
        process_string(input.subrange(1, input.len() as int), new_stack)
    }
}

spec fn stack_algorithm_results_in_empty_stack(input: Seq<char>) -> bool
{
    let stack = process_string(input, Seq::empty());
    stack.len() == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced unsupported last() with indexing */
fn process_string_impl(input: Vec<char>) -> (result: Vec<char>) {
    let mut stack: Vec<char> = Vec::new();
    for c in input {
        if stack.len() > 0 {
            let top = stack[stack.len()-1];
            if top == c {
                stack.pop();
            } else {
                stack.push(c);
            }
        } else {
            stack.push(c);
        }
    }
    stack
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    ensures result@.len() > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed is_empty() to use len() == 0 */
{
    let processed = process_string_impl(input);
    if processed.len() == 0 {
        vec!['a']
    } else {
        processed
    }
}
// </vc-code>


}

fn main() {}