// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_parsed_input(parts: Seq<Seq<char>>) -> bool {
    parts.len() == 3 && parts[0].len() > 0 && parts[1].len() > 0 && parts[2].len() > 0
}

spec fn is_word_chain(a: Seq<char>, b: Seq<char>, c: Seq<char>) -> bool {
    a.len() > 0 && b.len() > 0 && c.len() > 0 &&
    a[a.len() - 1] == b[0] && b[b.len() - 1] == c[0]
}

spec fn split_on_spaces(s: Seq<char>) -> Seq<Seq<char>>;

spec fn expected_result(input: Seq<char>) -> Seq<char> {
    let stripped = if input.len() > 0 && input[input.len() - 1] == '\n' {
        input.subrange(0, input.len() - 1)
    } else {
        input
    };
    let parts = split_on_spaces(stripped);
    if valid_parsed_input(parts) {
        if is_word_chain(parts[0], parts[1], parts[2]) {
            seq!['Y', 'E', 'S', '\n']
        } else {
            seq!['N', 'O', '\n']
        }
    } else {
        seq![]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added an `uninterp` keyword to the `split_on_spaces` spec function. This is a compilation error fix. The `split_on_spaces` is intentionally left uninterpreted in this case, as its precise logic is not critical to the current problem, and we are mainly focused on its effect on the `expected_result` function. */
uninterp spec fn split_on_spaces(s: Seq<char>) -> Seq<Seq<char>>; 
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@ == expected_result(input@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `pop_back` usage since it's a `Vec` method and should be called on `stripped_input_vec`. Also, fixed indexing on `parts` by using `@` to convert `Seq` to `Vec` as `parts` is a `Seq<Seq<char>>` and the function `is_word_chain` expects `Seq<char>` arguments, thus direct indexing using `parts[idx]` would be a compiler error as it tries to index into a `Seq` and pass another `Seq` into a function that expects a `Seq<char>` after a type conversion. */
{
    let mut stripped_input_vec = input;
    if stripped_input_vec.len() > 0 && stripped_input_vec[stripped_input_vec.len() - 1] == '\n' {
        stripped_input_vec.pop(); // Use pop() for Vec<char>
    }

    let stripped_seq = stripped_input_vec@;
    let parts = split_on_spaces(stripped_seq);

    if valid_parsed_input(parts) {
        if is_word_chain(parts@[0], parts@[1], parts@[2]) {
            vec!['Y', 'E', 'S', '\n']
        } else {
            vec!['N', 'O', '\n']
        }
    } else {
        vec![]
    }
}
// </vc-code>


}

fn main() {}