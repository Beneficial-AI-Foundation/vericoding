// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    input[input.len() as int - 1] == '\n' &&
    valid_input_structure(input)
}

spec fn valid_input_structure(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_output_format(output: Seq<char>) -> bool {
    output.len() == 0 || output[output.len() as int - 1] == '\n'
}

spec fn input_output_correspondence(input: Seq<char>, output: Seq<char>) -> bool
    recommends valid_input(input) && valid_output_format(output)
{
    true
}

spec fn process_input(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    input.subrange(0, 0)
}

spec fn can_form_palindrome(r: int, g: int, b: int, w: int) -> bool
    recommends r >= 0 && g >= 0 && b >= 0 && w >= 0
{
    let odd_count = (if r % 2 == 1 { 1int } else { 0int }) + 
                    (if g % 2 == 1 { 1int } else { 0int }) + 
                    (if b % 2 == 1 { 1int } else { 0int }) + 
                    (if w % 2 == 1 { 1int } else { 0int });
    odd_count <= 1 || 
    (r > 0 && g > 0 && b > 0 && can_form_palindrome_after_operation(r-1, g-1, b-1, w+3))
}

spec fn can_form_palindrome_after_operation(r: int, g: int, b: int, w: int) -> bool
    recommends r >= 0 && g >= 0 && b >= 0 && w >= 0
{
    let odd_count = (if r % 2 == 1 { 1int } else { 0int }) + 
                    (if g % 2 == 1 { 1int } else { 0int }) + 
                    (if b % 2 == 1 { 1int } else { 0int }) + 
                    (if w % 2 == 1 { 1int } else { 0int });
    odd_count <= 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Seq<char>) -> (result: Seq<char>)
    requires
        stdin_input.len() > 0,
        stdin_input[stdin_input.len() as int - 1] == '\n' || 
        !stdin_input.subrange(0, stdin_input.len() as int - 1).contains('\n'),
        valid_input(stdin_input),
    ensures
        result.len() >= 0,
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == 'Y' || result[i] == 'e' || result[i] == 's' || 
            result[i] == 'N' || result[i] == 'o' || result[i] == '\n' || result[i] == ' ',
        result.len() == 0 || result[result.len() as int - 1] == '\n',
        valid_output_format(result),
        input_output_correspondence(stdin_input, result),
        result == process_input(stdin_input),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}