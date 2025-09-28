// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn char_to_pos_spec(c: Seq<char>) -> int {
    if c.len() == 1 && c[0] == 'v' { 0 }
    else if c.len() == 1 && c[0] == '>' { 1 }
    else if c.len() == 1 && c[0] == '^' { 2 }
    else if c.len() == 1 && c[0] == '<' { 3 }
    else { 0 }
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_output(result: Seq<char>) -> bool {
    result == seq!['c', 'w'] || result == seq!['c', 'c', 'w'] || result == seq!['u', 'n', 'd', 'e', 'f', 'i', 'n', 'e', 'd']
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed len parameter and handled char_to_pos_spec */
proof fn char_to_pos_impl(c: char) -> (pos: int)
    ensures
        (c == 'v' && pos == 0) || (c == '>' && pos == 1) || (c == '^' && pos == 2) || (c == '<' && pos == 3),
        (c != 'v' && c != '>' && c != '^' && c != '<') ==> pos == 0
{
    if c == 'v' { 0 }
    else if c == '>' { 1 }
    else if c == '^' { 2 }
    else if c == '<' { 3 }
    else { 0 }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures valid_output(result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed type issues with `nat` and `int` for `len()` and  `index()` */
{
    let input_seq = input@;
    if input_seq.len() == 1 {
        let first_char = input_seq.index(0 as nat);
        let pos = char_to_pos_impl(first_char);
        if pos == 0 {
            "cw".to_string()
        } else {
            "ccw".to_string()
        }
    } else {
        "undefined".to_string()
    }
}
// </vc-code>


}

fn main() {}