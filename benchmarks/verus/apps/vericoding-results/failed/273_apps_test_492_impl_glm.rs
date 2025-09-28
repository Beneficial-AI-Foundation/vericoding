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
/* helper modified by LLM (iteration 3): changed return type from int to i32 and removed as int casts */
fn char_to_pos(c: char) -> i32 {
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
{
    /* code modified by LLM (iteration 5): fixed input.len() compilation error by using iterator to check length */
    let mut chars = input.chars();
    let first_char = chars.next().unwrap();
    if chars.next().is_none() {
        let pos = char_to_pos(first_char);
        if pos == 0 {
            "cw".to_string()
        } else if pos == 1 {
            "ccw".to_string()
        } else {
            "undefined".to_string()
        }
    } else {
        "undefined".to_string()
    }
}
// </vc-code>


}

fn main() {}