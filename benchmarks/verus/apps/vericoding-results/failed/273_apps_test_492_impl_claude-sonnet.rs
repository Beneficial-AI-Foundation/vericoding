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
/* helper modified by LLM (iteration 5): fixed nat comparison and index literal */
fn char_to_pos(c: char) -> (result: usize)
    requires
        c == 'v' || c == '>' || c == '^' || c == '<',
    ensures
        (c == 'v' ==> result == 0) &&
        (c == '>' ==> result == 1) &&
        (c == '^' ==> result == 2) &&
        (c == '<' ==> result == 3),
{
    if c == 'v' { 0 }
    else if c == '>' { 1 }
    else if c == '^' { 2 }
    else { 3 }
}

fn get_direction(input: &str) -> (result: Option<char>)
    requires
        input@.len() > 0,
    ensures
        result.is_some() ==> (result.unwrap() == 'v' || result.unwrap() == '>' || result.unwrap() == '^' || result.unwrap() == '<'),
{
    if input@.len() > 0nat {
        let c = input@.index(0);
        if c == 'v' || c == '>' || c == '^' || c == '<' {
            Some(c)
        } else {
            None
        }
    } else {
        None
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures valid_output(result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using string indexing */
    let direction_opt = get_direction(input);
    match direction_opt {
        Some(dir) => {
            let pos = char_to_pos(dir);
            if pos % 2 == 0 {
                "cw".to_string()
            } else {
                "ccw".to_string()
            }
        },
        None => {
            "undefined".to_string()
        }
    }
}
// </vc-code>


}

fn main() {}