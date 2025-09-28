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
/* helper modified by LLM (iteration 4): fix type mismatches and add proper conversions */
spec fn char_to_pos_index(c: char) -> int {
    if c == 'v' { 0 }
    else if c == '>' { 1 }
    else if c == '^' { 2 }
    else if c == '<' { 3 }
    else { -1 }
}

proof fn rotate_left_spec_proof(pos: int, steps: int) -> (result: int)
    requires 0 <= pos < 4
    ensures 0 <= result < 4
    decreases steps
{
    if steps <= 0 {
        pos
    } else {
        let next_pos = (pos + 3) % 4;
        rotate_left_spec_proof(next_pos, steps - 1)
    }
}

fn rotate_left_exec(pos: int, steps: int) -> (result: int)
    requires 0 <= pos < 4 && 0 <= steps < 4
    ensures 0 <= result < 4
{
    let mut current = pos;
    let mut remaining = steps;
    while remaining > 0
        invariant
            0 <= current < 4,
            0 <= remaining <= steps,
        decreases remaining
    {
        current = (current + 3) % 4;
        remaining = remaining - 1;
    }
    current
}
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures valid_output(result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fix type mismatches and use int parameters */
{
    let chars: Vec<char> = input.chars().collect();
    
    if chars.len() == 1 {
        let c = chars[0];
        let pos_val = char_to_pos_index(c);
        if pos_val >= 0 && pos_val < 4 {
            String::from("cw")
        } else {
            String::from("undefined")
        }
    } else {
        if chars.len() < 2 {
            String::from("undefined")
        } else {
            let first_char = chars[0];
            let pos_val = char_to_pos_index(first_char);
            
            if pos_val != 0 {
                String::from("undefined")
            } else {
                let second_char = chars[1];
                let steps_val = char_to_pos_index(second_char);
                
                if steps_val >= 0 && steps_val < 4 {
                    proof {
                        let new_pos_spec = rotate_left_spec_proof(pos_val, steps_val);
                    }
                    let new_pos_exec = rotate_left_exec(pos_val, steps_val);
                    if new_pos_exec == 3 {
                        String::from("ccw")
                    } else {
                        String::from("undefined")
                    }
                } else {
                    String::from("undefined")
                }
            }
        }
    }
}
// </vc-code>


}

fn main() {}