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

// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires valid_input(input@)
    ensures valid_output(result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type error by using usize for indexing */
    let chars = input@;
    
    if chars.len() == 0 {
        return "undefined".to_string();
    }
    
    let mut pos = 0;
    let mut i: usize = 0;
    
    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            0 <= pos <= 3
    {
        let c = chars[i as int];
        let prev_pos = pos;
        
        if c == 'v' {
            pos = 0;
        } else if c == '>' {
            pos = 1;
        } else if c == '^' {
            pos = 2;
        } else if c == '<' {
            pos = 3;
        }
        
        if i > 0 {
            let diff = (pos - prev_pos + 4) % 4;
            if diff == 1 {
                return "cw".to_string();
            } else if diff == 3 {
                return "ccw".to_string();
            } else if diff != 0 {
                return "undefined".to_string();
            }
        }
        
        i = i + 1;
    }
    
    "undefined".to_string()
}
// </vc-code>


}

fn main() {}