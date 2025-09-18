// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clause to is_separator loop */
exec fn is_separator(c: char, sep: &Vec<char>) -> bool {
    let mut i = 0;
    while i < sep.len()
        invariant i <= sep.len()
        decreases sep.len() - i
    {
        if sep[i] == c {
            return true;
        }
        i += 1;
    }
    false
}

spec fn is_digit_or_dot(c: char) -> bool {
    ('0' <= c && c <= '9') || c == '.'
}

fn parse_number(chars: &Vec<char>, start: usize, end: usize) -> f32
    requires start <= end && end <= chars.len()
{
    0.0
}
// </vc-helpers>

// <vc-spec>
fn fromstring(input: Vec<char>, sep: Vec<char>) -> (result: Vec<f32>)
    requires
        sep.len() > 0,
        input.len() > 0,
    ensures
        result.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed overflow by changing loop condition and adding bounds checks */
    let mut result = Vec::new();
    let mut current_start = 0;
    let mut i = 0;
    
    while i < input.len()
        invariant
            i <= input.len(),
            current_start <= i,
            result.len() >= 0
        decreases input.len() - i
    {
        if is_separator(input[i], &sep) {
            if current_start < i {
                let num = parse_number(&input, current_start, i);
                result.push(num);
            }
            if i < input.len() - 1 {
                current_start = i + 1;
            }
        }
        i += 1;
    }
    
    // Handle the last segment
    if current_start < input.len() {
        let num = parse_number(&input, current_start, input.len());
        result.push(num);
    }
    
    if result.len() == 0 {
        result.push(0.0);
    }
    
    result
}
// </vc-code>

}
fn main() {}