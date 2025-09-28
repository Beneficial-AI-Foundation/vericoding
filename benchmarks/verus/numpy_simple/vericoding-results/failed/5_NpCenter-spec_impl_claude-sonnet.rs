// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): converted usize to nat for consistency with Verus spec requirements */
fn pad_string(s: String, target_width: usize) -> (result: String)
    requires
        s@.len() >= 1,
    ensures
        if s@.len() > target_width as nat {
            result@ == s@
        } else {
            result@.len() == target_width as nat &&
            {
                let start_pos = (target_width as nat - s@.len() + 1) / 2;
                result@.skip(start_pos as int).take(s@.len() as int) == s@
            }
        },
{
    if s@.len() > target_width as nat {
        s
    } else {
        let padding_needed = target_width as nat - s@.len();
        let left_padding = (padding_needed + 1) / 2;
        let right_padding = padding_needed - left_padding;
        
        let mut result = String::new();
        
        let mut i = 0nat;
        while i < left_padding
            invariant
                0 <= i <= left_padding,
                result@.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == ' '
        {
            result.push(' ');
            i += 1;
        }
        
        result.push_str(&s);
        
        let mut j = 0nat;
        while j < right_padding
            invariant
                0 <= j <= right_padding,
                result@.len() == left_padding + s@.len() + j,
                forall|k: int| 0 <= k < left_padding ==> result@[k] == ' ',
                result@.skip(left_padding as int).take(s@.len() as int) == s@,
                forall|k: int| left_padding + s@.len() <= k < left_padding + s@.len() + j ==> result@[k] == ' '
        {
            result.push(' ');
            j += 1;
        }
        
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn center(input: Vec<String>, width: usize) -> (result: Vec<String>)
    requires 
        input.len() > 0,
        forall|i: int| 0 <= i < input.len() ==> input[i]@.len() >= 1,
    ensures
        result.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> 
            if input[i]@.len() > width {
                result[i]@.len() == input[i]@.len()
            } else {
                result[i]@.len() == width
            },
        forall|i: int| 0 <= i < input.len() ==> 
            if input[i]@.len() < width {
                let start_pos = (width - input[i]@.len() + 1) / 2;
                result[i]@.skip(start_pos as int).take(input[i]@.len() as int) == input[i]@
            } else {
                true
            }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type conversion for width parameter */
    let mut result: Vec<String> = Vec::new();
    
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                if input[j]@.len() > width as nat {
                    result[j]@.len() == input[j]@.len()
                } else {
                    result[j]@.len() == width as nat
                },
            forall|j: int| 0 <= j < i ==> 
                if input[j]@.len() < width as nat {
                    let start_pos = (width as nat - input[j]@.len() + 1) / 2;
                    result[j]@.skip(start_pos as int).take(input[j]@.len() as int) == input[j]@
                } else {
                    true
                }
    {
        let padded = pad_string(input[i].clone(), width);
        result.push(padded);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}