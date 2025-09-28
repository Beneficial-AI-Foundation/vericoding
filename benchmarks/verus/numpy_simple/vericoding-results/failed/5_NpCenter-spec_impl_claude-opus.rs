// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Convert width to nat for comparisons with string length */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                if input[j]@.len() > width {
                    result[j]@.len() == input[j]@.len()
                } else {
                    result[j]@.len() == width
                },
            forall|j: int| 0 <= j < i ==> 
                if input[j]@.len() < width {
                    let start_pos = (width - input[j]@.len() + 1) / 2;
                    result[j]@.skip(start_pos as int).take(input[j]@.len() as int) == input[j]@
                } else {
                    true
                },
    {
        let s = &input[i];
        let len = s@.len();
        let width_nat = width as nat;
        
        if len > width_nat {
            result.push(s.clone());
        } else if len == width_nat {
            result.push(s.clone());
        } else {
            let padding = width_nat - len;
            let left_pad = (padding + 1) / 2;
            let right_pad = padding - left_pad;
            
            let mut centered = String::new();
            let mut j: nat = 0;
            while j < left_pad
                invariant
                    0 <= j <= left_pad,
                    centered@.len() == j,
                    forall|k: int| 0 <= k < j ==> centered@[k] == ' ' as u8,
            {
                centered.push(' ');
                j = j + 1;
            }
            
            centered.push_str(s);
            
            j = 0;
            while j < right_pad
                invariant
                    0 <= j <= right_pad,
                    centered@.len() == left_pad + len + j,
                    centered@.skip(left_pad as int).take(len as int) == s@,
                    forall|k: int| 0 <= k < left_pad ==> centered@[k] == ' ' as u8,
                    forall|k: int| left_pad + len <= k < left_pad + len + j ==> centered@[k] == ' ' as u8,
            {
                centered.push(' ');
                j = j + 1;
            }
            
            assert(centered@.len() == width_nat);
            assert(centered@.skip(left_pad as int).take(len as int) == s@);
            result.push(centered);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}