// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn calculate_start_pos(input_len: usize, width: usize) -> (result: usize)
    requires
        input_len > 0,
        input_len <= width,
    ensures
        result == (width - input_len + 1) / 2
{
    (width - input_len + 1) / 2
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
    /* code modified by LLM (iteration 3): fixed compilation error by converting ghost nat to usize for exec condition */
    let mut result: Vec<String> = Vec::new();
    
    for i in 0..input.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                if input[j]@.len() > (width as nat) {
                    result[j]@.len() == input[j]@.len()
                } else {
                    result[j]@.len() == width
                },
            forall|j: int| 0 <= j < i ==> 
                if input[j]@.len() < (width as nat) {
                    let start_pos = (width - (input[j]@.len() as usize) + 1) / 2;
                    result[j]@.skip(start_pos as int).take(input[j]@.len() as int) == input[j]@
                } else {
                    true
                }
    {
        let input_str = &input[i];
        let input_len = input_str@.len();
        let input_len_usize = input_len as usize;
        
        if input_len_usize > width {
            result.push(input_str.clone());
        } else {
            let start_pos = calculate_start_pos(input_len_usize, width);
            let spaces_before = " ".repeat(start_pos);
            let spaces_after = " ".repeat(width - start_pos - input_len_usize);
            let centered = format!("{}{}{}", spaces_before, input_str, spaces_after);
            result.push(centered);
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}