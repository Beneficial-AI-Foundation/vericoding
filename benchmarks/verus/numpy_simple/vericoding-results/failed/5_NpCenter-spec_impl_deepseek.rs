// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax and types */
fn get_left_padding(line_len: usize, width: usize) -> (result: usize)
    requires
        line_len <= width,
        width >= 1,
    ensures
        result <= width - line_len,
        result <= width,
{
    (width - line_len) / 2
}

fn get_right_padding(line_len: usize, width: usize) -> (result: usize)
    requires
        line_len <= width,
        width >= 1,
    ensures
        result + line_len <= width,
        result <= width,
{
    width - line_len - get_left_padding(line_len, width)
}

fn build_centered_string(line: String, width: usize) -> (result: String)
    requires
        line@.len() >= 1,
        line@.len() <= width,
        width >= 1,
    ensures
        result@.len() == width,
        let left_pad = get_left_padding(line@.len(), width);
        let start_pos = left_pad as int;
        result@.skip(start_pos).take(line@.len() as int) == line@,
{
    let left_pad = get_left_padding(line@.len(), width);
    let right_pad = get_right_padding(line@.len(), width);
    
    let mut spaces_left = String::new();
    let mut i: usize = 0;
    while i < left_pad
        invariant
            i <= left_pad,
            spaces_left@.len() == i,
        decreases left_pad - i
    {
        spaces_left.push(' ');
        i = i + 1;
    }
    
    let mut spaces_right = String::new();
    let mut j: usize = 0;
    while j < right_pad
        invariant
            j <= right_pad,
            spaces_right@.len() == j,
        decreases right_pad - j
    {
        spaces_right.push(' ');
        j = j + 1;
    }
    
    let mut result = spaces_left;
    result.push_str(line.as_str());
    result.push_str(spaces_right.as_str());
    result
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
    /* code modified by LLM (iteration 5): fixed variable declaration placement */
    let mut result: Vec<String> = Vec::with_capacity(input.len());
    let mut index: usize = 0;
    
    while index < input.len()
        invariant
            result.len() == index,
            forall|i: int| 0 <= i < input.len() ==> input[i]@.len() >= 1,
            forall|i: int| 0 <= i < index ==> 
                if input[i]@.len() > width {
                    result[i]@.len() == input[i]@.len()
                } else {
                    result[i]@.len() == width
                },
            forall|i: int| 0 <= i < index ==> 
                if input[i]@.len() < width {
                    let start_pos = ((width - input[i]@.len() + 1) / 2) as int;
                    result[i]@.skip(start_pos).take(input[i]@.len() as int) == input[i]@
                } else {
                    true
                },
        decreases input.len() - index
    {
        let current_line = &input[index];
        
        if current_line@.len() > width {
            result.push(current_line.clone());
        } else {
            let centered = build_centered_string(current_line.clone(), width);
            result.push(centered);
        }
        
        index = index + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}