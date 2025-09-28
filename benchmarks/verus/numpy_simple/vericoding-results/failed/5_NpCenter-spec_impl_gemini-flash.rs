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
/* code modified by LLM (iteration 5): Fixed compilation error with `line.chars().nth(l).unwrap()` by using `line.as_str().chars().nth(l).unwrap()` instead, to ensure `&str` method call. */
{
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < input.len()
        invariant
            0 <= i as int <= input.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                if input[j].len() > width {
                    result[j].len() == input[j].len()
                } else {
                    result[j].len() == width
                },
            forall|j: int| 0 <= j < i ==> 
                if input[j].len() < width {
                    let start_pos = ((width - input[j].len() + 1) / 2) as int;
                    result[j].chars().skip(start_pos as usize).take(input[j].len()).collect::<String>() == input[j]
                } else {
                    true
                }
        decreases input.len() - i
    {
        let line: &String = &input[i];
        let line_len: usize = line.len();
        if line_len >= width {
            result.push(line.clone());
        } else {
            let padding_len = width - line_len;
            let left_padding_len = padding_len / 2;
            let right_padding_len = padding_len - left_padding_len;

            let mut centered_line_string = String::new();
            let mut k = 0;
            while k < left_padding_len
                invariant
                    0 <= k <= left_padding_len,
                    centered_line_string.len() == k
                decreases left_padding_len - k
            {
                centered_line_string.push(' ');
                k += 1;
            }
            let mut l = 0;
            while l < line_len
                invariant
                    left_padding_len <= centered_line_string.len(),
                    centered_line_string.len() == left_padding_len + l,
                    0 <= l <= line_len
                decreases line_len - l
            {
                centered_line_string.push(line.as_str().chars().nth(l).unwrap());
                l += 1;
            }
            let mut m = 0;
            while m < right_padding_len
                invariant
                    (left_padding_len + line_len) <= centered_line_string.len(),
                    centered_line_string.len() == left_padding_len + line_len + m,
                    0 <= m <= right_padding_len
                decreases right_padding_len - m
            {
                centered_line_string.push(' ');
                m += 1;
            }
            result.push(centered_line_string);
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}