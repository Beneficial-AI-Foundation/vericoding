// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [fixed unsupported String::push using char_to_string and push_str] */
fn repeat_char(c: char, n: usize) -> (res: String)
    ensures
        res@.len() == n,
        forall|i: int| 0 <= i < n ==> res@[i] == c,
{
    let mut res = String::from_str("");
    let mut i: usize = 0;
    let char_str = char_to_string(c);
    while i < n
        invariant
            i <= n,
            res@.len() == i,
            forall|j: int| 0 <= j < i ==> res@[j] == c,
        decreases n - i
    {
        res.push_str(&char_str);
        i = i + 1;
    }
    res
}

/* helper modified by LLM (iteration 3): [worked around verus internal error by using push_str] */
fn center_string(s: &String, width: usize) -> (result: String)
    requires
        s@.len() >= 1,
    ensures
        if s@.len() >= width {
            result@ == s@
        } else {
            result@.len() == width
            && {
                let start_pos = (width - s@.len() + 1) / 2;
                result@.skip(start_pos as int).take(s@.len() as int) == s@
            }
        }
{
    let s_len = s.len();
    if s_len >= width {
        return s.clone();
    }

    let total_padding = width - s_len;
    let left_padding = (total_padding + 1) / 2;
    let right_padding = total_padding - left_padding;

    let left_str = repeat_char(' ', left_padding);
    let right_str = repeat_char(' ', right_padding);
    
    let mut res = left_str;
    res.push_str(s);
    res.push_str(&right_str);
    res
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
    /* code modified by LLM (iteration 5): [no changes needed, fix was in helper function] */
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            i <= input.len(),
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
        decreases input.len() - i
    {
        let s = &input[i];
        let centered_s = center_string(s, width);
        result.push(centered_s);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}