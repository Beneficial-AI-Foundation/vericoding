// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add spec function for string length for use in ensures clause. */
spec fn string_len(s: String) -> nat { s@.len() }
// </vc-helpers>

// <vc-spec>
fn center(a: Vec<String>, width: Vec<usize>, fillchar: char) -> (result: Vec<String>)
    requires 
        a.len() == width.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i]@.len() >= 0 && {
                let orig_len = a[i]@.len() as int;
                let target_width = width[i] as int;
                &&& (orig_len >= target_width ==> result[i] == a[i])
                &&& result[i]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
            }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced direct s.len() with string_len(s) for verification. */ {
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            result.len() == i,
            result.len() <= a.len(),
            forall|j: int| 0 <= j < result.len() ==> {
                let orig_len = string_len(a[j]) as int;
                let target_width = width[j] as int;
                &&& string_len(result[j]) >= 0
                &&& (orig_len >= target_width ==> result[j] == a[j])
                &&& string_len(result[j]) as int == if orig_len >= target_width { orig_len } else { target_width }
            }
    {
        let s = a[i].clone();

        if string_len(s) >= width[i] as nat {
            result.push(s);
        } else {
            let diff: usize = width[i] - string_len(s) as usize;
            let left_padding_len: usize = diff / 2;
            let right_padding_len: usize = diff - left_padding_len;

            let fill_char_val = fillchar.clone();

            let mut padded_string = String::new();
            let mut k: usize = 0;
            while k < left_padding_len
                invariant
                    k <= left_padding_len
            {
                padded_string.push(fill_char_val);
                k = k + 1;
            }
            
            padded_string.push_str(s.as_str());

            let mut k: usize = 0;
            while k < right_padding_len
                invariant
                    k <= right_padding_len
            {
                padded_string.push(fill_char_val);
                k = k + 1;
            }
            result.push(padded_string);
        }

        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}