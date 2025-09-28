// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed return value naming in ensures block */
fn calculate_padding(orig_len: usize, target_width: usize) -> (result: (usize, usize))
    requires
        orig_len <= target_width,
    ensures
        result.0 + orig_len + result.1 == target_width,
        result.0 <= result.1 || result.0 == result.1 + 1,
{
    if orig_len == target_width {
        (0, 0)
    } else {
        let total_padding = target_width - orig_len;
        let left = total_padding / 2;
        let right = total_padding - left;
        (left, right)
    }
}
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
{
    /* code modified by LLM (iteration 5): no changes, fixed helper function only */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result[j]@.len() >= 0 && 
                (a[j]@.len() as int >= width[j] as int ==> result[j] == a[j]) &&
                result[j]@.len() as int == (if a[j]@.len() as int >= width[j] as int { a[j]@.len() as int } else { width[j] as int })
        decreases a.len() - i
    {
        let orig_str = a[i].clone();
        let orig_len = orig_str.len();
        let target_width = width[i];

        if orig_len >= target_width {
            result.push(orig_str);
        } else {
            let (left_pad, right_pad) = calculate_padding(orig_len, target_width);
            let mut centered_str = String::new();
            
            // Add left padding
            let mut j = 0;
            while j < left_pad
                invariant
                    0 <= j <= left_pad,
                    centered_str.len() == j,
                decreases left_pad - j
            {
                centered_str.push(fillchar);
                j += 1;
            }
            
            // Add original string
            centered_str.push_str(&orig_str);
            
            // Add right padding
            let mut j = 0;
            while j < right_pad
                invariant
                    0 <= j <= right_pad,
                    centered_str.len() == left_pad + orig_len + j,
                decreases right_pad - j
            {
                centered_str.push(fillchar);
                j += 1;
            }
            
            result.push(centered_str);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}