// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix type compatibility between nat and usize */
fn center_string(s: String, w: usize, fillchar: char) -> (result: String)
    requires
        true,
    ensures
        result@.len() == if s@.len() >= w as nat { s@.len() } else { w as nat },
        s@.len() >= w as nat ==> result == s,
{
    if s@.len() >= w as nat {
        s
    } else {
        let padding = w - (s@.len() as usize);
        let left_padding = padding / 2;
        let right_padding = padding - left_padding;
        let mut result = String::new();
        let mut i = 0;
        while i < left_padding
            invariant
                i <= left_padding,
                result@.len() == i as nat,
            decreases left_padding - i
        {
            result.push(fillchar);
            i += 1;
        }
        result.push_str(&s);
        i = 0;
        while i < right_padding
            invariant
                i <= right_padding,
                result@.len() == (left_padding as nat) + s@.len() + (i as nat),
            decreases right_padding - i
        {
            result.push(fillchar);
            i += 1;
        }
        result
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
    /* code modified by LLM (iteration 5): fix type compatibility in main function */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_len = a[j]@.len() as int;
                let target_width = width[j] as int;
                &&& (orig_len >= target_width ==> result[j] == a[j])
                &&& result[j]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
            },
        decreases a.len() - i
    {
        let centered = center_string(a[i].clone(), width[i], fillchar);
        result.push(centered);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}