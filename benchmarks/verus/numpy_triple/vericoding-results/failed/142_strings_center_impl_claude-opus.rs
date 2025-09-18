// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

/* helper modified by LLM (iteration 5): Fixed type error by using usize comparison instead of nat */
fn center_string(s: &String, width: usize, fillchar: char) -> (result: String)
    ensures
        result@.len() == max(s@.len(), width as nat),
        s@.len() >= width as nat ==> result == *s
{
    if s.len() >= width {
        s.clone()
    } else {
        let total_padding = width - s.len();
        let left_padding = total_padding / 2;
        let right_padding = total_padding - left_padding;
        
        let mut result = String::with_capacity(width);
        let mut i: usize = 0;
        while i < left_padding
            invariant
                i <= left_padding,
                result@.len() == i as nat,
                result.capacity() >= width
        {
            result.push(fillchar);
            i += 1;
        }
        
        result.push_str(s);
        
        i = 0;
        while i < right_padding
            invariant
                i <= right_padding,
                result@.len() == (left_padding as nat) + s@.len() + (i as nat),
                result.capacity() >= width
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
    /* code modified by LLM (iteration 5): No changes needed in main code */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == width.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==>
                #[trigger] result[j]@.len() >= 0 && {
                    let orig_len = a[j]@.len() as int;
                    let target_width = width[j] as int;
                    &&& (orig_len >= target_width ==> result[j] == a[j])
                    &&& result[j]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
                }
    {
        let centered = center_string(&a[i], width[i], fillchar);
        result.push(centered);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}