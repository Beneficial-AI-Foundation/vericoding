// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): using vstd new_strlit instead of String::new */
fn repeat_char(c: char, n: usize) -> (result: String)
    ensures result@.len() == n as int
{
    let mut s = new_strlit("").to_string();
    let mut i = 0;
    while i < n
        invariant s@.len() == i as int
    {
        s.push(c);
        i += 1;
    }
    s
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
    /* code modified by LLM (iteration 5): using vstd new_strlit instead of String::new */
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
            }
    {
        let orig_len = a[i].len();
        let target_width = width[i];
        
        if orig_len >= target_width {
            result.push(a[i].clone());
        } else {
            let padding = target_width - orig_len;
            let left_padding = padding / 2;
            let right_padding = padding - left_padding;
            
            let left_fill = repeat_char(fillchar, left_padding);
            let right_fill = repeat_char(fillchar, right_padding);
            
            let mut centered = new_strlit("").to_string();
            centered.push_str(&left_fill);
            centered.push_str(&a[i]);
            centered.push_str(&right_fill);
            
            result.push(centered);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}