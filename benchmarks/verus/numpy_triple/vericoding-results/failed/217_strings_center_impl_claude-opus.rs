// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): Fixed String length access to use @ notation */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == width.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j]@.len() >= 0,
            forall|j: int| 0 <= j < i ==> {
                let orig_len = a[j]@.len() as int;
                let target_width = width[j] as int;
                &&& (orig_len >= target_width ==> result[j] == a[j])
                &&& result[j]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
            },
    {
        let s = &a[i];
        let w = width[i];
        let s_len = s@.len();
        
        if s_len >= w {
            result.push(s.clone());
        } else {
            let total_padding = w - s_len;
            let left_padding = total_padding / 2;
            let right_padding = total_padding - left_padding;
            
            let mut padded = String::new();
            let mut j = 0;
            while j < left_padding
                invariant
                    j <= left_padding,
                    padded@.len() == j,
            {
                padded.push(fillchar);
                j = j + 1;
            }
            
            let mut j = 0;
            while j < s@.len()
                invariant
                    j <= s@.len(),
                    padded@.len() == left_padding + j,
            {
                padded.push(s@[j]);
                j = j + 1;
            }
            
            let mut j = 0;
            while j < right_padding
                invariant
                    j <= right_padding,
                    padded@.len() == left_padding + s_len + j,
            {
                padded.push(fillchar);
                j = j + 1;
            }
            
            assert(padded@.len() == left_padding + s_len + right_padding);
            assert(padded@.len() == w);
            result.push(padded);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}