// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): produce a string of n repeated chars */
fn repeat_char(n: usize, c: char) -> (result: String)
    ensures
        result@.len() == n,
{
    let mut result = String::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == i,
        decreases n - i
    {
        result.push(c);
        i += 1;
    }
    result
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
/* code modified by LLM (iteration 5): implement centering using repeat_char */
    let mut result: Vec<String> = Vec::new();
    let len = a.len();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
        decreases len - i
    {
        let orig = a[i].clone();
        let orig_len = orig.len();
        let target = width[i];
        if orig_len >= target {
            result.push(orig);
        } else {
            let total = target - orig_len;
            let left = total / 2;
            let right = total - left;
            let left_pad = repeat_char(left, fillchar);
            let right_pad = repeat_char(right, fillchar);
            let mut s = left_pad;
            s.push_str(&orig);
            s.push_str(&right_pad);
            result.push(s);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}