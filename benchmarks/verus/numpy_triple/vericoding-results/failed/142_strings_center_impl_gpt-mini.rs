// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide spec function to get String view length */
spec fn str_len(s: String) -> nat { s@.len() }
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
    /* code modified by LLM (iteration 5): avoid calling String::len(); use spec-view lengths and track s_len manually */
    let mut result: Vec<String> = Vec::new();
    let n: usize = a.len();
    let mut i: usize = 0;
    while i < n
        invariant i <= n && result.len() == i
        decreases n - i
    {
        let orig = a[i].clone();
        let orig_len: usize = a[i]@.len() as usize;
        let target: usize = width[i];
        if orig_len >= target {
            result.push(orig);
        } else {
            let total: usize = target - orig_len;
            let left: usize = total / 2;
            let right: usize = total - left;
            let mut s = String::new();
            let mut s_len: usize = 0;

            let mut j: usize = 0;
            while j < left
                invariant j <= left && s_len == j
                decreases left - j
            {
                s.push(fillchar);
                s_len += 1;
                j += 1;
            }

            s.push_str(&orig);
            s_len += orig_len;

            let mut k: usize = 0;
            while k < right
                invariant k <= right && s_len == left + orig_len + k
                decreases right - k
            {
                s.push(fillchar);
                s_len += 1;
                k += 1;
            }

            result.push(s);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}